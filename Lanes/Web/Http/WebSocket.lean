/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Sha1
public import Lanes.Lib.Encoding.Base64
public import Lanes.Lib.Encoding.Digits
public import Lanes.Web.Http.Basic

/-!
WebSockets (RFC 6455) as data: the opening handshake read from a request and answered, frames
encoded and decoded, and a connection's side of the protocol, all pure.

`decode` reads one frame from the front of the bytes received, or says it needs more, or names
the close code to fail the connection with: an unknown opcode, a frame masked when it must not be
or not when it must, a payload over the limit, a reserved bit set (no extension is offered), or a
control frame fragmented or over 125 bytes; it checks them in websockets' order. It reads back every frame `encode` writes, with
whatever follows (`WebSocket.decode_encode`, in `Lanes/Web/Http/WebSocketSound.lean`).

`Conn` is the server's side of a connection: it takes the bytes received and returns the
messages they complete and what to send back. A client's frames must be masked; fragments are
put together, up to a message's limit, with control frames between them; text must be UTF-8;
a ping is answered by a pong, and a close by the same close, after which the connection ends.
-/

@[expose] public section

namespace Lanes.WebSocket

/-! ### The opening handshake (§4.2) -/

def guid : String := "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- `Sec-WebSocket-Accept` for a client's `Sec-WebSocket-Key`. -/
def acceptKey (key : String) : String :=
  Base64.encode .std (Sha1.hash (key ++ guid).toUTF8)

inductive Refusal where
  | notGet
  | notUpgrade
  | badVersion
  | badKey
  deriving DecidableEq, Repr

/-- The comma-separated tokens of a header, in lowercase. -/
def tokens (value : String) : List String :=
  (value.splitOn ",").map fun t => t.trimAscii.toString.toLower

def hasToken (r : Http.Request) (name token : String) : Bool :=
  r.headers.any fun (n, v) => n == name && (tokens v).contains token

/-- The client's key, if the request asks to open a WebSocket as RFC 6455 says. -/
def check (r : Http.Request) : Except Refusal String := do
  unless r.method == .get do throw .notGet
  unless hasToken r "upgrade" "websocket" && hasToken r "connection" "upgrade" do throw .notUpgrade
  unless (r.header? "sec-websocket-version").map (·.trimAscii.toString) == some "13" do
    throw .badVersion
  match r.header? "sec-websocket-key" with
  | some key =>
    let key := key.trimAscii.toString
    if ((Base64.decode .std key).map (·.size)) == some 16 then return key else throw .badKey
  | none => throw .badKey

/-- The subprotocols the client offers, in its order of preference. -/
def protocols (r : Http.Request) : List String :=
  r.headers.flatMap fun (n, v) =>
    if n == "sec-websocket-protocol" then (v.splitOn ",").map (·.trimAscii.toString) else []

/-- `101 Switching Protocols` for a client's key, with the subprotocol chosen, if any. -/
def switching (key : String) (protocol : Option String := none) : Http.Response where
  status := 101
  headers := [("upgrade", "websocket"), ("connection", "Upgrade"),
    ("sec-websocket-accept", acceptKey key)]
    ++ (protocol.map fun p => [("sec-websocket-protocol", p)]).getD []

/-- The answer to a request refused: `426` with the version spoken, or `400`. -/
def Refusal.response : Refusal → Http.Response
  | .badVersion => { status := 426, headers := [("sec-websocket-version", "13")] }
  | _ => { status := 400 }

/-! ### Frames (§5) -/

inductive Opcode where
  | continuation | text | binary | close | ping | pong
  deriving DecidableEq, Repr, Inhabited

def Opcode.code : Opcode → Nat
  | .continuation => 0 | .text => 1 | .binary => 2 | .close => 8 | .ping => 9 | .pong => 10

def Opcode.ofCode? : Nat → Option Opcode
  | 0 => some .continuation | 1 => some .text | 2 => some .binary
  | 8 => some .close | 9 => some .ping | 10 => some .pong
  | _ => none

def Opcode.control (o : Opcode) : Bool := o.code ≥ 8

structure Frame where
  fin : Bool := true
  opcode : Opcode
  /-- The key a client masks its frames with; a server's are not masked. -/
  mask : Option (Vector UInt8 4) := none
  /-- Unmasked. -/
  payload : ByteArray
  deriving Repr

structure Limits where
  /-- The payload of one frame. -/
  maxPayload : Nat := 1 <<< 20
  /-- A message, all its fragments together. -/
  maxMessage : Nat := 1 <<< 24

/-- The close codes a connection is failed with. -/
def protocolError : Nat := 1002
def invalidData : Nat := 1007
def tooBig : Nat := 1009

/-- XOR with the key, the `i`th byte with the key's `i % 4`th; it undoes itself. -/
def applyMask (key : Vector UInt8 4) (b : ByteArray) : ByteArray :=
  ⟨b.data.mapIdx fun i x => x ^^^ key[i % 4]'(Nat.mod_lt _ (by decide))⟩

/-- The length as written: in the second byte, or after it in two or eight bytes. -/
def lengthBytes (n : Nat) : Nat × List UInt8 :=
  if n ≤ 125 then (n, [])
  else if n < 65536 then (126, (Digits.split 256 2 n).map (·.toUInt8))
  else (127, (Digits.split 256 8 n).map (·.toUInt8))

def header (f : Frame) : List UInt8 :=
  let (len7, ext) := lengthBytes f.payload.size
  ((if f.fin then 128 else 0) + f.opcode.code).toUInt8
    :: ((if f.mask.isSome then 128 else 0) + len7).toUInt8
    :: ext ++ (f.mask.map (·.toList)).getD []

def encode (f : Frame) : ByteArray :=
  ⟨(header f).toArray⟩ ++ (match f.mask with | some k => applyMask k f.payload | none => f.payload)

inductive Decoded where
  /-- More bytes are needed. -/
  | more
  /-- A frame, and how many bytes it took. -/
  | frame (f : Frame) (size : Nat)
  /-- The connection must be failed with this close code. -/
  | fail (code : Nat)
  deriving Repr

/-- The payload's length, after the header's first two bytes, and the bytes it took. A length
not written in the fewest bytes is read, as websockets and browsers read it. -/
def readLength (len7 : Nat) (rest : List UInt8) : Option (Nat × Nat) :=
  if len7 ≤ 125 then some (len7, 0)
  else
    let w := if len7 = 126 then 2 else 8
    if rest.length < w then none else some (Digits.join 256 ((rest.take w).map (·.toNat)), w)

structure Header where
  fin : Bool
  /-- The three reserved bits. -/
  rsv : Nat
  opcode : Opcode
  mask : Option (Vector UInt8 4)
  length : Nat
  /-- The header's own size in bytes. -/
  size : Nat

/-- A header read from the front of the bytes received, or the close code to fail with, or
`none` if more bytes are needed. `masked` is whether the frame must be masked, if that is
known, and `sofar` the bytes of a message already received in fragments: a data frame may hold
only what is left of the message's limit. A wrong opcode or mask fails at once, a payload over
the limit as soon as its length is read, as in websockets, so that it is never held. -/
def readHeader (l : Limits) (masked : Option Bool) (sofar : Nat) (h : List UInt8) :
    Option (Except Nat Header) :=
  match h with
  | b0 :: b1 :: rest =>
    match Opcode.ofCode? (b0.toNat % 16) with
    | none => some (.error protocolError)
    | some op =>
      if masked.any (· != decide (b1.toNat ≥ 128)) then some (.error protocolError)
      else
        match readLength (b1.toNat % 128) rest with
        | none => none
        | some (n, w) =>
          if n > (if op.control then l.maxPayload else min l.maxPayload (l.maxMessage - sofar)) then
            some (.error tooBig)
          else
            let hd (mask : Option (Vector UInt8 4)) (size : Nat) : Header :=
              { fin := decide (b0.toNat ≥ 128), rsv := (b0.toNat / 16) % 8, opcode := op, mask,
                length := n, size }
            if b1.toNat ≥ 128 then
              match rest.drop w with
              | k0 :: k1 :: k2 :: k3 :: _ => some (.ok (hd (some #v[k0, k1, k2, k3]) (2 + w + 4)))
              | _ => none
            else some (.ok (hd none (2 + w)))
  | _ => none

/-- One frame from the front of `bytes`. A reserved bit set, or a control frame fragmented or
over 125 bytes, fails once the frame is whole. -/
def decode (l : Limits) (bytes : ByteArray) (masked : Option Bool := none) (sofar : Nat := 0) :
    Decoded :=
  match readHeader l masked sofar (bytes.extract 0 14).data.toList with
  | none => .more
  | some (.error c) => .fail c
  | some (.ok h) =>
    if bytes.size < h.size + h.length then .more
    else if h.rsv ≠ 0 || (h.opcode.control && (!h.fin || h.length > 125)) then .fail protocolError
    else
      let body := bytes.extract h.size (h.size + h.length)
      let payload := match h.mask with | some k => applyMask k body | none => body
      .frame { fin := h.fin, opcode := h.opcode, mask := h.mask, payload } (h.size + h.length)

/-! ### A connection, the server's side (§5.4, §5.5, §7) -/

inductive Message where
  | text (s : String)
  | binary (b : ByteArray)
  deriving Repr

/-- A close code a peer may send (§7.4): not 1004, 1005, 1006 or 1015, nor one unassigned below 3000. -/
def validCode (c : Nat) : Bool :=
  (1000 ≤ c && c ≤ 1003) || (1007 ≤ c && c ≤ 1014) || (3000 ≤ c && c ≤ 4999)

def closePayload (code : Nat) (reason : String := "") : ByteArray :=
  ⟨#[(code / 256).toUInt8, (code % 256).toUInt8]⟩ ++ reason.toUTF8

/-- The code and reason of a close frame's payload, or the code to fail with. -/
def readClose (p : ByteArray) : Except Nat (Option (Nat × String)) :=
  if p.size = 0 then .ok none
  else if p.size = 1 then .error protocolError
  else
    let code := p[0]!.toNat * 256 + p[1]!.toNat
    match String.fromUTF8? (p.extract 2 p.size) with
    | none => .error invalidData
    | some reason => if validCode code then .ok (some (code, reason)) else .error protocolError

inductive Event where
  /-- A message received whole. -/
  | message (m : Message)
  /-- Bytes to write to the peer. -/
  | send (bytes : ByteArray)
  /-- The connection is over: close the socket. The code is the close code sent or received. -/
  | closed (code : Nat)
  deriving Repr

structure Conn where
  limits : Limits := {}
  /-- Bytes received and not yet a whole frame. -/
  buffer : ByteArray := .empty
  /-- A message received in fragments: whether it is text, and its bytes so far. -/
  fragments : Option (Bool × ByteArray) := none
  /-- A close was sent, and the peer's is awaited. -/
  closing : Bool := false
  over : Bool := false

namespace Conn

def frameBytes (op : Opcode) (payload : ByteArray) : ByteArray := encode { opcode := op, payload }

/-- The connection failed: a close frame with the code, then the end. -/
def fail (c : Conn) (code : Nat) : Conn × List Event :=
  ({ c with over := true, buffer := .empty },
    [.send (frameBytes .close (closePayload code)), .closed code])

def deliver (c : Conn) (isText : Bool) (bytes : ByteArray) : Conn × List Event :=
  if isText then
    match String.fromUTF8? bytes with
    | some s => (c, [.message (.text s)])
    | none => c.fail invalidData
  else (c, [.message (.binary bytes)])

/-- One frame received. -/
def frame (c : Conn) (f : Frame) : Conn × List Event :=
  match f.opcode with
    | .ping => (c, if c.closing then [] else [.send (frameBytes .pong f.payload)])
    | .pong => (c, [])
    | .close =>
      match readClose f.payload with
      | .error code => c.fail code
      | .ok what =>
        let code := (what.map (·.1)).getD 1005
        let reply := if c.closing then [] else [.send (frameBytes .close f.payload)]
        ({ c with over := true, buffer := .empty }, reply ++ [.closed code])
    | .continuation =>
      match c.fragments with
      | none => c.fail protocolError
      | some (isText, sofar) =>
        let bytes := sofar ++ f.payload
        if bytes.size > c.limits.maxMessage then c.fail tooBig
        else if f.fin then ({ c with fragments := none }).deliver isText bytes
        else ({ c with fragments := some (isText, bytes) }, [])
    | .text | .binary =>
      if c.fragments.isSome then c.fail protocolError
      else
        let isText := f.opcode == .text
        if f.fin then c.deliver isText f.payload
        else ({ c with fragments := some (isText, f.payload) }, [])

/-- Frames from the buffer while whole ones are there. Each round takes at least two bytes, so
the buffer's size is fuel enough. -/
def drain (c : Conn) : Nat → List Event → Conn × List Event
  | 0, out => (c, out)
  | fuel + 1, out =>
    if c.over then (c, out)
    else match decode c.limits c.buffer (some true) ((c.fragments.map (·.2.size)).getD 0) with
      | .more => (c, out)
      | .fail code =>
        let (c, evs) := c.fail code
        (c, out ++ evs)
      | .frame f size =>
        let (c, evs) := ({ c with buffer := c.buffer.extract size c.buffer.size }).frame f
        drain c fuel (out ++ evs)

/-- Bytes received from the peer: the messages they complete, and what to do. -/
def receive (c : Conn) (bytes : ByteArray) : Conn × List Event :=
  if c.over then (c, [])
  else
    let c := { c with buffer := c.buffer ++ bytes }
    c.drain (c.buffer.size + 1) []

/-- The bytes of a message sent to the peer, unfragmented and unmasked. -/
def send (m : Message) : ByteArray :=
  match m with
  | .text s => frameBytes .text s.toUTF8
  | .binary b => frameBytes .binary b

/-- Close from this side: the bytes to send; the connection ends when the peer's close comes. -/
def close (c : Conn) (code : Nat := 1000) (reason : String := "") : Conn × ByteArray :=
  ({ c with closing := true }, frameBytes .close (closePayload code reason))

end Conn

end Lanes.WebSocket
