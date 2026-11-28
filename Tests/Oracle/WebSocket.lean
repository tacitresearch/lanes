/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Lanes.Web.Http.WebSocket

/-!
`Lanes.WebSocket` against RFC 6455's examples, and a server's side of a connection against the
Sans-I/O protocol of Python's websockets library.
-/

namespace Tests.Oracle.WebSocket

open Lanes Lanes.WebSocket

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def bytes (xs : List Nat) : ByteArray := ⟨(xs.map (·.toUInt8)).toArray⟩

def frameOf : Decoded → Option Frame
  | .frame f _ => some f
  | _ => none

def failOf : Decoded → Option Nat
  | .fail c => some c
  | _ => none

def isMore : Decoded → Bool
  | .more => true
  | _ => false

def key : Vector UInt8 4 := #v[0x37, 0xfa, 0x21, 0x3d]

def masked (op : Opcode) (payload : ByteArray) (fin := true) : ByteArray :=
  encode { fin, opcode := op, mask := some key, payload }

def handshake : Http.Request where
  method := .get
  path := ["chat"]
  headers := [("host", "server.example.com"), ("upgrade", "websocket"), ("connection", "keep-alive, Upgrade"),
    ("sec-websocket-key", "dGhlIHNhbXBsZSBub25jZQ=="), ("sec-websocket-version", "13"),
    ("sec-websocket-protocol", "chat, superchat")]

def messagesOf (evs : List Event) : List String :=
  evs.filterMap fun
    | .message (.text s) => some s!"text:{s}"
    | .message (.binary b) => some s!"binary:{Bytes.hex b}"
    | _ => none

def sentOf (evs : List Event) : ByteArray :=
  evs.foldl (fun acc e => match e with | .send b => acc ++ b | _ => acc) .empty

def closedOf (evs : List Event) : Option Nat :=
  evs.findSome? fun | .closed c => some c | _ => none

def run (input : ByteArray) (l : Limits := {}) : List Event := (({ limits := l } : Conn).receive input).2

def tests : List (String × Bool) :=
  [ ("websocket: SHA-1 of FIPS 180-4's examples",
      Bytes.hex (Sha1.hash "abc".toUTF8) == "a9993e364706816aba3e25717850c26c9cd0d89d"
        && Bytes.hex (Sha1.hash "".toUTF8) == "da39a3ee5e6b4b0d3255bfef95601890afd80709"
        && Bytes.hex (Sha1.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8)
          == "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
        && Bytes.hex (Sha1.hash ⟨Array.replicate 1000000 0x61⟩) == "34aa973cd4c4daa4f61eeb2bdbad27316534016f"),
    ("websocket: RFC 6455 §1.3: the handshake's accept key, and the answer",
      acceptKey "dGhlIHNhbXBsZSBub25jZQ==" == "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
        && (match check handshake with
          | .ok k => (switching k (some "chat")).headers.contains ("sec-websocket-accept", "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=")
          | .error _ => false)
        && protocols handshake == ["chat", "superchat"]),
    ("websocket: a handshake refused: not GET, no upgrade, another version, a bad key",
      check { handshake with method := .post } == .error .notGet
        && check { handshake with headers := handshake.headers.filter (·.1 != "upgrade") } == .error .notUpgrade
        && check { handshake with headers := handshake.headers.map fun (n, v) =>
            if n == "sec-websocket-version" then (n, "8") else (n, v) } == .error .badVersion
        && check { handshake with headers := handshake.headers.map fun (n, v) =>
            if n == "sec-websocket-key" then (n, "c2hvcnQ=") else (n, v) } == .error .badKey
        && Refusal.badVersion.response.status == 426),
    ("websocket: RFC 6455 §5.7's frames, written and read",
      encode { opcode := .text, payload := "Hello".toUTF8 } == bytes [0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]
        && masked .text "Hello".toUTF8
          == bytes [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]
        && encode { fin := false, opcode := .text, payload := "Hel".toUTF8 } == bytes [0x01, 0x03, 0x48, 0x65, 0x6c]
        && encode { opcode := .continuation, payload := "lo".toUTF8 } == bytes [0x80, 0x02, 0x6c, 0x6f]
        && (encode { opcode := .binary, payload := ⟨Array.replicate 256 0⟩ }).extract 0 4
          == bytes [0x82, 0x7e, 0x01, 0x00]
        && (encode { opcode := .binary, payload := ⟨Array.replicate 65536 0⟩ }).extract 0 10
          == bytes [0x82, 0x7f, 0, 0, 0, 0, 0, 1, 0, 0]
        && ((frameOf (decode {} (bytes [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58]))).map
          (·.payload)) == some "Hello".toUTF8),
    ("websocket: decode waits for a whole frame",
      isMore (decode {} (bytes [0x81])) && isMore (decode {} (bytes [0x81, 0x85, 0x37]))
        && isMore (decode {} (bytes [0x82, 0x7e, 0x01])) && isMore (decode {} (bytes [0x81, 0x05, 0x48]))),
    ("websocket: decode fails on an unknown opcode, a mask where none is wanted, a payload over the limit, reserved bits, and a long or fragmented control frame",
      failOf (decode {} (bytes [0x83, 0x00])) == some 1002
        && failOf (decode {} (bytes [0x81, 0x00]) (some true)) == some 1002
        && failOf (decode {} (bytes [0x81, 0x80]) (some false)) == some 1002
        && failOf (decode { maxPayload := 4 } (bytes [0x82, 0x05])) == some 1009
        && failOf (decode {} (bytes [0x82, 0x7f, 0x80, 0, 0, 0, 0, 1, 0, 0])) == some 1009
        && failOf (decode { maxMessage := 10 } (bytes [0x80, 0x05]) (sofar := 6)) == some 1009
        && failOf (decode {} (bytes [0xc1, 0x00])) == some 1002
        && failOf (decode {} (bytes ([0x89, 0x7e, 0x00, 0x7e] ++ List.replicate 126 0))) == some 1002
        && failOf (decode {} (bytes [0x09, 0x00])) == some 1002),
    ("websocket: a length not in the fewest bytes is read, as browsers read it",
      ((frameOf (decode {} (bytes [0x82, 0x7e, 0x00, 0x02, 7, 8]))).map (·.payload)) == some (bytes [7, 8])),
    ("websocket: a connection puts fragments together, with a ping between them",
      let evs := run (masked .text "Hel".toUTF8 (fin := false) ++ masked .ping "p".toUTF8
        ++ masked .continuation "lo".toUTF8)
      messagesOf evs == ["text:Hello"] && sentOf evs == encode { opcode := .pong, payload := "p".toUTF8 }),
    ("websocket: a connection answers a close with the same close and ends",
      let evs := run (masked .close (closePayload 1000 "bye") ++ masked .text "late".toUTF8)
      messagesOf evs == [] && sentOf evs == encode { opcode := .close, payload := closePayload 1000 "bye" }
        && closedOf evs == some 1000),
    ("websocket: a connection fails on an unmasked frame, text not UTF-8, a lone continuation, a message over its limit, a bad close code",
      closedOf (run (encode { opcode := .text, payload := "x".toUTF8 })) == some 1002
        && closedOf (run (masked .text ⟨#[0xff]⟩)) == some 1007
        && closedOf (run (masked .continuation "x".toUTF8)) == some 1002
        && closedOf (run (masked .binary ⟨Array.replicate 3 0⟩ (fin := false) ++ masked .continuation ⟨Array.replicate 3 0⟩)
          { maxMessage := 5 }) == some 1009
        && closedOf (run (masked .close (closePayload 1005))) == some 1002
        && closedOf (run (masked .close ⟨#[0x03]⟩)) == some 1002),
    ("websocket: bytes received in pieces give the same messages",
      let input := masked .text "Hello".toUTF8 ++ masked .binary ⟨#[1, 2, 3]⟩ ++ masked .ping .empty
      let whole := run input
      let (c, a) := ({} : Conn).receive (input.extract 0 7)
      let (_, b) := c.receive (input.extract 7 input.size)
      messagesOf (a ++ b) == messagesOf whole && messagesOf whole == ["text:Hello", "binary:010203"]) ]

/-! ### Against websockets -/

def oracleLimits : Limits := { maxPayload := 1024, maxMessage := 1024 }

def sentFrames (b : ByteArray) : Nat → List Frame
  | 0 => []
  | fuel + 1 =>
    match decode { maxPayload := b.size } b with
    | .frame f n => f :: sentFrames (b.extract n b.size) fuel
    | _ => []

def answer (c : Case) : Answer :=
  if c.op != "server" then none
  else
    let evs := run c.input oracleLimits
    let messages := evs.filterMap fun
      | .message (.text s) => some (Json.arr #[.str "text", .str (Bytes.hex s.toUTF8)])
      | .message (.binary b) => some (Json.arr #[.str "binary", .str (Bytes.hex b)])
      | _ => none
    let sent := sentFrames (sentOf evs) (sentOf evs).size
    let pongs := sent.filterMap fun f => if f.opcode == .pong then some (Json.str (Bytes.hex f.payload)) else none
    let close : Json := match sent.find? (·.opcode == .close) with
      | some f => if f.payload.size ≥ 2 then ((f.payload[0]!.toNat * 256 + f.payload[1]!.toNat : Nat) : Json)
        else (-1 : Int)
      | none => .null
    some (Json.mkObj [("messages", .arr messages.toArray), ("pongs", .arr pongs.toArray), ("close", close)])

/-- Whether a close frame comes while a message is open in fragments. -/
def closeInFragments (b : ByteArray) : Nat → Bool → Bool
  | 0, _ => false
  | fuel + 1, open_ =>
    match decode { maxPayload := b.size } b with
    | .frame f n =>
      if f.opcode == .close then open_
      else
        let open_ := match f.opcode with
          | .text | .binary | .continuation => !f.fin
          | _ => open_
        closeInFragments (b.extract n b.size) fuel open_
    | _ => false

/-- Whether a control frame comes, while a message is open in fragments, longer than what is left
of the message's limit. Only headers are read, so a frame cut off counts. -/
def controlOverRest (b : ByteArray) : Nat → Option Nat → Bool
  | 0, _ => false
  | fuel + 1, sofar =>
    match readHeader { maxPayload := 1 <<< 62, maxMessage := 1 <<< 62 } none 0 (b.extract 0 14).data.toList with
    | some (.ok h) =>
      if h.opcode.control && sofar.any (h.length > oracleLimits.maxMessage - ·) then true
      else
        let sofar := match h.opcode with
          | .text | .binary => if h.fin then none else some h.length
          | .continuation => if h.fin then none else sofar.map (· + h.length)
          | _ => sofar
        controlOverRest (b.extract (h.size + h.length) b.size) fuel sofar
    | _ => false

/-- The differences decided: websockets' Sans-I/O layer leaves a text's UTF-8 to the layer above,
which fails with 1007 as we do; it fails a close that arrives inside a fragmented message, which
RFC 6455 §5.4 allows between fragments, as we do; and it counts a control frame inside a
fragmented message against what is left of the message's limit, where we count only data. -/
def known (c : Case) (theirs : Answer) : Option String :=
  match theirs with
  | some j =>
    let msgs := match j.getObjValD "messages" with | .arr a => a.toList | _ => []
    if msgs.any (fun m => match m with | .arr a => a[0]? == some (.str "text-invalid") | _ => false) then
      some "websockets' Sans-I/O layer leaves UTF-8 to the layer above"
    else if closeInFragments c.input c.input.size false then
      some "websockets fails a close inside a fragmented message"
    else if controlOverRest c.input c.input.size none then
      some "websockets counts a control frame against a fragmented message's limit"
    else none
  | none => none

def payloadGen : Gen ByteArray := do
  match ← Gen.below 24 with
  | 0 => return ⟨#[0xff, 0xfe]⟩
  | 1 | 2 => return ⟨Array.replicate (1000 + (← Gen.below 100)) 0x61⟩
  | 3 | 4 | 5 => return closePayload (← Gen.pick [1000, 1001, 1005, 1006, 1015, 2000, 3000, 4999, 5000]) (← Gen.pick ["", "bye"])
  | _ => return (String.ofList (← Gen.list (← Gen.below 6) (Gen.pick "abcé☺".toList))).toUTF8

def frameGen : Gen ByteArray := do
  let op ← Gen.pick [Opcode.text, .text, .binary, .continuation, .ping, .pong, .close]
  let fin ← Gen.chance 70
  let k0 := (← Gen.below 256).toUInt8
  let k1 := (← Gen.below 256).toUInt8
  let mask := if ← Gen.chance 95 then some #v[k0, k1, 3, 4] else none
  return encode { fin, opcode := op, mask, payload := ← payloadGen }

def case : Gen Case := do
  let frames ← Gen.list (1 + (← Gen.below 4)) frameGen
  let input := frames.foldl (· ++ ·) .empty
  let input ← if ← Gen.chance 15 then do
      let i ← Gen.below (input.size + 1)
      let b := (← Gen.below 256).toUInt8
      pure (if h : i < input.size then input.set i b h else input)
    else pure input
  return ⟨"server", input⟩

def package : Package where
  name := "websocket"
  reference := .python "websockets"
  edges := [⟨"server", masked .text "Hello".toUTF8⟩, ⟨"server", masked .ping "p".toUTF8⟩,
    ⟨"server", masked .close (closePayload 1000)⟩, ⟨"server", encode { opcode := .text, payload := "x".toUTF8 }⟩,
    ⟨"server", bytes [0x82, 0xfe, 0x00, 0x05, 1, 2, 3, 4, 0, 0, 0, 0, 0]⟩]
  case
  answer
  known
  shrinks := false
  recorded := 400

end Tests.Oracle.WebSocket
