/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Gate
public import Lanes.Web.Http.Stream
public import Lanes.Web.Http.Upgrade
public import Lanes.Web.Http.WebSocket

/-!
WebSockets behind the gate: what the system sees of a socket, and a socket's side of the server,
as a pure machine the server's loop runs (`Http.Upgrade`).

A request that `Server.wants` opens a socket: the server checks its handshake (`check`), hands
its head to the system, and the system answers it `accept` (or anything else, which refuses it).
From then on the socket is known by the id its head entered with:

- each message received is a request to the system (`Msg.message`), through the gate, repeating
  the head; the system answers it `Response.taken` once it has taken it, and the next is handed
  on only then. `503` offers it again later; any other refusal closes the socket.
- the system sends with outputs that answer the socket's id: `text`, `binary` or `close`.
- when the socket ends, however it ends, the system is told once (`Msg.closed`), and answers it
  as it answers a message.

The session answers pings, pings a peer that has been quiet, closes one that stays quiet, waits a
while for the peer's close after its own, and closes a peer that does not take what is sent: the
bytes waiting to be written are bounded (`Session.Config.outbox_max`). What it writes are frames
a client reads (`WebSocket.Session.step_writes`, in `Lanes/Web/Http/WebSocketSessionSound.lean`),
and it has at most one request with the system at a time, so a socket holds at most one place
among the gate's pending requests, and only while that request is with the system.
-/

@[expose] public section

namespace Lanes.WebSocket

open Http

/-! ### What the system sees -/

/-- A colon is not in a token, so a request read from a client never has a header of this name. -/
def kindName : String := ":websocket"
def codeName : String := ":code"

/-- A request the server hands the system for the socket whose head entered with the id
`socket`. -/
inductive Msg where
  /-- Message `index` received on the socket. -/
  | message (socket index : Nat) (m : Message)
  /-- The socket has ended, with this close code. -/
  | closed (socket code : Nat)
  deriving Repr

/-- What a request handed to the system is, if it is one of a socket's. -/
def msg? (r : Request) : Option Msg := do
  let socket ← (r.headers.lookup Stream.headName).bind decimal?
  let index ← (r.headers.lookup Stream.indexName).bind decimal?
  match r.headers.lookup kindName with
  | some "text" => return .message socket index (.text (← String.fromUTF8? r.body))
  | some "binary" => return .message socket index (.binary r.body)
  | some "closed" => return .closed socket (← (r.headers.lookup codeName).bind decimal?)
  | _ => none

/-- What the session hands the system. -/
inductive Ask where
  | message (m : Message)
  | closed (code : Nat)
  deriving Repr

/-- The request for `ask`, numbered `index`, repeating the head. -/
def Ask.request (head : Request) (index : Nat) : Ask → Request
  | .message (.text s) =>
    { head with headers := (kindName, "text") :: (Stream.indexName, toString index) :: head.headers
                body := s.toUTF8 }
  | .message (.binary b) =>
    { head with headers := (kindName, "binary") :: (Stream.indexName, toString index) :: head.headers
                body := b }
  | .closed code =>
    { head with headers := (kindName, "closed") :: (Stream.indexName, toString index)
                  :: (codeName, toString code) :: head.headers
                body := .empty }

/-- The answer to the head that opens a socket, with the subprotocol chosen, if any. -/
def accept (protocol : Option String := none) : Response :=
  { status := 101, headers := (protocol.map fun p => [("sec-websocket-protocol", p)]).getD [] }

/-- An output that sends a text to the socket it answers. -/
def text (s : String) : Response := { headers := [(kindName, "text")], body := s.toUTF8 }

def binary (b : ByteArray) : Response := { headers := [(kindName, "binary")], body := b }

/-- An output that closes the socket it answers. -/
def close (code : Nat := 1000) (reason : String := "") : Response :=
  { headers := [(kindName, "close"), (codeName, toString code)], body := reason.toUTF8 }

/-- What the system asks to be done with a socket. -/
inductive Send where
  | message (m : Message)
  | close (code : Nat) (reason : String)

/-- What an output to a socket asks; `none` if it is none of `text`, `binary` and `close`, or a
close with a code a server may not send. -/
def Send.ofResponse? (r : Response) : Option Send :=
  match r.headers.lookup kindName with
  | some "text" => (String.fromUTF8? r.body).map (.message ∘ .text)
  | some "binary" => some (.message (.binary r.body))
  | some "close" => do
    let code ← (r.headers.lookup codeName).bind decimal?
    if validCode code then return .close code ((String.fromUTF8? r.body).getD "") else none
  | _ => none

/-! ### A socket's side of the server -/

namespace Session

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  /-- What is received: a frame's payload, and a message's. -/
  limits : Limits := {}
  /-- Bytes of a frame sent: a longer message is sent in fragments. At least 125, the most a
  control frame holds, and at most 2⁶². -/
  frame_max : Nat := 65536
  /-- Bytes of frames waiting to be written. While there are more, nothing is read; a message
  that would make more closes the socket, `1008`. -/
  outbox_max : Nat := 4194304
  /-- Bytes read at once. -/
  read_max : Nat := 65536
  /-- How long the peer may send nothing before it is pinged. -/
  ping_ms : Nat := 20000
  /-- How long the peer may send nothing, pongs included, before the socket is closed, `1011`. -/
  idle_ms : Nat := 60000
  /-- How long the peer's close is waited for, after this side's. -/
  close_ms : Nat := 5000
  /-- How long to wait before handing the system again what it was too busy to take. -/
  poll_ms : Nat := 1000

/-- The bytes of a frame sent. -/
def Config.cap (cfg : Config) : Nat := min (max 125 cfg.frame_max) (2 ^ 62)

end Session

structure Session where
  head : Request
  /-- The answer to the head, written first. -/
  hello : ByteArray
  conn : Conn
  attached : Bool := false
  /-- Frames to write, not yet handed to the socket. -/
  outbox : ByteArray := .empty
  /-- A write has been handed to the socket and has not been sent. -/
  writing : Bool := false
  /-- Messages received and not yet handed to the system, oldest first. -/
  inbox : List Message := []
  /-- The request with the system, by its number; or to be handed again at `again`. -/
  asked : Option (Nat × Ask) := none
  again : Option Nat := none
  /-- The number of the next request. -/
  index : Nat := 0
  /-- When bytes were last received. -/
  heard_ms : Nat
  pinged : Bool := false
  /-- When this side's close was sent. -/
  closing_ms : Option Nat := none
  /-- The socket is over, with this code: what is to be written is, and then it closes. -/
  ended : Option Nat := none
  /-- The socket is closed. -/
  shut : Bool := false
  /-- The system has been told the socket ended, or will not be. -/
  told : Bool := false
  stopping : Bool := false

namespace Session

variable (cfg : Config)

/-- `payload` as frames of at most `cap` bytes: one, or fragments of a message. -/
def fragments (cap : Nat) (op : Opcode) (payload : ByteArray) : ByteArray :=
  if _h : payload.size ≤ max 1 cap then encode { opcode := op, payload }
  else
    encode { fin := false, opcode := op, payload := payload.extract 0 (max 1 cap) }
      ++ fragments cap .continuation (payload.extract (max 1 cap) payload.size)
termination_by payload.size
decreasing_by simp only [ByteArray.size_extract]; omega

/-- The headers of the answer to the head that go out with the `101`: not those the handshake
writes, nor any the reader would not keep. -/
def extra (r : Response) : List (String × String) :=
  r.headers.filter fun (n, v) =>
    Response.kept (n, v) && !["upgrade", "connection", "sec-websocket-accept",
      "sec-websocket-protocol"].contains n.toLower

/-- The session once the system has answered the head `r`, a `101`. A head whose handshake does
not check, which the bridge refuses before the system sees it, is answered `400` and closed. -/
def start (now_ms : Nat) (head : Request) (r : Response) : Session :=
  let protocol := (r.headers.find? (·.1.toLower == "sec-websocket-protocol")).map (·.2)
  match check head with
  | .ok key =>
    let hello := { switching key protocol with
                   headers := (switching key protocol).headers ++ extra r }
    { head, hello := hello.headWire [], conn := { limits := cfg.limits }, heard_ms := now_ms }
  | .error e =>
    { head, hello := e.response.wire, conn := { limits := cfg.limits }, heard_ms := now_ms
      ended := some protocolError }

/-- Whether the socket may still send: not ended, and no close sent. -/
def live (s : Session) : Bool := s.ended.isNone && s.closing_ms.isNone

/-- This side closes: its close frame is to be written, and the peer's waited for. -/
def closeWith (now_ms : Nat) (code : Nat) (reason : String) (s : Session) : Session :=
  if s.live then
    let (conn, bytes) := s.conn.close code reason
    { s with conn, outbox := s.outbox ++ bytes, closing_ms := some now_ms }
  else s

/-- This side fails the socket: its close frame is written, and the socket closes then. -/
def failWith (code : Nat) (s : Session) : Session :=
  if s.ended.isSome then s
  else
    let bytes := if s.live then (s.conn.close code).2 else .empty
    { s with outbox := s.outbox ++ bytes, ended := some code }

/-- A message the system sends, unless the peer is too slow to take what is waiting. -/
def sendMessage (m : Message) (s : Session) : Session :=
  if !s.live then s
  else
    let bytes := match m with
      | .text t => fragments cfg.cap .text t.toUTF8
      | .binary b => fragments cfg.cap .binary b
    if s.outbox.size + bytes.size ≤ cfg.outbox_max then { s with outbox := s.outbox ++ bytes }
    else failWith policyViolation { s with outbox := .empty }

/-- What `Conn.receive` asks, kept. -/
def absorb (s : Session) : List Event → Session
  | [] => s
  | .message m :: rest => absorb { s with inbox := s.inbox ++ [m] } rest
  | .send bytes :: rest => absorb { s with outbox := s.outbox ++ bytes } rest
  | .closed code :: rest => absorb { s with ended := s.ended <|> some code } rest

def receive (now_ms : Nat) (bytes : ByteArray) (s : Session) : Session :=
  if s.ended.isSome then s
  else
    let (conn, events) := s.conn.receive bytes
    absorb { s with conn, heard_ms := now_ms, pinged := false } events

/-- The system's answer to request `index`: taken, or too busy to take it now, or refused. -/
def answered (now_ms index : Nat) (r : Response) (s : Session) : Session :=
  match s.asked with
  | some (k, ask) =>
    if k != index || s.again.isSome then s
    else if r.status == 503 && !s.stopping then { s with again := some (now_ms + cfg.poll_ms) }
    else
      let s := { s with asked := none }
      match ask with
      | .closed _ => { s with told := true }
      | .message _ =>
        if r.status < 300 then s
        else closeWith now_ms (if r.status < 500 then policyViolation else internalError) ""
          { s with inbox := [] }
  | none => s

def pushed (now_ms : Nat) (r : Response) (s : Session) : Session :=
  match Send.ofResponse? r with
  | some (.message m) => sendMessage cfg m s
  | some (.close code reason) => closeWith now_ms code reason s
  | none => closeWith now_ms internalError "" s

/-- What time does: the peer's close not come, the peer too quiet, or due a ping. -/
def tick (now_ms : Nat) (s : Session) : Session :=
  if !s.attached || s.ended.isSome then s
  else if s.closing_ms.any (· + cfg.close_ms ≤ now_ms) then { s with ended := some 1006 }
  else if s.heard_ms + cfg.idle_ms ≤ now_ms then failWith internalError s
  else if s.live && !s.pinged && s.heard_ms + cfg.ping_ms ≤ now_ms then
    { s with outbox := s.outbox ++ Conn.frameBytes .ping .empty, pinged := true }
  else s

/-- Hand the system the next request, if none is with it: a message received, or, once the
socket has ended and every message is handed on, that it has ended. -/
def offer (now_ms : Nat) (s : Session) : Session × List Http.Upgrade.Action :=
  match s.asked with
  | some (k, ask) =>
    if s.again.any (· ≤ now_ms) then ({ s with again := none }, [.submit k (ask.request s.head k)])
    else (s, [])
  | none =>
    match s.inbox, s.ended with
    | m :: rest, _ =>
      ({ s with inbox := rest, asked := some (s.index, .message m), index := s.index + 1 },
        [.submit s.index ((Ask.message m).request s.head s.index)])
    | [], some code =>
      if s.told then (s, [])
      else ({ s with asked := some (s.index, .closed code), index := s.index + 1 },
        [.submit s.index ((Ask.closed code).request s.head s.index)])
    | [], none => (s, [])

/-- Write what is waiting, if no write is; once the socket has ended, write it all and close. -/
def flush (s : Session) : Session × List Http.Upgrade.Action :=
  if s.shut then (s, [])
  else if s.ended.isSome then
    ({ s with shut := true, outbox := .empty },
      if s.attached then (if s.outbox.isEmpty then [] else [.write s.outbox]) ++ [.close] else [])
  else if s.attached && !s.writing && !s.outbox.isEmpty then
    ({ s with outbox := .empty, writing := true }, [.write s.outbox])
  else (s, [])

def advance (now_ms : Nat) (s : Session) : Session × List Http.Upgrade.Action :=
  let (s, asks) := offer now_ms s
  let (s, writes) := flush s
  (s, asks ++ writes)

/-- What the session does about one thing that happened at `now_ms`. -/
def step (now_ms : Nat) (s : Session) : Http.Upgrade.Event → Session × List Http.Upgrade.Action
  | .attached rest =>
    if s.attached || s.shut then (s, [])
    else
      let s := receive now_ms rest { s with attached := true, heard_ms := now_ms, writing := true }
      let (s, actions) := advance now_ms s
      (s, .write s.hello :: actions)
  | .received bytes => advance now_ms (receive now_ms bytes s)
  | .ended | .broken => advance now_ms { s with ended := s.ended <|> some 1006 }
  | .sent => advance now_ms { s with writing := false }
  | .tick => advance now_ms (tick cfg now_ms s)
  | .stop => advance now_ms (closeWith now_ms goingAway "" { s with stopping := true })
  | .answered index r => advance now_ms (answered cfg now_ms index r s)
  | .pushed r => advance now_ms (pushed cfg now_ms r s)

def wantsInput (s : Session) : Bool :=
  s.attached && s.ended.isNone && s.inbox.isEmpty && s.outbox.size ≤ cfg.outbox_max

def earlier : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | a, b => a <|> b

def wakeAt (s : Session) : Option Nat :=
  let timers :=
    if !s.attached || s.ended.isSome then none
    else
      earlier (s.closing_ms.map (· + cfg.close_ms))
        (earlier (some (s.heard_ms + cfg.idle_ms))
          (if s.live && !s.pinged then some (s.heard_ms + cfg.ping_ms) else none))
  earlier s.again timers

def closed (s : Session) : Bool := s.shut && s.told

end Session

/-- Which requests open a WebSocket, and the limits of the sockets. -/
structure Server where
  wants : Request → Bool
  config : Session.Config := {}

/-- The bridge with the handshake checked: a request that is to open a socket and does not ask
as RFC 6455 says is answered `400`, or `426` for another version, before the system sees it. -/
def Server.bridge {σ : Signature} (ws : Server) (b : Http.Bridge σ) : Http.Bridge σ :=
  { b with decode := fun id r =>
      if ws.wants r && (msg? r).isNone then
        match check r with
        | .error e => .error e.response
        | .ok _ => b.decode id r
      else b.decode id r }

/-- The protocol for `Http.serve`'s `upgrade`. -/
def Server.upgrade (ws : Server) : Http.Upgrade where
  wants := ws.wants
  State := Session
  start := Session.start ws.config
  step := Session.step ws.config
  wantsInput := Session.wantsInput ws.config
  room _ := ws.config.read_max
  wakeAt := Session.wakeAt ws.config
  unsent s := s.writing
  closed := Session.closed

end Lanes.WebSocket
