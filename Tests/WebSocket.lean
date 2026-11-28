/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Web.Http.WebSocketSession
import Tests.Live

/-!
WebSockets behind the gate: the session alone, and a room of sockets served over a real socket
to a client written here, and to Python's `websockets` when its environment is there
(`oracles/websockets/live.py`).

The room: a request for `/chat` opens a socket, which the system accepts while fewer than eight
are open; a text is sent to every socket open, its sender's included; `slow` is refused, which
closes its socket; `close me` asks the server to close the sender's socket; when a socket ends,
the others are told `left` and its close code.
-/

namespace Tests.WebSocket

open Lanes Lanes.Http Lanes.WebSocket Std Std.Async Tests.Live

/-! ### The room -/

inductive In where
  | join (req : ReqId)
  | say (req socket : ReqId) (text : String)
  | left (req socket code : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature := Lanes.Server.sig In (ReqId × Http.Response)

def room : Service sig.In sig.Out (List ReqId) where
  init := []
  step members
    | .join req =>
      if members.length < 8 then (members ++ [req], [(req, accept)])
      else (members, [(req, .text "the room is full\n" 503)])
    | .say req socket text =>
      if text == "slow" then (members, [(req, .text "no\n" 403)])
      else if text == "close me" then (members, [(req, .taken), (socket, close 4000 "asked")])
      else (members, (req, .taken) :: members.map (·, WebSocket.text text))
    | .left req socket code =>
      let rest := members.erase socket
      (rest, (req, .taken) :: rest.map (·, WebSocket.text s!"left {code}"))

def roomDecode (id : ReqId) (r : Http.Request) : Except Http.Response In :=
  match msg? r with
  | some (.message socket _ (.text s)) => .ok (.say id socket s)
  | some (.message _ _ (.binary _)) => .error (.text "texts only\n" 400)
  | some (.closed socket code) => .ok (.left id socket code)
  | none => if r.path == ["chat"] then .ok (.join id) else .error (.text "not found\n" 404)

def ws : WebSocket.Server := { wants := (·.path == ["chat"]) }

def bridge : Bridge sig := ws.bridge { decode := roomDecode, encode := some }

/-! ### The session alone -/

def head : Http.Request :=
  { method := .get, path := ["chat"]
    headers := [("host", "x"), ("upgrade", "websocket"), ("connection", "Upgrade"),
      ("sec-websocket-key", "dGhlIHNhbXBsZSBub25jZQ=="), ("sec-websocket-version", "13")] }

def masked (op : Opcode) (b : ByteArray) (fin : Bool := true) : ByteArray :=
  encode { fin, opcode := op, mask := some #v[1, 2, 3, 4], payload := b }

/-- The frames of what a server writes. -/
def framesOf (bytes : ByteArray) : List Frame := Id.run do
  let mut out := []
  let mut rest := bytes
  for _ in [0:bytes.size] do
    match Lanes.WebSocket.decode { maxPayload := 1 <<< 30, maxMessage := 1 <<< 30 } rest (some false) with
    | .frame f n =>
      out := out ++ [f]
      rest := rest.extract n rest.size
    | _ => break
  return out

def writes (actions : List Upgrade.Action) : ByteArray :=
  actions.foldl (fun acc a => match a with | .write b => acc ++ b | _ => acc) .empty

def submits (actions : List Upgrade.Action) : List (Nat × Http.Request) :=
  actions.filterMap fun | .submit i r => some (i, r) | _ => none

def run (cfg : Session.Config) (s : Session) (events : List (Nat × Upgrade.Event)) :
    Session × List Upgrade.Action :=
  events.foldl (fun (s, out) (now, e) => let (s, a) := Session.step cfg now s e; (s, out ++ a))
    (s, [])

def opened (cfg : Session.Config := {}) : Session × List Upgrade.Action :=
  run cfg (Session.start cfg 0 head accept) [(0, .attached .empty)]

def closeCode (f : Frame) : Nat := f.payload[0]!.toNat * 256 + f.payload[1]!.toNat

def sessionTests : List (String × Bool) :=
  let (_, hello) := opened
  let helloText := (String.fromUTF8? (writes hello)).getD ""
  let (_, said) := run {} (opened).1 [(1, .sent), (2, .received (masked .text "hi".toUTF8))]
  let (s, again) := run {} (opened).1 [(1, .sent), (2, .received (masked .text "a".toUTF8 ++ masked .text "b".toUTF8)),
    (3, .answered 0 busy), (4, .tick), (1005, .tick)]
  let (_, next) := run {} s [(1006, .answered 0 .taken)]
  let (_, ponged) := run {} (opened).1 [(1, .sent), (2, .received (masked .ping "p".toUTF8))]
  let (closedS, closing) := run {} (opened).1 [(1, .sent),
    (2, .received (masked .text "last".toUTF8 ++ masked .close (closePayload 1000 "bye")))]
  let (closedS, _) := run {} closedS [(3, .answered 0 .taken), (4, .answered 1 .taken)]
  let small : Session.Config := { frame_max := 200 }
  let (_, long) := run small (opened small).1 [(1, .sent), (2, .pushed (WebSocket.text (String.ofList (List.replicate 500 'x'))))]
  let tight : Session.Config := { outbox_max := 100 }
  let (_, over) := run tight (opened tight).1 [(2, .pushed (WebSocket.text (String.ofList (List.replicate 200 'x'))))]
  let (_, refused) := run {} (opened).1 [(1, .sent), (2, .received (masked .text "x".toUTF8)),
    (3, .answered 0 (.text "no" 403))]
  let (_, quiet) := run {} (opened).1 [(1, .sent), (20001, .tick)]
  let (_, silent) := run {} (opened).1 [(1, .sent), (20001, .tick), (20002, .sent), (60001, .tick)]
  let (_, reasoned) := run {} (opened).1 [(1, .sent),
    (2, .pushed (WebSocket.close 1000 (String.ofList (List.replicate 100 'é'))))]
  let (unanswered, _) := run {} (opened).1 [(1, .sent), (2, .pushed (WebSocket.close 1000)), (5003, .tick)]
  [ ("websocket session: the answer to the head is RFC 6455's",
      helloText.startsWith "HTTP/1.1 101" && (helloText.splitOn "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=").length == 2),
    ("websocket session: a message is handed to the system, repeating the head",
      match submits said with
      | [(0, r)] => (msg? (Stream.tag r 7)).any (fun | .message 7 0 (.text "hi") => true | _ => false)
          && r.path == ["chat"]
      | _ => false),
    ("websocket session: a message the system is too busy for is handed again after poll_ms, and the next only once it is taken",
      (submits again).map (·.1) == [0, 0] && (submits next).map (·.1) == [1]),
    ("websocket session: a ping is answered by a pong with its payload",
      (framesOf (writes ponged)).any fun f => f.opcode == .pong && f.payload == "p".toUTF8),
    ("websocket session: a close is echoed and the socket closes, after the message before it; the system is told once",
      (framesOf (writes closing)).any (fun f => f.opcode == .close && closeCode f == 1000)
        && closing.getLast? matches some .close
        && (submits closing).length == 1 && closedS.closed),
    ("websocket session: a long message is sent in fragments that make it up",
      let fs := framesOf (writes long)
      fs.length == 3 && fs.all (·.payload.size ≤ 200) && (fs.map (·.fin)) == [false, false, true]
        && (fs.map (·.opcode)) == [.text, .continuation, .continuation]
        && (fs.foldl (fun (acc : ByteArray) (f : Frame) => acc ++ f.payload) .empty).size == 500),
    ("websocket session: a peer too slow to take what is sent is closed 1008",
      (framesOf (writes over)).any (fun f => f.opcode == .close && closeCode f == policyViolation)),
    ("websocket session: a message the system refuses closes the socket 1008",
      (framesOf (writes refused)).any (fun f => f.opcode == .close && closeCode f == policyViolation)),
    ("websocket session: a quiet peer is pinged, and one that stays quiet is closed 1011",
      (framesOf (writes quiet)).any (·.opcode == .ping)
        && (framesOf (writes silent)).any (fun f => f.opcode == .close && closeCode f == internalError)),
    ("websocket session: a close's reason is cut to fit 125 bytes, on a character's boundary",
      (framesOf (writes reasoned)).any fun f => f.opcode == .close && f.payload.size ≤ 125
        && (String.fromUTF8? (f.payload.extract 2 f.payload.size)).isSome),
    ("websocket session: the peer's close is waited for close_ms, then the socket ends",
      unanswered.ended == some 1006),
    ("websocket session: a bad handshake is refused before the system sees it",
      (match bridge.decode 0 { head with headers := head.headers.filter (·.1 != "sec-websocket-key") } with
        | .error r => r.status == 400 | _ => false)
      && (match bridge.decode 0 { head with headers := head.headers.map fun (n, v) =>
            if n == "sec-websocket-version" then (n, "12") else (n, v) } with
        | .error r => r.status == 426 | _ => false)) ]

/-! ### `Http.Conn` with a request that switches -/

def connTests : List (String × Bool) :=
  let cfg : Conn.Config := { upgrades := some (·.path == ["chat"]) }
  let bytes := "GET /a HTTP/1.1\r\nHost: x\r\n\r\nGET /chat HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8
  let (c, first) := Conn.step cfg 0 {} (.received bytes)
  let (c, early) := Conn.step cfg 1 c (.responded 1 accept)
  let (c, later) := Conn.step cfg 2 c (.answered 0 (.text "a"))
  let (_, refused) := Conn.step cfg 1 (Conn.step cfg 0 {} (.received
    "GET /chat HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8)).1 (.responded 0 (.text "no" 403))
  [ ("conn: a request that may switch is handed on, and nothing after it is read",
      (first.filterMap fun | .begin s _ => some s | .submit s _ => some s | _ => none) == [0, 1]
        && !c.reading),
    ("conn: a 101 is not written, and the connection is handed over once every earlier response is",
      early.isEmpty && (later.map fun | .write s _ => s!"w{s}" | .switch s .. => s!"s{s}" | _ => "?")
        == ["w0", "s1"] && c.closed),
    ("conn: any other answer to it is written, with Connection: close, and the connection closes",
      (refused.any fun | .write _ b => ((String.fromUTF8? b).getD "").startsWith "HTTP/1.1 403" | _ => false)
        && refused.getLast? == some .close) ]

/-! ### Over a socket -/

structure Peer where
  socket : TCP.Socket.Client
  buffer : IO.Ref ByteArray

def handshake (key : String := "dGhlIHNhbXBsZSBub25jZQ==") (version : String := "13")
    (path : String := "/chat") : String :=
  s!"GET {path} HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n" ++
    s!"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: {version}\r\n\r\n"

def headEnd? (b : ByteArray) : Option Nat :=
  (List.range b.size).find? fun i =>
    i + 3 < b.size && b[i]! == 13 && b[i + 1]! == 10 && b[i + 2]! == 13 && b[i + 3]! == 10

/-- Connect, send `request`, and read the head of the answer. -/
def openPeer (port : UInt16) (request : String) : Async (Peer × String) := do
  let socket ← TCP.Socket.Client.mk
  socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
  socket.send request.toUTF8
  let mut got := ByteArray.empty
  for _ in [0:64] do
    if (headEnd? got).isSome then break
    match ← within 5000 (socket.recv? 65536) with
    | some (some bytes) => got := got ++ bytes
    | _ => break
  let stop := ((headEnd? got).map (· + 4)).getD got.size
  let peer := { socket, buffer := ← IO.mkRef (got.extract stop got.size) }
  return (peer, (String.fromUTF8? (got.extract 0 stop)).getD "")

def Peer.send (p : Peer) (op : Opcode) (payload : ByteArray) : Async Unit :=
  p.socket.send (masked op payload)

/-- The next frame the server sent, or `none` when none comes within five seconds. -/
def Peer.frame (p : Peer) : Async (Option Frame) := do
  for _ in [0:4096] do
    match Lanes.WebSocket.decode { maxPayload := 1 <<< 24 } (← p.buffer.get) (some false) with
    | .frame f n =>
      p.buffer.modify fun b => b.extract n b.size
      return some f
    | .fail _ => return none
    | .more =>
      match ← within 5000 (p.socket.recv? 65536) with
      | some (some bytes) => p.buffer.modify (· ++ bytes)
      | _ => return none
  return none

/-- Frames until one `pick` takes, at most twenty. -/
def Peer.until (p : Peer) (pick : Frame → Bool) : Async (Option Frame) := do
  for _ in [0:20] do
    match ← p.frame with
    | some f => if pick f then return some f
    | none => return none
  return none

def isText (s : String) (f : Frame) : Bool := f.opcode == .text && f.payload == s.toUTF8

/-- Whether the server ends the connection within five seconds. -/
def Peer.ends (p : Peer) : Async Bool := do
  for _ in [0:64] do
    match ← within 5000 (p.socket.recv? 65536) with
    | some (some _) => pure ()
    | some none => return true
    | none => return false
  return false

/-- Python's `websockets` client, if its environment is there: it says `py`, reads it back, and
closes. -/
def python (port : UInt16) (name : String → String) : IO (List (String × Bool)) := do
  let cache := (← IO.getEnv "LANES_ORACLE_CACHE").getD ".lake/oracles"
  let exe : System.FilePath := s!"{cache}/venv/websockets/bin/python"
  unless ← exe.pathExists do return []
  let out ← IO.Process.output
    { cmd := exe.toString, args := #["-I", "oracles/websockets/live.py", toString port] }
  return [(name "websocket live: Python's websockets client talks to the server",
    out.exitCode == 0 && out.stdout.trimAscii.toString == "ok")]

def liveTest (ioThreads : Nat) : Async (List (String × Bool)) := do
  let server ← serve (Lanes.Server.system room) bridge { port := 0, ioThreads }
    (upgrade := some ws.upgrade)
  let some port := server.port | return [("websocket live: the server reports its port", false)]
  let (a, headA) ← openPeer port (handshake)
  let (b, _) ← openPeer port (handshake "x3JJHMbDL1EzLkh9GBhXDw==")
  a.send .text "hi".toUTF8
  let aHi ← a.until (isText "hi")
  let bHi ← b.until (isText "hi")
  a.send .ping "p".toUTF8
  let pong ← a.until (·.opcode == .pong)
  let large := String.ofList (List.replicate 200000 'y')
  a.send .text large.toUTF8
  let mut parts : List Frame := []
  for _ in [0:8] do
    match ← b.frame with
    | some f =>
      parts := parts ++ [f]
      if f.fin then break
    | none => break
  b.send .close (closePayload 1000 "bye")
  let bClose ← b.until (·.opcode == .close)
  let bEnds ← b.ends
  let left ← a.until (isText "left 1000")
  a.send .text "close me".toUTF8
  let asked ← a.until (·.opcode == .close)
  a.send .close (closePayload 4000)
  let aEnds ← a.ends
  let (c, _) ← openPeer port (handshake)
  c.send .text "slow".toUTF8
  let slow ← c.until (·.opcode == .close)
  let (_, noKey) ← openPeer port ("GET /chat HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\n" ++
    "Connection: Upgrade\r\nSec-WebSocket-Version: 13\r\n\r\n")
  let (_, oldVersion) ← openPeer port (handshake (version := "8"))
  let (_, plain) ← openPeer port "GET /else HTTP/1.1\r\nHost: localhost\r\n\r\n"
  let name := fun (s : String) => if ioThreads == 0 then s else s!"{s} (on {ioThreads} IO threads)"
  let py ← python port name
  let (d, _) ← openPeer port (handshake)
  d.send .text "still here".toUTF8
  let dHere ← d.until (isText "still here")
  server.stop
  let away ← d.until (·.opcode == .close)
  return [
    (name "websocket live: the server answers the handshake 101 with RFC 6455's key",
      headA.startsWith "HTTP/1.1 101" && (headA.splitOn "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=").length == 2),
    (name "websocket live: a text goes to every socket in the room, its sender's included",
      aHi.isSome && bHi.isSome),
    (name "websocket live: a ping is answered by a pong", pong.any (·.payload == "p".toUTF8)),
    (name "websocket live: a long message comes in fragments that make it up",
      parts.length > 1 && (parts.foldl (fun (acc : ByteArray) (f : Frame) => acc ++ f.payload) .empty) == large.toUTF8),
    (name "websocket live: a close is echoed and the server ends the connection",
      bClose.any (closeCode · == 1000) && bEnds),
    (name "websocket live: the system is told a socket ended, with its code", left.isSome),
    (name "websocket live: the system closes a socket, and the connection ends after the peer's close",
      asked.any (closeCode · == 4000) && aEnds),
    (name "websocket live: a message the system refuses closes its socket 1008",
      slow.any (closeCode · == policyViolation)),
    (name "websocket live: a handshake without a key is refused 400, another version 426",
      noKey.startsWith "HTTP/1.1 400" && oldVersion.startsWith "HTTP/1.1 426"),
    (name "websocket live: requests that do not switch are served as before",
      plain.startsWith "HTTP/1.1 404"),
    (name "websocket live: stopping the server closes an open socket 1001",
      dHere.isSome && away.any (closeCode · == goingAway))] ++ py

def tests : List (String × Bool) := sessionTests ++ connTests

def live : Async (List (String × Bool)) := do
  return (← liveTest 0) ++ (← liveTest 2)

end Tests.WebSocket
