/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Sync.Mutex
public import Lanes.Lib.Net.Ip
public import Lanes.Web.Http.Conn
public import Lanes.Web.Http.Gate
public import Lanes.Web.Http.Stream

/-!
The server's connections on a loop of C threads (`native/loop.c`), each with its own epoll and its
own listening socket on the port (`SO_REUSEPORT`); Linux only. The C moves bytes and keeps time:
it accepts, reads at most what it is told, writes what it is given, closes when told, and calls
`turn` with what happened. What that means is `Conn.step`'s, here as in the server's own loop.

Each connection's state lives on its thread, held by the C, and is only touched there. What
crosses threads goes through a `Mutex`, which marks it thread-shared: a request through the
server's `submit`, and its answer back through the mailbox of the connection's thread, whose
first letter writes the thread's eventfd.
-/

public section

namespace Lanes.Http

/-- Which loop runs the server's connections. -/
inductive IOLoop where
  /-- `Std.Net` on Lean's libuv loop: every platform. -/
  | lean
  /-- `native/loop.c`: Linux only, refused elsewhere when the server starts. -/
  | c
  deriving DecidableEq, Repr

namespace CLoop

opaque HandleImpl : NonemptyType

/-- The C loop: its threads, their sockets and their tables of connections. -/
def Handle : Type := HandleImpl.type

instance : Nonempty Handle := HandleImpl.property

/-- Bind `threads` listening sockets to `host` and `port` (`0` picks one, shared by all). -/
@[extern "lanes_cloop_new"]
opaque new (host : @& String) (port : UInt16) (threads connections_max : UInt32)
  (write_ms linger_ms tick_ms : UInt64) : IO Handle

@[extern "lanes_cloop_port"]
opaque port (h : @& Handle) : UInt16

@[extern "lanes_cloop_wake"]
opaque wake (h : @& Handle) (thread : UInt32) : BaseIO Unit

/-- Every thread stops accepting, tells each connection `stop` and ends once none is open. -/
@[extern "lanes_cloop_stop"]
opaque stop (h : @& Handle) : BaseIO Unit

/-- Wait for every thread to end; it blocks the calling thread. -/
@[extern "lanes_cloop_join"]
opaque join (h : @& Handle) : BaseIO Unit

/-- An answer for a connection of a thread, in the thread's mailbox. `native/loop.c` reads the
token by its layout: one object, then a 64-bit scalar. -/
structure Mail where
  event : Conn.Event
  token : UInt64

/-- The C holds one of these for each connection. -/
structure Line where
  conn : Conn
  submit : Request → (Response → BaseIO Unit) → BaseIO Unit
  /-- The ids the heads of the requests that stream entered the system with, by number. -/
  heads : List (Nat × ReqId) := []

/-- What the C does after a turn. `native/loop.c` reads it by its layout: two objects, then
four 64-bit scalars in this order. -/
structure Turn where
  line : Line
  /-- Write these bytes, after what is still unwritten. -/
  out : ByteArray
  /-- Read at most this many bytes, while nothing is unwritten; `0`: do not read. -/
  want : UInt64
  /-- Tell the connection `tick` at this time; `0`: no deadline. -/
  deadline_ms : UInt64
  /-- `1`: write what is left, shut down, drain for `linger_ms`, close. -/
  closed : UInt64
  /-- `1`: tell the connection `sent` once nothing is unwritten. -/
  sent : UInt64

/-- What one thread of the C calls with: its own, so that no two threads count references to
it. -/
structure Handler where
  loop : Handle
  thread : UInt32
  config : Conn.Config
  mail : Std.Mutex (Array Mail)
  /-- How the requests of a connection from this peer reach the system. -/
  front : Ip.Addr → Request → (Response → BaseIO Unit) → BaseIO Unit
  /-- How a request that streams, or a piece or a pull of one, reaches the system, and the id it
  entered with; these pass by the operations front, as in the server's own loop. -/
  submitStream : Request → (Response → BaseIO Unit) → BaseIO (Option ReqId)
  /-- Take one more connection, or refuse it (`Conn.Count.admit`). -/
  accept : BaseIO Bool
  leave : BaseIO Unit

/-- Hand the C a handler for each thread and start them. -/
@[extern "lanes_cloop_run"]
opaque run (h : @& Handle) (handlers : Array Handler) : IO Unit

private def post (h : Handler) (m : Mail) : BaseIO Unit := do
  let first ← h.mail.atomically (modifyGet fun q => (q.isEmpty, q.push m))
  if first then wake h.loop h.thread

private def finish (h : Handler) (line : Line) (out : ByteArray) : Turn :=
  let conn := line.conn
  let want := if conn.wantsInput h.config then min (conn.room h.config) 65536 else 0
  let deadline := Conn.earlier (conn.deadline h.config) (conn.wakeAt h.config)
  { line, out, want := want.toUInt64, deadline_ms := (deadline.getD 0).toUInt64
    closed := if conn.closed then 1 else 0, sent := if conn.unsent then 1 else 0 }

/-- A piece or a pull of the request that streams numbered `seq`, under the id its head
entered with. -/
private def toStream (h : Handler) (line : Line) (seq : Nat) (request : Request)
    (reply : Response → BaseIO Unit) : BaseIO Unit :=
  match line.heads.lookup seq with
  | some id => discard <| h.submitStream (Stream.tag request id) reply
  | none => reply (.text "the request is not with the system\n" 400)

/-- Do an action of a turn, as the server's own loop does; what it writes goes after `out`. -/
private def act (h : Handler) (token : UInt64) (line : Line) (out : ByteArray) :
    Conn.Action → BaseIO (Line × ByteArray)
  | .submit seq request => do
    line.submit request fun r => post h { token, event := .answered seq r }
    return (line, out)
  | .begin seq request => do
    let id ← h.submitStream request fun r => post h { token, event := .responded seq r }
    let heads := line.heads.filter (·.1 ≥ line.conn.written)
    return ({ line with heads := (id.map fun id => (seq, id) :: heads).getD heads }, out)
  | .piece seq index request => do
    toStream h line seq request fun r => post h { token, event := .took seq index r }
    return (line, out)
  | .pull seq index request => do
    toStream h line seq request fun r => post h { token, event := .pulled seq index r }
    return (line, out)
  | .interim _ bytes | .write _ bytes | .part _ bytes =>
    return (line, if out.isEmpty then bytes else out ++ bytes)
  | .close => return (line, out)

private def step (h : Handler) (token : UInt64) (line : Line) (event : Conn.Event)
    (now_ms : UInt64) : BaseIO Turn := do
  let wasClosed := line.conn.closed
  let (conn, actions) := line.conn.step h.config now_ms.toNat event
  let mut line := { line with conn }
  let mut out := ByteArray.empty
  for action in actions do
    (line, out) ← act h token line out action
  if conn.closed && !wasClosed then h.leave
  return finish h line out

/-- A connection the C has accepted: its first turn, or `none` to close it. -/
@[export lanes_cloop_open]
private def «open» (h : Handler) (peer : UInt32) (now_ms : UInt64) : BaseIO (Option Turn) := do
  unless ← h.accept do return none
  let submit := h.front (.v4 (.ofNat _ peer.toNat))
  return some (finish h { conn := { since_ms := now_ms.toNat }, submit } .empty)

/-- What the C saw: `0` bytes received, `1` their end, `2` a failed socket, `3` a deadline that
may have passed, `4` the server stopping, `5` everything written sent. -/
@[export lanes_cloop_turn]
private def turn (h : Handler) (token : UInt64) (line : Line) (kind : UInt8) (bytes : ByteArray)
    (now_ms : UInt64) : BaseIO Turn :=
  step h token line (event kind) now_ms
where
  event : UInt8 → Conn.Event
    | 0 => .received bytes
    | 1 => .ended
    | 3 => .tick
    | 4 => .stop
    | 5 => .sent
    | _ => .broken

@[export lanes_cloop_answer]
private def answer (h : Handler) (line : Line) (m : Mail) (now_ms : UInt64) : BaseIO Turn :=
  step h m.token line m.event now_ms

@[export lanes_cloop_take]
private def take (h : Handler) : BaseIO (Array Mail) :=
  h.mail.atomically (modifyGet fun q => (q, #[]))

/-- Start the loop on `handle`'s threads. -/
def start (handle : Handle) (threads : Nat) (config : Conn.Config)
    (front : Ip.Addr → Request → (Response → BaseIO Unit) → BaseIO Unit)
    (submitStream : Request → (Response → BaseIO Unit) → BaseIO (Option ReqId))
    (accept : BaseIO Bool) (leave : BaseIO Unit) : IO Unit := do
  let handlers ← (List.range threads).toArray.mapM fun i => do
    return { loop := handle, thread := i.toUInt32, config, mail := ← Std.Mutex.new #[], front
             submitStream, accept, leave : Handler }
  run handle handlers

end CLoop

end Lanes.Http
