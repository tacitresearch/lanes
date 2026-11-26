/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.ReadRequest
public import Lanes.Http.WireSpec

/-!
One connection of the HTTP server, as a pure function. The socket loop (`Lanes.Env.Http`) tells
it what happened (`Conn.Event`) and does what it answers (`Conn.Action`), and asks it whether to
read the socket (`Conn.wantsInput`), how many bytes (`Conn.room`) and until when to wait
(`Conn.deadline`). Everything else is decided here: what the bytes received are as requests
(by `Request.read`), the order responses go out in, when to answer `100 Continue`, when a head
or a body has taken too long, when to stop reading and when to close.

What it promises is proved of it for every configuration and every sequence of events
(`Lanes/Http/ConnSound.lean`), and the model checker runs it against a client that sends bytes
in any pieces, pipelines and leaves (`Tests/HttpConn.lean`).
-/

@[expose] public section

namespace Lanes.Http

namespace Conn

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  limits : Request.Limits := {}
  /-- Requests read from one connection whose responses are not yet written. While there are
  this many, nothing more is read from it. -/
  inflight_max : Nat := 16
  /-- How long a connection with nothing in flight waits for the next request. -/
  idle_ms : Nat := 10000
  /-- How long a head may take to arrive, from when the connection began to wait for it. -/
  head_ms : Nat := 10000
  /-- How long a body may take to arrive, from the end of its head. -/
  body_ms : Nat := 30000

inductive Stage where
  | idle
  | head
  | body
  /-- `inflight_max` requests are in flight, so nothing more is read. -/
  | full
  deriving DecidableEq, Repr, Hashable

inductive Slot where
  /-- Handed to the system, which has not answered yet. -/
  | asked (headOnly close : Bool)
  | ready (bytes : ByteArray)
  deriving DecidableEq, Repr, Hashable

inductive Event where
  | received (bytes : ByteArray)
  /-- The peer sends no more. -/
  | ended
  /-- The socket failed. -/
  | broken
  | answered (seq : Nat) (response : Response)
  | tick
  /-- The server is stopping. -/
  | stop
  deriving Repr

inductive Action where
  /-- Hand the request numbered `seq` to the system. -/
  | submit (seq : Nat) (request : Request)
  | interim (seq : Nat) (bytes : ByteArray)
  /-- Write the response to the request numbered `seq`. -/
  | write (seq : Nat) (bytes : ByteArray)
  | close
  deriving DecidableEq, Repr

end Conn

structure Conn where
  buffer : ByteArray := .empty
  /-- Where the next request starts in `buffer`. -/
  pos : Nat := 0
  /-- Bytes from `pos` that must be there before reading again can give anything but more. -/
  need : Nat := 0
  /-- Requests read whose responses are not written, oldest first, numbered from `written`. -/
  slots : List Conn.Slot := []
  written : Nat := 0
  /-- `false` once no more requests are to be read. -/
  reading : Bool := true
  closed : Bool := false
  stage : Conn.Stage := .idle
  /-- When the connection began to wait for what `stage` says. -/
  since_ms : Nat := 0
  /-- `100 Continue` was sent for the request being read. -/
  continued : Bool := false

namespace Conn

/-- `r` as it can be written so that a reader reads it back: headers a reader would not keep
are left out, and a response that cannot be written so becomes a `500`. -/
def sendable (close : Bool) (r : Response) : Response :=
  let closing := if close then [("Connection", "close")] else []
  let kept := { r with headers := r.headers.filter Response.kept ++ closing }
  if kept.writable then kept else { status := 500, headers := closing }

/-- The bytes of the response to a request; to `HEAD`, without the body. -/
def encode (headOnly close : Bool) (r : Response) : ByteArray :=
  let r := sendable close r
  if headOnly then r.headWire ["Content-Length: " ++ toString r.body.size] else r.wire

def refusal (why : Refusal) : ByteArray :=
  encode false true (.text "the request is refused\n" why.status)

def timeout : ByteArray :=
  encode false true (.text "the request took too long\n" 408)

def continueWire : ByteArray :=
  Response.headWire { status := 100 } []

variable (cfg : Config)

/-- The number the next request read gets. -/
def next (c : Conn) : Nat := c.written + c.slots.length

/-- How many more bytes the connection takes. -/
def room (c : Conn) : Nat := cfg.limits.message_max - (c.buffer.size - c.pos)

def wantsInput (c : Conn) : Bool :=
  !c.closed && c.reading && c.slots.length < cfg.inflight_max && 0 < room cfg c

def deadline (c : Conn) : Option Nat :=
  if c.closed || !c.reading then none
  else
    match c.stage with
    | .idle => if c.slots.isEmpty then some (c.since_ms + cfg.idle_ms) else none
    | .head => some (c.since_ms + cfg.head_ms)
    | .body => some (c.since_ms + cfg.body_ms)
    | .full => none

def settle (now_ms : Nat) (c : Conn) (stage : Stage) : Conn :=
  if c.stage = stage then c else { c with stage, since_ms := now_ms }

/-- What to do while the request at `pos` is not whole: wait for its head or its body, and
answer `100 Continue` to a head that asks for it once every earlier response is written. -/
def waitMore (now_ms : Nat) (c : Conn) : Conn × List Action :=
  match Request.readHead cfg.limits c.buffer c.pos with
  | .done head start =>
    let need := match head.framing with
      | .length n => start + n - c.pos
      | .chunked => 0
    let c := { settle now_ms c .body with need }
    if !c.continued && c.slots.isEmpty && head.version == .http11 && head.expectsContinue then
      ({ c with continued := true }, [.interim (next c) continueWire])
    else (c, [])
  | _ => (settle now_ms c (if c.buffer.size ≤ c.pos then .idle else .head), [])

/-- Read the requests that are whole, while there is room for them in flight. -/
def take (now_ms : Nat) : Nat → Conn → Conn × List Action
  | 0, c => (c, [])
  | fuel + 1, c =>
    if c.closed || !c.reading then (c, [])
    else if cfg.inflight_max ≤ c.slots.length then (settle now_ms c .full, [])
    else if c.buffer.size - c.pos < c.need then (c, [])
    else
      match Request.read cfg.limits c.buffer c.pos with
      | .more => waitMore cfg now_ms c
      | .refuse why => ({ c with reading := false, slots := c.slots ++ [.ready (refusal why)] }, [])
      | .done incoming stop =>
        let (c', actions) := take now_ms fuel
          { c with pos := stop, need := 0, slots := c.slots ++ [.asked incoming.headOnly incoming.close]
                   reading := !incoming.close, continued := false, stage := .idle, since_ms := now_ms }
        (c', .submit (next c) incoming.request :: actions)

/-- The responses at the front that are ready, written in order, and what is left. -/
def flushSlots : Nat → List Slot → List Action × Nat × List Slot
  | n, .ready bytes :: rest =>
    let (actions, written, left) := flushSlots (n + 1) rest
    (.write n bytes :: actions, written, left)
  | n, slots => ([], n, slots)

def flush (now_ms : Nat) (c : Conn) : Conn × List Action :=
  let (actions, written, slots) := flushSlots c.written c.slots
  let since_ms := if actions.isEmpty || c.stage != .idle then c.since_ms else now_ms
  ({ c with written, slots, since_ms }, actions)

def finish (c : Conn) : Conn × List Action :=
  if !c.reading && c.slots.isEmpty then ({ c with closed := true }, [.close]) else (c, [])

def advance (now_ms : Nat) (c : Conn) : Conn × List Action :=
  let (c, early) := flush now_ms c
  let (c, taken) := take cfg now_ms (cfg.inflight_max + 1) c
  let (c, writes) := flush now_ms c
  let (c, closing) := finish c
  (c, early ++ taken ++ writes ++ closing)

def answer (seq : Nat) (r : Response) (c : Conn) : Conn :=
  if c.written ≤ seq then
    match c.slots[seq - c.written]? with
    | some (.asked headOnly close) =>
      { c with slots := c.slots.set (seq - c.written) (.ready (encode headOnly close r)) }
    | _ => c
  else c

/-- Consumed bytes are dropped here, when more arrive, so that each byte is copied once. -/
def receive (bytes : ByteArray) (c : Conn) : Conn :=
  { c with buffer := (if c.pos = 0 then c.buffer else c.buffer.extract c.pos c.buffer.size) ++ bytes
           pos := 0 }

def expire (now_ms : Nat) (c : Conn) : Conn :=
  match deadline cfg c with
  | some t =>
    if t ≤ now_ms then
      if c.stage = .idle || cfg.inflight_max ≤ c.slots.length then { c with reading := false }
      else { c with reading := false, slots := c.slots ++ [.ready timeout] }
    else c
  | none => c

/--
What the connection does about one thing that happened at `now_ms`.

A closed connection does nothing more. One that is no longer reading takes no more bytes; it
writes the responses still due, in order, and then closes. More bytes than `room` is more than
the loop was told to read, and closes it at once.
-/
def step (now_ms : Nat) (c : Conn) (e : Event) : Conn × List Action :=
  if c.closed then (c, [])
  else
    match e with
    | .received bytes =>
      if !c.reading then (c, [])
      else if room cfg c < bytes.size then ({ c with closed := true }, [.close])
      else advance cfg now_ms (receive bytes c)
    | .ended => advance cfg now_ms { c with reading := false }
    | .broken => ({ c with closed := true }, [.close])
    | .answered seq r => advance cfg now_ms (answer seq r c)
    | .tick => advance cfg now_ms (expire cfg now_ms c)
    | .stop => advance cfg now_ms { c with reading := false }

/-- The connection after `events`, each with the time it happened, and what it asked for. -/
def run (c : Conn) : List (Nat × Event) → Conn × List Action
  | [] => (c, [])
  | (now_ms, e) :: rest =>
    let (c, first) := step cfg now_ms c e
    let (c, later) := run c rest
    (c, first ++ later)

/-- How many connections are open, so that no more than a bound are. -/
structure Count where
  count : Nat := 0
  stopping : Bool := false

/-- Whether one more connection is taken: not while stopping, nor beyond `connections_max`. -/
def Count.admit (connections_max : Nat) (n : Count) : Bool × Count :=
  if !n.stopping && n.count < connections_max then (true, { n with count := n.count + 1 })
  else (false, n)

def Count.leave (n : Count) : Count := { n with count := n.count - 1 }

end Conn

end Lanes.Http
