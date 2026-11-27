/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.ReadRequest
public import Lanes.Web.Http.Sse

/-!
One connection of the HTTP server, as a pure function. The socket loop (`Lanes.Web.IO.Server`) tells
it what happened (`Conn.Event`) and does what it answers (`Conn.Action`), and asks it whether to
read the socket (`Conn.wantsInput`), how many bytes (`Conn.room`) and until when to wait
(`Conn.deadline`). Everything else is decided here: what the bytes received are as requests
(by `Request.read`), the order responses go out in, when to answer `100 Continue`, when a head
or a body has taken too long, when to stop reading and when to close.

A request that streams (`Config.streams`) is handed on by its head; its body follows in pieces,
one with the system at a time, and the system's answer may open a response whose parts the
connection asks for one at a time, once what it wrote before has been sent (`Lanes.Web.Http.Stream`).

What it promises is proved of it for every configuration and every sequence of events
(`Lanes/Web/Http/ConnSound.lean`), and the model checker runs it against a client that sends bytes
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
  /-- How long a body may take to arrive, from the end of its head; for a body that streams, how
  long each piece may take, from when the system took the one before. -/
  body_ms : Nat := 30000
  /-- Which requests stream, by their head with the body left out: the body is handed on in
  pieces and the answer may open a streamed response. `none`: none does. -/
  streams : Option (Request → Bool) := none
  /-- Bytes of one piece of a body that streams; at least one is taken. -/
  piece_max : Nat := 65536
  /-- Bytes of a body that streams; a longer one is refused with `413`. -/
  streamBody_max : Nat := 1099511627776
  /-- Bytes of one part of a streamed response; a larger part cuts the response short. -/
  part_max : Nat := 1048576
  /-- How long to wait before asking the system again, after it answered a pull with nothing or
  a piece with `503`. -/
  poll_ms : Nat := 1000
  /-- How long a stream of events may write nothing before a comment keeps it open. -/
  heartbeat_ms : Nat := 15000

inductive Stage where
  | idle
  | head
  | body
  /-- `inflight_max` requests are in flight, so nothing more is read. -/
  | full
  /-- A piece of a body that streams is with the system, so the client is not waited for. -/
  | waiting
  deriving DecidableEq, Repr, Hashable

inductive Outflow.State where
  | going
  /-- The system has ended the response: its last chunk is to be written. -/
  | ended
  /-- The response cannot go on: the connection closes without its last chunk. -/
  | cut
  deriving DecidableEq, Repr, Hashable

/-- A response whose body comes in parts. -/
structure Outflow where
  /-- The request it answers, which each pull repeats. -/
  head : Request
  events : Bool
  close : Bool
  /-- What has come and is not written: the head at first, then the chunks of parts. -/
  pending : ByteArray
  /-- The number of the next pull, or of the one with the system. -/
  index : Nat := 0
  asking : Bool := false
  /-- When to pull again, after an answer with nothing. -/
  again : Option Nat := none
  /-- The id of the last event written, or the one the client said it last read. -/
  after : Option String := none
  state : Outflow.State := .going
  wrote_ms : Nat := 0
  deriving DecidableEq, Repr, Hashable

inductive Slot where
  /-- Handed to the system, which has not answered yet. -/
  | asked (headOnly close : Bool)
  | ready (bytes : ByteArray)
  /-- A request that streams, handed to the system, which has not answered yet. -/
  | opened (head : Request) (headOnly close : Bool)
  | stream (o : Outflow)
  deriving DecidableEq, Repr, Hashable

/-- Where the body of a request that streams is: so many bytes left of a body framed by its
length, or, in chunks, at a size line, in the data of a chunk, at the CRLF after it, or at the
CRLF after the last chunk. -/
inductive Inflow.Framing where
  | length (left : Nat)
  | size
  | data (left : Nat)
  | crlf
  | last
  deriving DecidableEq, Repr, Hashable

/-- The body of a request that streams, being handed on in pieces. -/
structure Inflow where
  seq : Nat
  head : Request
  framing : Inflow.Framing
  /-- The connection ends after the response. -/
  close : Bool
  index : Nat := 0
  /-- The piece with the system, and whether it is the last, until the system has taken it. -/
  asked : Option (ByteArray × Bool) := none
  /-- When to offer it again, after the system was too busy to take it. -/
  again : Option Nat := none
  /-- Bytes of the body handed on so far. -/
  taken : Nat := 0
  /-- `100 Continue` was written or is not asked for. -/
  continued : Bool := true
  deriving DecidableEq, Repr, Hashable

inductive Event where
  | received (bytes : ByteArray)
  /-- The peer sends no more. -/
  | ended
  /-- The socket failed. -/
  | broken
  | answered (seq : Nat) (response : Response)
  /-- The system's answer to the request that streams numbered `seq`. -/
  | responded (seq : Nat) (response : Response)
  /-- The system's answer to piece `index` of the body of the request numbered `seq`. -/
  | took (seq index : Nat) (response : Response)
  /-- The system's answer to pull `index` of the response to the request numbered `seq`. -/
  | pulled (seq index : Nat) (response : Response)
  /-- Everything written has been sent. -/
  | sent
  | tick
  /-- The server is stopping. -/
  | stop
  deriving Repr

inductive Action where
  /-- Hand the request numbered `seq` to the system. -/
  | submit (seq : Nat) (request : Request)
  /-- Hand the system the request that streams numbered `seq`; its answer is `responded`. -/
  | begin (seq : Nat) (request : Request)
  /-- Hand the system a piece of the body of `seq`; its answer is `took`. -/
  | piece (seq index : Nat) (request : Request)
  /-- Ask the system for a part of the response to `seq`; its answer is `pulled`. -/
  | pull (seq index : Nat) (request : Request)
  | interim (seq : Nat) (bytes : ByteArray)
  /-- Write the response to the request numbered `seq`, or the end of it. -/
  | write (seq : Nat) (bytes : ByteArray)
  /-- Write bytes of the streamed response to `seq`, which is not over. -/
  | part (seq : Nat) (bytes : ByteArray)
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
  /-- The body of a request that streams, while it is being handed on. -/
  inflow : Option Conn.Inflow := none
  /-- A part was written that has not been sent: no stream asks for more until it has. -/
  unsent : Bool := false

namespace Conn

/-- `r` as it can be written so that a reader reads it back: headers a reader would not keep
are left out, and a response that cannot be written so becomes a `500`. -/
def closing (close : Bool) : List (String × String) :=
  if close then [("Connection", "close")] else []

def sendable (close : Bool) (r : Response) : Response :=
  let kept := { r with headers := r.headers.filter Response.kept ++ closing close }
  if kept.writable then kept else { status := 500 }

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

/-- `r` as the head of a streamed response, its body left out. -/
def streamed (close : Bool) (r : Response) : Response :=
  { r with headers := r.headers.filter Response.kept ++ closing close, body := .empty }

/-- Whether `r` can head a streamed response: the client's reader reads its head back, and its
status allows a body. -/
def streamable (close : Bool) (r : Response) : Bool :=
  (streamed close r).writable && r.status != 204 && r.status != 304

/-- The head of a streamed response, as `Response.wireChunked` begins it. -/
def streamHead (close : Bool) (r : Response) : ByteArray :=
  (streamed close r).headWire ["Transfer-Encoding: chunked"]

/-- The last chunk, which ends a streamed response. -/
def lastChunk : ByteArray := "0\r\n\r\n".toUTF8

def heartbeatChunk : ByteArray := Response.chunk Sse.heartbeat

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
    | .full | .waiting => none

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

/-- The head at `pos`, whole, of a request that streams, and where its body starts. Its body may
be as long as `streamBody_max`. -/
def streamHead? (c : Conn) : Option (Request.Head × Nat) :=
  match cfg.streams with
  | none => none
  | some streams =>
    match Request.readHead { cfg.limits with body_max := cfg.streamBody_max } c.buffer c.pos with
    | .done head start => if streams (head.incoming .empty).request then some (head, start) else none
    | _ => none

def Inflow.start (seq : Nat) (head : Request.Head) : Inflow where
  seq
  head := (head.incoming .empty).request
  framing := match head.framing with
    | .length n => .length n
    | .chunked => .size
  close := head.close
  continued := !(head.version == .http11 && head.expectsContinue)

/-- The request that streams whose head ends at `start` is handed on, and its body, if it has
one, is to follow in pieces. -/
def begin (now_ms : Nat) (c : Conn) (head : Request.Head) (start : Nat) : Conn :=
  let body := head.framing != .length 0
  { c with pos := start, need := 0
           slots := c.slots ++ [.opened (head.incoming .empty).request head.headOnly head.close]
           reading := body || !head.close, continued := false
           stage := if body then .body else .idle, since_ms := now_ms
           inflow := if body then some (Inflow.start (next c) head) else none }

/-- Read the requests that are whole, while there is room for them in flight. -/
def take (now_ms : Nat) : Nat → Conn → Conn × List Action
  | 0, c => (c, [])
  | fuel + 1, c =>
    if c.closed || !c.reading || c.inflow.isSome then (c, [])
    else if cfg.inflight_max ≤ c.slots.length then (settle now_ms c .full, [])
    else if c.buffer.size - c.pos < c.need then (c, [])
    else
      match streamHead? cfg c with
      | some (head, start) =>
        let (c', actions) := take now_ms fuel (begin now_ms c head start)
        (c', .begin (next c) (head.incoming .empty).request :: actions)
      | none =>
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

/-! Bodies that stream -/

/-- What the next bytes of a body that streams are: more is needed, the body is refused, or a
piece and where it ends. -/
inductive Inflow.Got where
  | more
  | refuse (why : Refusal)
  | piece (data : ByteArray) (stop : Nat) (framing : Inflow.Framing) (last : Bool)

/-- The bytes of the body from `pos`, at most `room` of them and within one chunk, as the strict
reader reads them (`Request.chunks`), with `taken` bytes of it already handed on. `fuel` bounds
the size lines and CRLFs passed on the way. -/
def Inflow.next (bytes : ByteArray) (pos taken room : Nat) :
    Inflow.Framing → (fuel : Nat) → Inflow.Got
  | _, 0 => .more
  | .length left, _ + 1 =>
    let m := min room (min (bytes.size - pos) left)
    if m = 0 then .more
    else .piece (bytes.extract pos (pos + m)) (pos + m) (.length (left - m)) (left = m)
  | .data left, _ + 1 =>
    let m := min room (min (bytes.size - pos) left)
    if m = 0 then .more
    else .piece (bytes.extract pos (pos + m)) (pos + m) (if left = m then .crlf else .data (left - m))
      false
  | .size, fuel + 1 =>
    match Request.chunkSize bytes pos with
    | .more => .more
    | .refuse why => .refuse why
    | .done size start =>
      if size = 0 then Inflow.next bytes start taken room .last fuel
      else if cfg.streamBody_max < taken + size then .refuse .contentTooLarge
      else Inflow.next bytes start taken room (.data size) fuel
  | .crlf, fuel + 1 =>
    match crlf bytes pos with
    | .more => .more
    | .done none => .refuse .badRequest
    | .done (some next) => Inflow.next bytes next taken room .size fuel
  | .last, _ + 1 =>
    match crlf bytes pos with
    | .more => .more
    | .done none => .refuse .badRequest
    | .done (some stop) => .piece .empty stop .last true

/-- The next piece: the bytes of the body from `pos`, across chunks, up to `piece_max`. -/
def Inflow.gather (bytes : ByteArray) : (fuel pos taken : Nat) → Inflow.Framing → ByteArray →
    Inflow.Got
  | 0, pos, _, framing, acc => if acc.isEmpty then .more else .piece acc pos framing false
  | fuel + 1, pos, taken, framing, acc =>
    match Inflow.next cfg bytes pos taken (max 1 cfg.piece_max - acc.size) framing 3 with
    | .more => if acc.isEmpty then .more else .piece acc pos framing false
    | .refuse why => if acc.isEmpty then .refuse why else .piece acc pos framing false
    | .piece data stop framing' last =>
      if last || max 1 cfg.piece_max ≤ acc.size + data.size then
        .piece (acc ++ data) stop framing' last
      else Inflow.gather bytes fuel stop (taken + data.size) framing' (acc ++ data)

def Slot.isOpened : Slot → Bool
  | .opened .. => true
  | _ => false

/-- Hand on the next piece of the body that streams, if the system has taken the one before, and
`100 Continue` first if the head asked for it and every earlier response is written. -/
def pump (now_ms : Nat) (c : Conn) : Conn × List Action :=
  match c.inflow with
  | none => (c, [])
  | some f =>
    if c.closed || !c.reading then ({ c with inflow := none }, [])
    else if !(c.written ≤ f.seq && (c.slots[f.seq - c.written]?.any Slot.isOpened)) then
      ({ c with inflow := none, reading := false }, [])
    else
      match f.asked with
      | some (data, last) =>
        if f.again.any (· ≤ now_ms) then
          ({ c with inflow := some { f with again := none } },
            [.piece f.seq f.index (Stream.piece f.head f.index data last)])
        else (c, [])
      | none =>
        let early := if !f.continued && f.seq == c.written then [Action.interim f.seq continueWire]
          else []
        let f := { f with continued := f.continued || f.seq == c.written }
        match Inflow.gather cfg c.buffer (max 1 cfg.piece_max) c.pos f.taken f.framing .empty with
        | .more => ({ c with inflow := some f }, early)
        | .refuse why =>
          ({ c with inflow := none, reading := false
                    slots := c.slots.set (f.seq - c.written) (.ready (refusal why)) }, early)
        | .piece data stop framing last =>
          (settle now_ms { c with pos := stop, inflow := some { f with framing, asked := some (data, last)
                                                                       taken := f.taken + data.size } }
              .waiting,
            early ++ [.piece f.seq f.index (Stream.piece f.head f.index data last)])

/-- The system's answer to piece `index`: it has taken it, it is too busy and the piece is
offered again after `poll_ms`, or it refuses the rest of the body. -/
def took (now_ms seq index : Nat) (r : Response) (c : Conn) : Conn :=
  match c.inflow with
  | none => c
  | some f =>
    match f.asked with
    | none => c
    | some (_, last) =>
      if f.seq != seq || f.index != index then c
      else if r.status == 503 then
        { c with inflow := some { f with again := some (now_ms + cfg.poll_ms) } }
      else if r.status < 300 then
        if last then settle now_ms { c with inflow := none, reading := c.reading && !f.close } .idle
        else
          settle now_ms
            { c with inflow := some { f with asked := none, again := none, index := f.index + 1 } } .body
      else { c with inflow := none, reading := false }

/-! Responses that stream -/

/-- The system's answer to a request that streams: a streamed response if it opens one, else a
response as any other. -/
def respond (seq : Nat) (r : Response) (c : Conn) : Conn :=
  if c.written ≤ seq then
    match c.slots[seq - c.written]? with
    | some (.opened head headOnly close) =>
      let slot := match Stream.mode? r with
        | some mode =>
          if !headOnly && streamable close r then
            .stream { head, events := mode == .events, close, pending := streamHead close r
                      after := head.header? "last-event-id" }
          else .ready (encode headOnly close r)
        | none => .ready (encode headOnly close r)
      { c with slots := c.slots.set (seq - c.written) slot }
    | _ => c
  else c

/-- A part that has come: its chunk is to be written; of events, not one with the id of the last
written, which the client has. -/
def Outflow.accept (now_ms : Nat) (o : Outflow) (r : Response) : Outflow :=
  if o.events then
    let e := Sse.Event.ofResponse r
    if e.id.isSome && e.id == o.after then { o with again := some (now_ms + cfg.poll_ms) }
    else { o with pending := o.pending ++ Response.chunk e.encode, after := e.id.or o.after }
  else { o with pending := o.pending ++ Response.chunk r.body }

/-- The system's answer to pull `index`. -/
def pulled (now_ms seq index : Nat) (r : Response) (c : Conn) : Conn :=
  if c.written ≤ seq then
    match c.slots[seq - c.written]? with
    | some (.stream o) =>
      if !(o.asking && o.index == index && o.state == .going) then c
      else
        let o := { o with asking := false, index := o.index + 1 }
        let o := match Stream.part r with
          | .data bytes =>
            if cfg.part_max < bytes.size then { o with state := .cut } else Outflow.accept cfg now_ms o r
          | .nothing => { o with again := some (now_ms + cfg.poll_ms) }
          | .finish => { o with state := .ended }
          | .cut => { o with state := .cut }
        { c with slots := c.slots.set (seq - c.written) (.stream o) }
    | _ => c
  else c

/-- The streamed response at the front: write what has come, then its end, or close if it is
cut short; else ask for the next part once what was written has been sent, or keep a stream of
events open. -/
def flushStream (now_ms : Nat) (c : Conn) : Conn × List Action :=
  if c.closed then (c, [])
  else
    match c.slots with
    | .stream o :: rest =>
      let seq := c.written
      let writes := if o.pending.isEmpty then [] else [Action.part seq o.pending]
      let unsent := c.unsent || !o.pending.isEmpty
      let o := if o.pending.isEmpty then o else { o with pending := .empty, wrote_ms := now_ms }
      match o.state with
      | .ended =>
        ({ c with slots := rest, written := seq + 1, unsent
                  since_ms := if c.stage == .idle then now_ms else c.since_ms },
          writes ++ [.write seq lastChunk])
      | .cut =>
        ({ c with slots := .stream o :: rest, closed := true, reading := false, unsent },
          writes ++ [.close])
      | .going =>
        if unsent then ({ c with slots := .stream o :: rest, unsent }, writes)
        else if !o.asking && o.again.all (· ≤ now_ms) then
          ({ c with slots := .stream { o with asking := true, again := none } :: rest },
            [.pull seq o.index (Stream.pull o.head o.index o.after)])
        else if o.events && o.wrote_ms + cfg.heartbeat_ms ≤ now_ms then
          ({ c with slots := .stream { o with wrote_ms := now_ms } :: rest, unsent := true },
            [.part seq heartbeatChunk])
        else ({ c with slots := .stream o :: rest }, [])
    | _ => (c, [])

def earlier : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | a, b => a <|> b

/-- When the connection is to be looked at again though no deadline passes: to offer a piece
again, to pull again, or to keep a stream of events open. -/
def wakeAt (c : Conn) : Option Nat :=
  if c.closed then none
  else
    let inflow := c.inflow.bind (·.again)
    let outflow := match c.slots with
      | .stream o :: _ =>
        if o.state != .going || c.unsent then none
        else earlier (if o.asking then none else o.again)
          (if o.events then some (o.wrote_ms + cfg.heartbeat_ms) else none)
      | _ => none
    earlier inflow outflow

/-- The ready responses at the front, then the streamed one, then those behind it if it ended. -/
def drain (now_ms : Nat) (c : Conn) : Conn × List Action :=
  let (c, before) := flush now_ms c
  let (c, parts) := flushStream cfg now_ms c
  let (c, after) := flush now_ms c
  (c, before ++ parts ++ after)

def advance (now_ms : Nat) (c : Conn) : Conn × List Action :=
  let (c, early) := drain cfg now_ms c
  let (c, taken) := take cfg now_ms (cfg.inflight_max + 1) c
  let (c, pumped) := pump cfg now_ms c
  let (c, writes) := drain cfg now_ms c
  let (c, closing) := finish c
  (c, early ++ taken ++ pumped ++ writes ++ closing)

/-- A stream still going when nothing more is read ends: one of events with its last chunk, one
of bytes cut short. -/
def Slot.stop : Slot → Slot
  | .stream o =>
    .stream (if o.state == .going then { o with state := if o.events then .ended else .cut } else o)
  | s => s

/-- Nothing more is read, a body that streams is no longer handed on, and streams end. -/
def quiet (c : Conn) : Conn :=
  { c with reading := false, inflow := none, slots := c.slots.map Slot.stop }

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
    | .ended => advance cfg now_ms (quiet c)
    | .broken => ({ c with closed := true }, [.close])
    | .answered seq r => advance cfg now_ms (answer seq r c)
    | .responded seq r => advance cfg now_ms (respond seq r c)
    | .took seq index r => advance cfg now_ms (took cfg now_ms seq index r c)
    | .pulled seq index r => advance cfg now_ms (pulled cfg now_ms seq index r c)
    | .sent => advance cfg now_ms { c with unsent := false }
    | .tick => advance cfg now_ms (expire cfg now_ms c)
    | .stop => advance cfg now_ms (quiet c)

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
