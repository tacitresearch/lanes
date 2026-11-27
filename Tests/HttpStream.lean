/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
A connection whose requests stream, against a client and a system that do anything they may.
The client sends a stream in pieces of a few sizes and may leave; the system answers requests,
pieces and pulls in any order, is too busy for a piece once, answers a pull with nothing, with
an event it sent already, with a part or with the end; the loop says when what was written has
been sent; time passes and the server may stop. The search checks what the connection promises
of streams: the pieces the system takes make up the body the strict reader reads, in order; the
bytes written for a streamed response are its head, the chunks of the parts the system gave and
its last chunk, which the client's reader reads back as the head with those parts as its body,
and of events, the events given, each once; one piece and one pull at a time, none while what
was written is unsent; and the bounds and the order of responses as before.
-/

namespace Tests.HttpStream

open Lanes Lanes.Check Lanes.Http Lanes.Http.Conn

def streaming (r : Request) : Bool :=
  r.path == ["up"] || r.path == ["dl"] || r.path == ["ev"]

def cfg : Config :=
  { limits := { line_max := 40, head_max := 90, fields_max := 4, body_max := 4, chunks_max := 2 }
    inflight_max := 2, idle_ms := 9, head_ms := 9, body_ms := 9
    streams := some streaming, piece_max := 3, streamBody_max := 20, part_max := 4
    poll_ms := 1, heartbeat_ms := 2 }

/-- The strict reader with limits that let it read the whole body. -/
def wide : Request.Limits := { cfg.limits with body_max := 20, chunks_max := 10 }

def lengthUpload : ByteArray :=
  ("POST /up HTTP/1.1\r\nHost: h\r\nContent-Length: 7\r\n\r\nabcdefg"
    ++ "GET /a HTTP/1.1\r\nHost: h\r\n\r\n").toUTF8

def chunkedUpload : ByteArray :=
  ("POST /up HTTP/1.1\r\nHost: h\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nab\r\n4\r\ncdef\r\n0\r\n\r\n"
    ++ "GET /a HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n").toUTF8

def download : ByteArray :=
  ("GET /dl HTTP/1.1\r\nHost: h\r\n\r\n" ++ "GET /a HTTP/1.1\r\nHost: h\r\n\r\n").toUTF8

def events : ByteArray :=
  "GET /ev HTTP/1.1\r\nHost: h\r\nLast-Event-ID: e0\r\n\r\n".toUTF8

/-- What the system answers a request that streams. -/
def opening (r : Request) : Response :=
  if r.path == ["dl"] then Response.stream
  else if r.path == ["ev"] then Response.events
  else .text "got"

/-- The `index`th part the system gives: bytes for a download, an event for events. -/
def partOf (r : Request) (index : Nat) : Response :=
  if r.path == ["ev"] then Sse.Event.response { data := s!"d{index}\nx", id := some s!"e{index + 1}" }
  else Response.part s!"p{index}".toUTF8

inductive Out where
  | interim (seq : Nat)
  | write (seq : Nat) (bytes : ByteArray)
  | part (seq : Nat) (bytes : ByteArray)
  | close
  deriving DecidableEq, Hashable

structure World where
  conn : Conn := {}
  now : Nat := 0
  read : Nat := 0
  ended : Bool := false
  stopped : Bool := false
  /-- Requests handed on, and whether each streams. -/
  handed : List (Nat × Request × Bool) := []
  answered : List Nat := []
  /-- Pieces offered and not answered: number, index, data, last. -/
  offered : List (Nat × Nat × ByteArray × Bool) := []
  /-- The data of the pieces the system took, in turn. -/
  taken : List ByteArray := []
  lastTaken : Bool := false
  busy : Bool := false
  /-- Pulls asked and not answered. -/
  asked : List (Nat × Nat) := []
  /-- The parts the system gave, in turn: data for bytes, events for events. -/
  given : List ByteArray := []
  events : List Sse.Event := []
  repeated : Bool := false
  emptied : Bool := false
  finished : Bool := false
  out : List Out := []
  /-- Something went wrong that a property names. -/
  twoPieces : Bool := false
  twoPulls : Bool := false
  pulledUnsent : Bool := false
  stray : Bool := false
  heartbeat : Bool := false
  retried : Bool := false

def key (w : World) :=
  ((w.conn.buffer, w.conn.pos, w.conn.need, w.conn.slots, w.conn.written, w.conn.reading,
      w.conn.closed, w.conn.stage, w.conn.since_ms, w.conn.continued, w.conn.inflow, w.conn.unsent),
    (w.now, w.read, w.ended, w.stopped, w.handed.map (·.1), w.answered, w.offered, w.taken,
      w.lastTaken, w.busy, w.asked),
    (w.given, w.repeated, w.emptied, w.finished, w.out, w.twoPieces, w.twoPulls, w.pulledUnsent,
      w.stray, w.heartbeat, w.retried))

instance : BEq World := ⟨fun a b => key a == key b⟩
instance : Hashable World := ⟨fun w => hash (key w)⟩

def perform (w : World) (unsent : Bool) : Action → World
  | .submit seq request => { w with handed := w.handed ++ [(seq, request, false)] }
  | .begin seq request => { w with handed := w.handed ++ [(seq, request, true)] }
  | .piece seq index request =>
    let last := (request.headers.find? (·.1 == Stream.kindName)).any (·.2 == "last")
    { w with offered := w.offered ++ [(seq, index, request.body, last)]
             twoPieces := w.twoPieces || !w.offered.isEmpty
             retried := w.retried || w.busy }
  | .pull seq index _ =>
    { w with asked := w.asked ++ [(seq, index)], twoPulls := w.twoPulls || !w.asked.isEmpty
             pulledUnsent := w.pulledUnsent || unsent }
  | .interim seq _ => { w with out := w.out ++ [.interim seq] }
  | .write seq bytes => { w with out := w.out ++ [.write seq bytes] }
  | .part seq bytes =>
    { w with out := w.out ++ [.part seq bytes], heartbeat := w.heartbeat || bytes == heartbeatChunk }
  | .close => { w with out := w.out ++ [.close] }

def tell (w : World) (e : Event) : World :=
  let (conn, actions) := w.conn.step cfg w.now e
  let w := { w with stray := w.stray || (w.conn.closed && !actions.isEmpty) }
  let unsent := w.conn.unsent && !(e matches .sent)
  let (w, _) := actions.foldl (init := (w, unsent)) fun (w, unsent) a =>
    (perform w unsent a, unsent || a matches .part ..)
  { w with conn }

def requestOf (w : World) (seq : Nat) : Option Request :=
  (w.handed.find? (·.1 == seq)).map (·.2.1)

def next (stream : ByteArray) (w : World) : List (String × World) :=
  if w.conn.closed then []
  else
    let room := w.conn.room cfg
    let reads := if w.conn.wantsInput cfg && !w.ended then
      ([2, 1000].filterMap fun piece =>
        let n := min piece (min room (stream.size - w.read))
        if n = 0 then none
        else some ("read", tell { w with read := w.read + n } (.received (stream.extract w.read (w.read + n)))))
        ++ (if w.read == stream.size then [("the client leaves", tell { w with ended := true } .ended)] else [])
      else []
    let answers := w.handed.filterMap fun (seq, request, streams) =>
      if w.answered.contains seq then none
      else
        let w := { w with answered := w.answered ++ [seq] }
        some ("answered", tell w (if streams then .responded seq (opening request)
          else .answered seq (.text s!"r{seq}")))
    let pieces := w.offered.flatMap fun (seq, index, data, last) =>
      let w := { w with offered := w.offered.filter (· != (seq, index, data, last)) }
      [("piece taken", tell { w with taken := w.taken ++ [data], lastTaken := last }
          (.took seq index Response.taken))]
        ++ (if w.busy then [] else [("piece refused: busy", tell { w with busy := true } (.took seq index busy))])
    let pulls := w.asked.flatMap fun (seq, index) =>
      let w := { w with asked := w.asked.filter (· != (seq, index)) }
      match requestOf w seq with
      | none => []
      | some request =>
        let part := partOf request index
        let accepts := w.conn.written ≤ seq && match w.conn.slots[seq - w.conn.written]? with
          | some (.stream o) => o.asking && o.index == index && o.state == .going
          | _ => false
        let fresh :=
          if !accepts then w
          else if request.path == ["ev"] then
            let e := Sse.Event.ofResponse part
            { w with events := w.events ++ [e] }
          else { w with given := w.given ++ [part.body] }
        [("part", tell fresh (.pulled seq index part))]
          ++ (if w.emptied then [] else [("nothing yet", tell { w with emptied := true } (.pulled seq index .nothing))])
          ++ (if 2 ≤ index then [("finished", tell { w with finished := true } (.pulled seq index .finished))] else [])
          ++ (if request.path == ["ev"] && 1 ≤ index && !w.repeated then
                [("an event again", tell { w with repeated := true } (.pulled seq index (partOf request (index - 1))))]
              else [])
    reads ++ answers ++ pieces ++ pulls
      ++ (if w.conn.unsent then [("sent", tell w .sent)] else [])
      ++ (if w.now < 3 then [("tick", tell { w with now := w.now + 1 } .tick)] else [])
      ++ (if w.stopped then [] else [("stop", tell { w with stopped := true } .stop)])

def model (stream : ByteArray) : Model World String where
  init := [{}]
  next := next stream

/-- The bytes written for the response to `seq`, in turn. -/
def bytesOf (w : World) (seq : Nat) : ByteArray :=
  w.out.foldl (init := .empty) fun acc o =>
    match o with
    | .write s bytes | .part s bytes => if s == seq then acc ++ bytes else acc
    | _ => acc

def writes (w : World) : List Nat :=
  w.out.filterMap fun
    | .write seq _ => some seq
    | _ => none

def concat (parts : List ByteArray) : ByteArray := parts.foldl (· ++ ·) .empty

def strictBody (stream : ByteArray) : Option ByteArray :=
  match Request.read wide stream 0 with
  | .done incoming _ => some incoming.request.body
  | _ => none

def isPrefix (a b : ByteArray) : Bool := a.data.toList.isPrefixOf b.data.toList

/-- The body of what is written for `seq`, the head and whole chunks so far. -/
def chunksSoFar (bytes : ByteArray) : Option ByteArray :=
  match headEnd bytes with
  | none => none
  | some start =>
    let rec go (fuel pos : Nat) (acc : ByteArray) : ByteArray :=
      match fuel with
      | 0 => acc
      | fuel + 1 =>
        match chunkHead bytes pos with
        | .done (some (size, dataStart)) =>
          if size = 0 then acc
          else if dataStart + size + 2 ≤ bytes.size then go fuel (dataStart + size + 2)
            (acc ++ bytes.extract dataStart (dataStart + size))
          else acc
        | _ => acc
    some (go bytes.size start .empty)

def streamSeq (w : World) : Option Nat :=
  (w.handed.find? fun (_, r, s) => s && (r.path == ["dl"] || r.path == ["ev"])).map (·.1)

def properties (stream : ByteArray) : List (Property World) :=
  [ .always "responses are written in the order the requests were read, each once" fun w =>
      writes w == List.range (writes w).length,
    .always "the pieces taken are the strict reader's body, in order, all once the last is" fun w =>
      match strictBody stream with
      | some body => isPrefix (concat w.taken) body && (!w.lastTaken || concat w.taken == body)
      | none => w.taken.isEmpty,
    .always "one piece at a time, offered again only after the system was busy" fun w =>
      !w.twoPieces,
    .always "one pull at a time, and none while something written is unsent" fun w =>
      !w.twoPulls && !w.pulledUnsent,
    .always "the bytes of a streamed response are its head and the chunks of the parts given" fun w =>
      match streamSeq w with
      | none => true
      | some seq =>
        let bytes := bytesOf w seq
        bytes.isEmpty || match chunksSoFar bytes with
          | none => false
          | some body =>
            (requestOf w seq).any (·.path == ["ev"]) || isPrefix body (concat w.given),
    .always "a streamed response that ended is read back with the parts as its body" fun w =>
      match streamSeq w with
      | none => true
      | some seq =>
        let bytes := bytesOf w seq
        !(writes w).contains seq || (requestOf w seq).any (·.path == ["ev"]) ||
          match Response.read bytes.size bytes true with
          | .done (some r) => r.body == concat w.given
              && r.headers.contains ("transfer-encoding", "chunked")
          | _ => false,
    .always "events are read back as given, each once" fun w =>
      match streamSeq w with
      | none => true
      | some seq =>
        !(requestOf w seq).any (·.path == ["ev"]) ||
          match chunksSoFar (bytesOf w seq) with
          | none => true
          | some body => (Sse.parse (String.fromUTF8! body).toList).isPrefixOf w.events,
    .always "a closed connection asks for nothing more" fun w => !w.stray,
    .always "the connection closes once, and nothing is written after" fun w =>
      w.out.count .close ≤ 1 && (w.out.getLast?.all (· == .close) || !w.out.contains .close),
    .always "the buffer stays within its bound" fun w =>
      w.conn.pos ≤ w.conn.buffer.size && w.conn.buffer.size ≤ cfg.limits.message_max,
    .always "no more requests are in flight than the bound" fun w =>
      w.conn.slots.length ≤ cfg.inflight_max,
    .sometimes "the last piece is taken" (·.lastTaken),
    .sometimes "a piece is offered again after the system was busy" (·.retried) ]

def streamProperties : List (Property World) :=
  [ .sometimes "a streamed response ends and the request behind it is answered" fun w =>
      w.finished && (writes w).length == 2,
    .sometimes "a pull is answered with nothing" (·.emptied) ]

def eventProperties : List (Property World) :=
  [ .sometimes "a stream of events writes a comment to stay open" (·.heartbeat),
    .sometimes "an event given again is not written again" fun w =>
      w.repeated && (match streamSeq w with
        | some seq => match chunksSoFar (bytesOf w seq) with
          | some body => (Sse.parse (String.fromUTF8! body).toList).length == 2
          | none => false
        | none => false),
    .sometimes "a stream of events ends at stop with its last chunk" fun w =>
      w.stopped && (writes w).length == 1 && w.out.contains .close ]

@[never_extract] def report (stream : ByteArray) (more : List (Property World)) :=
  search (model stream) (properties stream ++ more) {} id

def checks : IO (List (String × Bool)) := do
  let length := report lengthUpload []
  let chunked := report chunkedUpload []
  let down := report download streamProperties
  let evs := report events eventProperties
  for (name, r) in [("length", length), ("chunked", chunked), ("download", down), ("events", evs)] do
    unless r.ok && r.complete do IO.println s!"http stream {name}: {repr r.failure.isSome} {r.states}"
  return [
    ("http stream: a body framed by its length is handed on in pieces that make it up, one at a "
      ++ "time, and the request behind it read", length.ok && length.complete),
    ("http stream: a chunked body likewise", chunked.ok && chunked.complete),
    ("http stream: a streamed response is its head, the chunks of the parts given and its end",
      down.ok && down.complete),
    ("http stream: a stream of events writes each event given once, keeps open and ends at stop",
      evs.ok && evs.complete) ]

end Tests.HttpStream
