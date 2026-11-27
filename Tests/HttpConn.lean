/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
A connection of the HTTP server against a client and a system that do anything they may. The
loop reads the client's bytes in pieces of any of a few sizes, only while the connection wants
them and never more than its room; the client may leave at any moment, before, between or
inside requests; the system answers the requests in any order, some twice, and answers numbers
nobody asked; time passes, and the server may stop. The search explores every order of these
and checks what the connection promises.

The stream pipelines three requests: a `GET`, a `POST` that asks for `100 Continue`, and a
`HEAD` that closes the connection; a second stream has a request the reader refuses between two
it reads, after two. The limits are small, so that the room of the buffer and the bound on requests in
flight both come into play.
-/

namespace Tests.HttpConn

open Lanes Lanes.Check Lanes.Http Lanes.Http.Conn

def cfg : Config :=
  { limits := { line_max := 40, head_max := 80, fields_max := 4, body_max := 4, chunks_max := 2 }
    inflight_max := 2, idle_ms := 2, head_ms := 2, body_ms := 3 }

def pipelined : ByteArray :=
  ("GET /a HTTP/1.1\r\nHost: h\r\n\r\n"
    ++ "POST /b HTTP/1.1\r\nHost: h\r\nContent-Length: 3\r\nExpect: 100-continue\r\n\r\nxyz"
    ++ "HEAD /c HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n").toUTF8

def smuggled : ByteArray :=
  ("GET /a HTTP/1.1\r\nHost: h\r\n\r\n" ++ "GET /z HTTP/1.1\r\nHost: h\r\n\r\n"
    ++ "GET /b HTTP/1.1\r\nHost: h\r\nContent-Length: 1\r\nContent-Length: 1\r\n\r\nx"
    ++ "GET /c HTTP/1.1\r\nHost: h\r\n\r\n").toUTF8

/-- The requests the reader reads in turn from the whole stream, up to one that closes, and the
refusal that ends them, if one does. -/
def readAll (bytes : ByteArray) : Nat → Nat → List Request.Incoming × Option Refusal
  | 0, _ => ([], none)
  | fuel + 1, pos =>
    match Request.read cfg.limits bytes pos with
    | .done incoming stop =>
      if incoming.close then ([incoming], none)
      else
        let (rest, why) := readAll bytes fuel stop
        (incoming :: rest, why)
    | .refuse why => ([], some why)
    | .more => ([], none)

def reply (seq : Nat) : Response := .text s!"r{seq}"

inductive Out where
  | interim (seq : Nat)
  | write (seq : Nat) (bytes : ByteArray)
  | close
  deriving DecidableEq, Hashable

structure World where
  conn : Conn := {}
  now : Nat := 0
  read : Nat := 0
  ended : Bool := false
  stopped : Bool := false
  submitted : List (Nat × Request) := []
  answered : List Nat := []
  twice : Bool := false
  stranger : Bool := false
  out : List Out := []
  /-- An action was asked for by a connection already closed. -/
  stray : Bool := false
  /-- A request was read from more than one piece. -/
  pieced : Bool := false
  /-- At a tick, a deadline had passed and still stood. -/
  overdue : Bool := false
  wasFull : Bool := false

def key (w : World) :=
  ((w.conn.buffer, w.conn.pos, w.conn.need, w.conn.slots, w.conn.written, w.conn.reading,
      w.conn.closed, w.conn.stage, w.conn.since_ms, w.conn.continued, w.conn.inflow, w.conn.unsent),
    (w.now, w.read, w.ended, w.stopped, w.submitted.map (·.1), w.answered, w.twice, w.stranger),
    (w.out, w.stray, w.pieced, w.overdue, w.wasFull))

instance : BEq World := ⟨fun a b => key a == key b⟩
instance : Hashable World := ⟨fun w => hash (key w)⟩

def perform (w : World) : Action → World
  | .submit seq request => { w with submitted := w.submitted ++ [(seq, request)] }
  | .interim seq _ => { w with out := w.out ++ [.interim seq] }
  | .write seq bytes => { w with out := w.out ++ [.write seq bytes] }
  | .close => { w with out := w.out ++ [.close] }
  | .begin .. | .piece .. | .pull .. | .part .. => { w with stray := true }

def tell (w : World) (e : Event) : World :=
  let (conn, actions) := w.conn.step cfg w.now e
  let w := actions.foldl perform { w with conn, stray := w.stray || (w.conn.closed && !actions.isEmpty) }
  let overdue := match e, conn.deadline cfg with
    | .tick, some t => t ≤ w.now
    | _, _ => false
  { w with overdue := w.overdue || overdue, wasFull := w.wasFull || conn.stage == .full }

def next (stream : ByteArray) (w : World) : List (String × World) :=
  if w.conn.closed then []
  else
    let room := w.conn.room cfg
    let reads := if w.conn.wantsInput cfg && !w.ended then
      ([1, 9, 1000].filterMap fun piece =>
        let n := min piece (min room (stream.size - w.read))
        if n = 0 then none
        else
          let pieced := w.pieced || (w.conn.pos < w.conn.buffer.size && n < stream.size - w.read)
          some ("read", tell { w with read := w.read + n, pieced }
            (.received (stream.extract w.read (w.read + n)))))
        ++ [("the client leaves", tell { w with ended := true } .ended)]
      else []
    let answers := w.submitted.filterMap fun (seq, _) =>
      if w.answered.contains seq then
        if w.twice then none
        else some ("answered again", tell { w with twice := true } (.answered seq (reply 7)))
      else some ("answered", tell { w with answered := w.answered ++ [seq] } (.answered seq (reply seq)))
    reads ++ answers
      ++ (if w.stranger then [] else
        [("a number nobody asked is answered", tell { w with stranger := true } (.answered 9 (reply 9)))])
      ++ (if w.now < 3 then [("tick", tell { w with now := w.now + 1 } .tick)] else [])
      ++ (if w.stopped then [] else [("stop", tell { w with stopped := true } .stop)])

def model (stream : ByteArray) : Model World String where
  init := [{}]
  next := next stream

def writes (w : World) : List (Nat × ByteArray) :=
  w.out.filterMap fun
    | .write seq bytes => some (seq, bytes)
    | _ => none

def position (w : World) (o : Out → Bool) : Option Nat := w.out.findIdx? o

/-- Each response written is the system's first answer to the request of its number, written as
that request asks, or the refusal or the timeout that ends the connection, which no request was
handed on for. -/
def answeredRight (stream : ByteArray) (w : World) : Bool :=
  let (expected, why) := readAll stream 8 0
  (writes w).all fun (seq, bytes) =>
    match w.submitted.find? (·.1 == seq), expected[seq]? with
    | some _, some incoming =>
      w.answered.contains seq && bytes == encode incoming.headOnly incoming.close (reply seq)
    | some _, none => false
    | none, _ =>
      bytes == timeout || why.any fun why => seq == expected.length && bytes == refusal why

/-- `100 Continue` is written after every earlier response, before its own, once. -/
def continuedInTurn (w : World) : Bool :=
  w.out.all fun
    | .interim seq =>
      w.out.count (.interim seq) == 1
        && (writes w).all fun (s, bytes) =>
          let here := (position w (· == .write s bytes)).getD 0
          let mine := (position w (· == .interim seq)).getD 0
          if s < seq then here < mine else if s == seq then mine < here else true
    | _ => true

/-- The client has sent everything, stayed, and every request handed on is answered, in no
time: so every response is written and the connection closed after the one that asked. -/
def settled (stream : ByteArray) (w : World) : Bool :=
  w.read == stream.size && !w.ended && !w.stopped && w.now == 0
    && w.submitted.all (w.answered.contains ·.1)

def properties (stream : ByteArray) : List (Property World) :=
  let (expected, why) := readAll stream 8 0
  [ .always "responses are written in the order the requests were read, each once" fun w =>
      (writes w).map (·.1) == List.range (writes w).length,
    .always "the requests handed on are those the reader reads in turn from the whole stream"
      fun w => w.submitted == (List.range w.submitted.length).zip
        ((expected.take w.submitted.length).map (·.request)),
    .always "each response is the first answer to its request, or the refusal or timeout last"
      (answeredRight stream),
    .always "100 Continue goes out after the earlier responses and before its own" continuedInTurn,
    .always "a closed connection asks for nothing more" fun w => !w.stray,
    .always "the connection closes once, and nothing is written after" fun w =>
      w.out.count .close ≤ 1 && (w.out.getLast?.all (· == .close) || !w.out.contains .close),
    .always "the buffer stays within its bound" fun w =>
      w.conn.pos ≤ w.conn.buffer.size && w.conn.buffer.size ≤ cfg.limits.message_max,
    .always "no more requests are in flight than the bound" fun w =>
      w.conn.slots.length ≤ cfg.inflight_max,
    .always "no deadline stands once it has passed" fun w => !w.overdue,
    .always "once settled, every request is answered on the wire and the connection closes"
      fun w => !settled stream w || why.isSome
        || ((writes w).length == expected.length && w.out.contains .close),
    .sometimes "every request is answered and the connection closes" fun w =>
      (writes w).length == expected.length + (if why.isSome then 1 else 0)
        && w.out.contains .close,
    .sometimes "a request is read from more than one piece" (·.pieced),
    .sometimes "requests in flight reach the bound" (·.wasFull),
    .sometimes "an answer is given twice" fun w => w.twice && !w.conn.closed,
    .sometimes "a request is refused or times out" fun w =>
      (writes w).any fun (seq, _) => !(w.submitted.any (·.1 == seq)) ]

/-- Not a constant, so that the search runs when the tests do, not whenever the test binary
starts, as it does for each child process of `Tests.Durable`. -/
@[never_extract] def report (stream : ByteArray) := search (model stream) (properties stream) {} id

def checks : IO (List (String × Bool)) := do
  let pipelined := report pipelined
  let smuggled := report smuggled
  return [
    ("http conn: against a client that sends in any pieces, pipelines and leaves, every promise "
      ++ "holds", pipelined.ok && pipelined.complete),
    ("http conn: and with a request the reader refuses between two it reads",
      smuggled.ok && smuggled.complete)]

def steps (c : Conn) (events : List Event) : Conn × List Action :=
  c.run cfg (events.map (0, ·))

def tests : List (String × Bool) :=
  [ ("http conn: the model reads three requests and refuses one",
      (readAll pipelined 8 0).1.length == 3 && (readAll smuggled 8 0).1.length == 2
        && (readAll smuggled 8 0).2 == some .badRequest),
    ("http conn: 100 Continue is sent for a head that asks, and the body then read",
      let (_, actions) := steps {} [.received
        "POST /b HTTP/1.1\r\nHost: h\r\nContent-Length: 3\r\nExpect: 100-continue\r\n\r\n".toUTF8,
        .received "xyz".toUTF8]
      actions.take 2 == [.interim 0 continueWire,
        .submit 0 { method := .post, path := ["b"], body := "xyz".toUTF8
                    headers := [("host", "h"), ("content-length", "3"), ("expect", "100-continue")] }]),
    ("http conn: a head over its limit is refused with 431 and the connection closed",
      let (c, actions) := steps {}
        [.received ("GET / HTTP/1.1\r\nHost: h\r\nX: " ++ String.ofList (List.replicate 70 'a')).toUTF8]
      c.closed && actions == [.write 0 (refusal .fieldsTooLarge), .close]
        && (String.fromUTF8? (refusal .fieldsTooLarge)).any (·.startsWith "HTTP/1.1 431")),
    ("http conn: more bytes than its room close the connection at once",
      let (c, actions) := steps {} [.received (ByteArray.mk (Array.replicate 145 65))]
      c.closed && actions == [.close]),
    ("http conn: a broken socket closes at once, with requests in flight",
      let (c, actions) := steps {} [.received "GET / HTTP/1.1\r\nHost: h\r\n\r\n".toUTF8, .broken]
      c.closed && actions.getLast? == some .close && actions.length == 2),
    ("http conn: an idle connection is closed at its deadline, with nothing written",
      let (c, actions) := ({} : Conn).run cfg [(1, .tick), (2, .tick)]
      c.closed && actions == [.close]),
    ("http conn: a HEAD is answered with the length of the body and no body",
      encode true false (.text "four") == "HTTP/1.1 200 \r\nContent-Length: 4\r\ncontent-type: text/plain; charset=utf-8\r\nX-Content-Type-Options: nosniff\r\n\r\n".toUTF8),
    ("http conn: headers that cannot be written are left out, and a bad status becomes 500",
      sendable false { status := 99, headers := [("Content-Length", "9"), ("a b", "c"), ("x", "ok")] }
          == { status := 500 }
        && sendable true { headers := [("Content-Length", "9"), ("x", " y")] }
          == { headers := [("X-Content-Type-Options", "nosniff"), ("Connection", "close")] }),
    ("http conn: every response says nosniff, once, the refusals' included",
      (sendable false (.text "a")).headers.contains ("X-Content-Type-Options", "nosniff")
        && (sendable false { headers := [("x-content-type-options", "nosniff")] }).headers
          == [("x-content-type-options", "nosniff")]
        && (((String.fromUTF8? (refusal .contentTooLarge)).getD "").splitOn
          "X-Content-Type-Options: nosniff").length == 2),
    ("http conn: no more connections are taken than the bound, and none while stopping",
      let (a, n) := ({} : Count).admit 1
      let (b, n) := n.admit 1
      let (c, _) := n.leave.admit 1
      a && !b && c && !(({ stopping := true } : Count).admit 5).1) ]

end Tests.HttpConn
