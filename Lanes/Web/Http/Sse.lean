/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Stream

/-!
Server-Sent Events: what an event is, the bytes the server writes for one (`Sse.Event.encode`),
how the system gives one as its answer to a pull (`Event.response`, `Event.ofResponse`), and a
model of the client's reader of a stream of them (`Sse.parse`, after the WHATWG HTML standard,
9.2.6), against which `Lanes.Web.Http.SseSound` proves that the reader reads what was written.

The model splits lines at LF only: the writer writes no CR, and an event made from a response
has none (`Event.ofResponse`). It gives each event the `id` and `retry` of its own block, where a
browser keeps the last `id` for later events and takes `retry` as its time to reconnect, and it
takes a `retry` of at most eighteen digits, where a browser takes any.
-/

@[expose] public section

namespace Lanes.Http.Sse

structure Event where
  data : String
  event : Option String := none
  id : Option String := none
  retry : Option Nat := none
  deriving DecidableEq, Repr

namespace Event

/-- The lines of an event, each without its LF, the blank line that ends it left out. -/
def lines (e : Event) : List (List Char) :=
  (e.event.map fun n => "event: ".toList ++ n.toList).toList
    ++ (e.id.map fun i => "id: ".toList ++ i.toList).toList
    ++ (e.retry.map fun n => "retry: ".toList ++ (toString n).toList).toList
    ++ (pieces '\n' e.data.toList).map ("data: ".toList ++ ·)

def chars (e : Event) : List Char :=
  e.lines.flatMap (· ++ ['\n']) ++ ['\n']

def encode (e : Event) : ByteArray :=
  (String.ofList e.chars).toUTF8

/-- Whether the client reads the event back as it is: no line break in its name or id, no NUL
in its id, no CR in its data, and a `retry` of at most eighteen digits. -/
def valid (e : Event) : Bool :=
  e.event.all (fun n => !n.toList.contains '\n' && !n.toList.contains '\r')
    && e.id.all (fun i => !i.toList.contains '\n' && !i.toList.contains '\r'
      && !i.toList.contains '\x00')
    && !e.data.toList.contains '\r'
    && e.retry.all (· < 10 ^ 18)

/-- Line breaks as LF: CRLF and a CR alone become LF, as the client reads them. -/
def lf : List Char → List Char
  | '\r' :: '\n' :: rest => '\n' :: lf rest
  | '\r' :: rest => '\n' :: lf rest
  | c :: rest => c :: lf rest
  | [] => []

/-- Without CR, LF or NUL. -/
def oneLine (s : String) : String :=
  String.ofList (s.toList.filter fun c => c != '\r' && c != '\n' && c != '\x00')

def header? (r : Response) (name : String) : Option String :=
  (r.headers.find? (·.1.toLower == name)).map (·.2)

/-- The event a system gives as its answer to a pull: its body is the data, and the headers
`event`, `event-id` and `retry` its other fields. -/
def ofResponse (r : Response) : Event where
  data := String.ofList (lf ((String.fromUTF8? r.body).getD "").toList)
  event := (header? r "event").map oneLine
  id := (header? r "event-id").map oneLine
  retry := (header? r "retry").bind fun v => (decimal? v).filter (· < 10 ^ 18)

def response (e : Event) : Response where
  headers := (e.event.map ("event", ·)).toList ++ (e.id.map ("event-id", ·)).toList
    ++ (e.retry.map fun n => ("retry", toString n)).toList
  body := e.data.toUTF8

end Event

/-- A comment, which keeps a stream open and is no event. -/
def heartbeat : ByteArray := ":\n\n".toUTF8

/-! The client's reader -/

/-- What the reader has gathered of the event whose lines it is reading. -/
structure Reader where
  data : List Char := []
  hasData : Bool := false
  event : Option String := none
  id : Option String := none
  retry : Option Nat := none


/-- A line that is not blank: a comment, or a field and its value, the one blank after the
colon left out. -/
def Reader.field (r : Reader) (line : List Char) : Reader :=
  match line with
  | ':' :: _ => r
  | _ =>
    let value := match line.dropWhile (· != ':') with
      | _ :: ' ' :: v => v
      | _ :: v => v
      | [] => []
    match String.ofList (line.takeWhile (· != ':')) with
    | "data" => { r with data := if r.hasData then r.data ++ '\n' :: value else value, hasData := true }
    | "event" => { r with event := some (String.ofList value) }
    | "id" => if value.contains '\x00' then r else { r with id := some (String.ofList value) }
    | "retry" => match decimal? (String.ofList value) with
      | some n => { r with retry := some n }
      | none => r
    | _ => r

/-- The events of `lines`, each dispatched at the blank line after it; a block without a data
line dispatches none. -/
def Reader.lines : Reader → List (List Char) → List Event
  | _, [] => []
  | r, [] :: rest =>
    (if r.hasData then [{ data := String.ofList r.data, event := r.event, id := r.id, retry := r.retry }]
      else []) ++ Reader.lines {} rest
  | r, line :: rest => Reader.lines (r.field line) rest

/-- The lines of `text` that are ended by LF; what follows the last LF is not a line yet. -/
def splitLf : List Char → List Char → List (List Char)
  | [], _ => []
  | '\n' :: rest, line => line.reverse :: splitLf rest []
  | c :: rest, line => splitLf rest (c :: line)

/-- The events the client has read once it has received `text`. -/
def parse (text : List Char) : List Event :=
  Reader.lines {} (splitLf text [])

end Lanes.Http.Sse
