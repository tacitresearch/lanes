/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.ReadRequest
public import Lanes.Web.Http.WireSpec

/-!
What a streamed request or response is to the system behind the gate. A system sees each piece
of a request body, and is asked for each part of a response, as a request of its own through the
gate, so that pieces and parts take the path the request took, in its order, each with an id, a
deadline and the gate's bound (`docs/decisions/` "Streams go through the gate").

- A **piece** repeats the head of the request it belongs to, with the piece's bytes as its body.
  The system answers it to say it has taken it: `503` asks for it again later, any other status
  of 300 or more refuses the rest of the body.
- A **pull** repeats the head too and asks for the next part of the response. The system answers
  it with a part (`Response.part`), with nothing yet (`Response.nothing`), or with the end
  (`Response.finished`).

Both carry headers whose names are not tokens, which no request read from a client has, and
the server tags each with the id its head entered the system with (`Stream.tag`), so that the
system knows which request it belongs to.
-/

@[expose] public section

namespace Lanes.Http

namespace Stream

/-- How the parts of a streamed response are written: as the bytes of a body, or as events
(`Lanes.Web.Http.Sse`). -/
inductive Mode where
  | bytes
  | events
  deriving DecidableEq, Repr

/-- A colon is not in a token, so a request read from a client never has a header of this name. -/
def kindName : String := ":stream"
def indexName : String := ":index"
def afterName : String := ":after"
def headName : String := ":head"

inductive Msg where
  | piece (head : Nat) (index : Nat) (data : ByteArray) (last : Bool)
  | pull (head : Nat) (index : Nat) (after : Option String)
  deriving DecidableEq, Repr

/-- Piece `index` of the body of the request whose head is `head`. -/
def piece (head : Request) (index : Nat) (data : ByteArray) (last : Bool) : Request :=
  { head with
    headers := (kindName, if last then "last" else "piece") :: (indexName, toString index)
      :: head.headers
    body := data }

/-- A call for part `index` of the response to `head`, after the event `after` if one was sent. -/
def pull (head : Request) (index : Nat) (after : Option String) : Request :=
  { head with
    headers := (kindName, "pull") :: (indexName, toString index)
      :: ((after.map (afterName, ·)).toList ++ head.headers)
    body := .empty }

/-- A piece or a pull of the request whose head entered the system with the id `head`. -/
def tag (r : Request) (head : Nat) : Request :=
  { r with headers := (headName, toString head) :: r.headers }

/-- What a request handed to the system is, if it is a piece or a pull. -/
def msg? (r : Request) : Option Msg := do
  let head ← (r.headers.lookup headName).bind decimal?
  let index ← (r.headers.lookup indexName).bind decimal?
  match r.headers.lookup kindName with
  | some "piece" => some (.piece head index r.body false)
  | some "last" => some (.piece head index r.body true)
  | some "pull" => some (.pull head index (r.headers.lookup afterName))
  | _ => none

/-- How the system answers a pull. -/
inductive Part where
  | data (bytes : ByteArray)
  /-- Nothing yet: the connection asks again after `poll_ms`. -/
  | nothing
  | finish
  /-- The response cannot go on: the connection closes without its last chunk, so the client
  sees it cut short. -/
  | cut
  deriving DecidableEq, Repr

def part (r : Response) : Part :=
  if r.status == 204 then .finish
  else if r.status == 503 || r.status == 504 then .nothing
  else if 200 ≤ r.status && r.status < 300 then
    if r.body.isEmpty then .nothing else .data r.body
  else .cut

/-- Whether an answer to a request that streams opens a streamed response, and how:
`Transfer-Encoding: chunked` among its headers, with `Content-Type: text/event-stream` for
events. -/
def mode? (r : Response) : Option Mode :=
  if r.headers.any fun (n, v) => n.toLower == "transfer-encoding" && v.toLower == "chunked" then
    some (if r.headers.any fun (n, v) =>
        n.toLower == "content-type" && v.toLower.startsWith "text/event-stream"
      then .events else .bytes)
  else none

end Stream

namespace Response

/-- The head of a response whose body comes in parts, each the answer to a pull. -/
def stream (status : Nat := 200) (headers : List (String × String) := []) : Response :=
  { status, headers := ("Transfer-Encoding", "chunked") :: headers }

/-- The head of a stream of events (Server-Sent Events). -/
def events (headers : List (String × String) := []) : Response :=
  stream 200 (("Content-Type", "text/event-stream") :: ("Cache-Control", "no-cache") :: headers)

/-- An answer to a pull: the next part. -/
def part (bytes : ByteArray) : Response := { body := bytes }

/-- An answer to a pull: nothing yet. -/
def nothing : Response := {}

/-- An answer to a pull: the response ends. -/
def finished : Response := { status := 204 }

/-- An answer to a piece: taken. -/
def taken : Response := { status := 204 }

end Response

end Lanes.Http
