/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Gate

/-!
The HTTP client adapter: the wire format as pure functions, a caller model-checked against what
a called service may do, and the same caller run against a real server and a closed port.
-/

namespace Tests.HttpClient

open Lanes Lanes.Http Std.Async

def bytes (s : String) : ByteArray := s.toUTF8

def body? (response : Option Response) : Option String :=
  response.bind fun r => String.fromUTF8? r.body

def wireTests : List (String × Bool) :=
  [ ("http wire: a request is written with its path and query escaped and no smuggled header",
      (({ method := .post, path := ["a b", "c"], query := [("q", "x&y")]
          headers := [("X-Test", "1"), ("Evil", "a\r\nInjected: 1")], body := bytes "hi" } :
        Request).wire "10.0.0.1")
        == bytes ("POST /a%20b/c?q=x%26y HTTP/1.1\r\nHost: 10.0.0.1\r\nConnection: close\r\n"
          ++ "Content-Length: 2\r\nX-Test: 1\r\n\r\nhi")),
    ("http wire: a response with a length is read to that length",
      let r := Response.parse (bytes "HTTP/1.1 201 Created\r\nContent-Length: 2\r\nX-A: b\r\n\r\nokEXTRA")
      r.map (·.status) == some 201 && body? r == some "ok"
        && (r.bind (·.headers.lookup "x-a")) == some "b"),
    ("http wire: a chunked response is put together",
      body? (Response.parse (bytes ("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n"
        ++ "4\r\nWiki\r\n5;ext=1\r\npedia\r\n0\r\n\r\n"))) == some "Wikipedia"),
    ("http wire: without a length the body runs to the end",
      body? (Response.parse (bytes "HTTP/1.0 200 OK\r\n\r\nall of it")) == some "all of it"),
    ("http wire: a cut body, a cut chunk, a cut head and what is not HTTP are refused",
      [ "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nshort",
        "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nWi",
        "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n",
        "SSH-2.0-OpenSSH\r\n\r\n", "" ].all fun text => (Response.parse (bytes text)).isNone) ]

/-! A caller: asked to fetch, it calls a service and reports the status it got, or that it got
none. -/

inductive In where
  | fetch (id : Nat) (target : Client.Call)
  | reply (id : Nat) (response : Option Response)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (id : Nat) (target : Client.Call)
  | done (id : Nat) (status : Option Nat)
  deriving DecidableEq, Repr, Hashable

abbrev callerSig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- The state is how many calls are open. -/
abbrev caller : System callerSig where
  State _ := Nat
  actor _ :=
    { init := 0
      step := fun calls msg =>
        match msg with
        | .fetch id target => (calls + 1, [.emit (.call id target)])
        | .reply id response => (calls - 1, [.emit (.done id (response.map (·.status)))])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

def port : Client.Port callerSig where
  called
    | .call id target => some (id, target)
    | .done .. => none
  reply id response := .reply id response
  replied
    | .reply id _ => some id
    | .fetch .. => none

/-- Clients ask for each fetch once and remember what they were told. -/
def clients : Outside callerSig (List Nat × List (Nat × Option Nat)) where
  init := ([], [])
  allow d x :=
    match x with
    | .fetch id _ => if id ∈ d.1 then none else some (id :: d.1, d.2)
    | .reply .. => none
  observe d out :=
    match out with
    | .done id status => (d.1, (id, status) :: d.2)
    | .call .. => d

def world := clients.both (Client.outside port)

instance : callerSig.Inspect := {}
instance : caller.Inspect := {}

def target (tcpPort : UInt16) (path : List String := []) : Client.Call :=
  { host := "127.0.0.1", port := tcpPort, request := { method := .get, path } }

def check :=
  Check.system caller
    { driver := world.driver fun d =>
        [.fetch 0 (target 80), .fetch 1 (target 80)] ++ d.2.flatMap fun id =>
          [.reply id (some { status := 200 }), .reply id none] }
    [ .always "nothing is reported that was not asked for" fun w =>
        w.driver.1.2.all fun (id, _) => id ∈ w.driver.1.1,
      .always "no fetch is reported twice" fun w =>
        (w.driver.1.2.map (·.1)).eraseDups.length == w.driver.1.2.length,
      .always "the caller knows how many calls are open" fun w =>
        w.state.state () ≥ w.driver.2.length,
      .sometimes "a fetch succeeds and another finds no service" fun w =>
        w.driver.1.2.any (·.2 == some 200) && w.driver.1.2.any (·.2 == none) ]

def tests : List (String × Bool) :=
  wireTests ++
  [ ("http client: a caller is right against everything a service may do, answers or not",
      check.ok && check.complete) ]

def live : Async (List (String × Bool)) := do
  let server ← serve (Server.system Tests.Gate.echo) Tests.Gate.bridge { port := 0 }
  let some tcpPort := server.port | return [("http client: the server reports its port", false)]
  let reported ← IO.mkRef #[]
  let all ← IO.Promise.new
  let rt ← Runtime.startWith caller { record := true } fun rt out => do
    Client.handler port { timeout_ms := 3000 } rt out
    if let .done id status := out then
      if (← reported.modifyGet fun r => ((r.push (id, status)).size, r.push (id, status))) == 4
      then all.resolve ()
  rt.input (.fetch 0 (target tcpPort))
  rt.input (.fetch 1 (target tcpPort ["bad"]))
  rt.input (.fetch 2 (target 1))
  rt.input (.fetch 3 { (target tcpPort) with host := "not an address" })
  await all
  rt.idle
  let events := (← rt.trace).toList
  rt.stop
  server.stop
  let statuses := (← reported.get).toList
  return [
    ("http client: a real call brings back the server's answer",
      statuses.lookup 0 == some (some 200) && statuses.lookup 1 == some (some 400)),
    ("http client: a closed port and a bad address are reported as no answer",
      statuses.lookup 2 == some none && statuses.lookup 3 == some none),
    ("http client: the real service does only what its model allows", world.allows events) ]

end Tests.HttpClient
