/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Web
import Tests.Ops
import Tests.Fixtures.BankWeb

/-!
Reads answered from the state (`docs/decisions/new-reads.md`), on the bank behind its web page:
a balance page is answered from the account's state and never enters the system. The same
requests with reads on and off get the same answers, and with reads on the journal holds the
transfers alone; each read after a transfer's response sees it; and a shard on a journal file
that answered reads starts again in the state it had.
-/

namespace Tests.Reads

open Lanes Lanes.Http Std Std.Async Tests.Fixtures.Bank Tests.Fixtures.BankWeb

abbrev bankSys := bank Acct 100

def balancePage (s : Account) : Http.Response :=
  .html (OutcomeView (.balance s.balance)).render

/-- A balance page reads its account. An account that does not exist is no read: it enters, and
the bridge answers `404`. -/
def reads (request : Http.Request) : Option (Read bankSys) :=
  (Routes.account.handle (fun n _ => toAcct n) request).join.map fun account =>
    { actor := account, answer := balancePage }

/-- The read answers what the journalled request would: the account's `query` changes nothing
and emits its balance, which the bridge writes as the read's response. -/
theorem read_agrees (self : Acct) (s : Account) (req : Http.ReqId) :
    (account 100 self).step s (.query req) = (s, [.emit ⟨req, .balance s.balance⟩])
      ∧ bridge.encode ⟨req, .balance s.balance⟩ = some (req, balancePage s) :=
  ⟨rfl, rfl⟩

def post (port : UInt16) (body : String) : Async String :=
  Tests.Web.fetch port "/transfer" (method := "POST") (body := body)

def bodyOf (response : String) : String :=
  match response.splitOn "\r\n\r\n" with
  | _ :: body :: _ => body
  | _ => ""

/-- The same requests with reads on and off: the answers, and the inputs the journal holds. -/
def run (on : Bool) : Async (List String × List (Http.ReqId × Http.Request)) := do
  let (log, written) ← Tests.Ops.memory (served bankSys bridge {}) []
  let server ← serveWith bankSys bridge { port := 0 } {} (some log)
    (reads := if on then reads else fun _ => none)
  let port := server.port.getD 0
  let mut answers := #[]
  answers := answers.push (← Tests.Web.fetch port "/accounts/0")
  answers := answers.push (← post port "src=0&dst=1&amount=10")
  answers := answers.push (← Tests.Web.fetch port "/accounts/0")
  answers := answers.push (← Tests.Web.fetch port "/accounts/7")
  answers := answers.push (← Tests.Web.fetch port "/")
  server.stop
  let inputs := (← written.get).toList.filterMap fun
    | .input x => some x
    | _ => none
  return (answers.toList.map bodyOf, inputs)

def sameTest : Async (List (String × Bool)) := do
  let (off, offInputs) ← run false
  let (on, onInputs) ← run true
  let paths := onInputs.map fun (_, r) => r.path
  return [
    ("reads: a balance read from the state answers as the journalled request does",
      off == on && on[0]? == some "<span>100</span>" && on[2]? == some "<span>90</span>"),
    ("reads: with reads off every request is journalled", offInputs.length == 5),
    ("reads: with reads on the journal holds the requests that are no read, and no read",
      onInputs.length == 3 && paths == [["transfer"], ["accounts", "7"], []]) ]

/-- Each transfer's response is followed at once by a read of its source, over the same and
over a fresh connection: every read shows the debit. -/
def afterTest : Async (List (String × Bool)) := do
  let server ← serve bankSys bridge { port := 0 } (reads := reads)
  let port := server.port.getD 0
  let mut seen := #[]
  for n in [1:21] do
    discard <| post port "src=0&dst=2&amount=1"
    seen := seen.push (bodyOf (← Tests.Web.fetch port "/accounts/0") == s!"<span>{100 - n}</span>")
  let many ← Async.concurrentlyAll ((List.range 40).toArray.map fun _ =>
    Tests.Web.fetch port "/accounts/0")
  server.stop
  return [
    ("reads: a read after a transfer's response sees the transfer", seen.all id),
    ("reads: concurrent reads are each answered once, with the same state",
      many.all fun r => r.startsWith "HTTP/1.1 200" && bodyOf r == "<span>80</span>") ]

/-- On a journal file with snapshots: reads between writes, a restart, and the state is the one
the writes left. -/
def durableTest : Async (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let journal : System.FilePath := s!"{dir}/lanes-reads-{← IO.monoNanosNow}.journal"
  let saving : Saving bankSys := { actors := actors Codec.fin 100, out := Tests.Fixtures.Bank.Response.codec }
  let start := serve bankSys bridge { port := 0, journal, system := "reads test" }
    { snapshotEvery := 3 } (saving := some saving) (reads := reads)
  let server ← start
  let port := server.port.getD 0
  for _ in [0:4] do
    discard <| post port "src=1&dst=0&amount=5"
    for _ in [0:5] do discard <| Tests.Web.fetch port "/accounts/1"
  let before ← Tests.Web.fetch port "/accounts/1"
  server.stop
  let server ← start
  let after ← Tests.Web.fetch (server.port.getD 0) "/accounts/1"
  let zero ← Tests.Web.fetch (server.port.getD 0) "/accounts/0"
  server.stop
  for file in [journal, journal.addExtension "lock", journal.addExtension "snapshot"] do
    if ← file.pathExists then IO.FS.removeFile file
  return [
    ("reads: a shard that answered reads starts again in the state its writes left",
      bodyOf before == "<span>80</span>" && bodyOf after == "<span>80</span>"
        && bodyOf zero == "<span>120</span>") ]

def live : Async (List (String × Bool)) := do
  return (← sameTest) ++ (← afterTest) ++ (← durableTest)

end Tests.Reads
