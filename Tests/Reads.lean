/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Web
import Tests.Fixtures.BankWeb

/-!
Reads answered from the state (`Http.View`): the runtime's peeks; the bank's balances and their
total read from the accounts' states, through `Loopback` and over a socket; and a read's
deadline and bound.
-/

namespace Tests.Reads

open Lanes Lanes.Http Std Std.Async Tests.Fixtures.Bank Tests.Fixtures.BankWeb
open Tests.Web (fetch)

abbrev bankSys := bank Acct 100

def total : Route Unit := .get (.seg "total")

/-- A balance, as the bridge answers a `balance` that enters the system. -/
def balanceView (a : Acct) : View bankSys where
  reads := [a]
  answer get _ := Response.html (OutcomeView (.balance (get a List.mem_cons_self).balance)).render

/-- The total of every account. On the runtime each account is read between its own steps, so
beside transfers in flight the total may miss what is on its way (`docs/decisions/D116-free-running.md`). -/
def totalView : View bankSys where
  reads := List.finRange 3
  answer get _ := .text s!"{((List.finRange 3).attach.map fun ⟨a, h⟩ => (get a h).balance).sum}"

/-- The balances and the total are reads; the routes are the bridge's. -/
def view (r : Request) : Option (View bankSys) :=
  (dispatch [Routes.account.handle fun n _ => (toAcct n).map balanceView,
    total.handle fun () _ => some totalView] r).join

/-- A balance read from the state is what the query that enters the system answers from the same
state, which the query leaves as it was. -/
theorem balanceView_answers (id : Http.ReqId) (a : Acct) (s : Account) :
    (bankSys.actor a).step s (.query id) = (s, [.emit ⟨id, .balance s.balance⟩])
      ∧ bridge.encode ⟨id, .balance s.balance⟩ = some (id, (balanceView a).answer (fun _ _ => s) []) :=
  ⟨rfl, rfl⟩

/-! The runtime's peeks. -/

def transfer (req src dst amount : Nat) : Tests.Fixtures.Bank.Request Acct :=
  .transfer { req, src := Fin.ofNat 3 src, dst := Fin.ofNat 3 dst, amount }

/-- What a peek read: each actor's balance, then those of the others it asked for. -/
def balances {ids : List Acct} (p : Peek bankSys ids) : List (Nat × Int) × List (Nat × Int) :=
  (p.states.map fun e => (e.1.val, e.2.balance),
    (p.others.map fun e => (e.1.val, e.2.balance)).mergeSort (·.1 ≤ ·.1))

def peekTest : Async (List (String × Bool)) := do
  let rt ← Runtime.start bankSys
  rt.input (transfer 0 0 1 30)
  rt.input (transfer 1 1 2 50)
  rt.idle
  let named ← IO.Promise.new
  let asked ← rt.tryPeek (List.finRange 3) fun p => named.resolve (p.map balances)
  let others ← IO.Promise.new
  let askedEvery ← rt.tryPeek [] (every := fun a => a != 2) fun p => others.resolve (p.map balances)
  let named ← await named.result?
  let others ← await others.result?
  rt.stop
  let refused := !(← rt.tryPeek [] fun _ => pure ())
  return [
    ("reads: a peek reads each actor it names between its steps, here after every transfer",
      asked && named == some (some ([(0, 70), (1, 80), (2, 150)], []))),
    ("reads: a peek of every actor started reads each once",
      askedEvery && others == some (some ([], [(0, 70), (1, 80)]))),
    ("reads: a runtime that has stopped is asked nothing", refused) ]

/-! Through `Loopback`. -/

def status (r : Except String Http.Response) : Nat :=
  match r with
  | .ok r => r.status
  | .error _ => 0

def text (r : Except String Http.Response) : String :=
  match r with
  | .ok r => (String.fromUTF8? r.body).getD ""
  | .error _ => ""

def loopbackTests : List (String × Bool) :=
  let lb := Loopback.start bankSys bridge (view := view)
  let (lb, before) := lb.get ["accounts", "1"]
  let (lb, moved) := lb.post ["transfer"] [("src", "0"), ("dst", "1"), ("amount", "30")]
  let (lb, after) := lb.get ["accounts", "1"]
  let (lb, sum) := lb.get ["total"]
  let (lb, missing) := lb.get ["accounts", "7"]
  [ ("reads: through the loopback a balance is read from the state, and sees a transfer before it",
      status before == 200 && text before == "<span>100</span>" && status moved == 200
        && text after == "<span>130</span>"),
    ("reads: the total of every account is read at one boundary; the bridge has no such route",
      text sum == "300" && status missing == 404),
    ("reads: no read is left waiting", lb.reads.isEmpty && lb.peeks.isEmpty && lb.pending.isEmpty) ]

/-! Over a socket. -/

def body (response : String) : String :=
  ((response.splitOn "\r\n\r\n").drop 1).headD ""

def socketTest : Async (List (String × Bool)) := do
  let server ← serve bankSys bridge { port := 0 } { record := true } (view := view)
  let some port := server.port | return [("reads: the server reports its port", false)]
  let before ← fetch port "/accounts/0"
  let moved ← fetch port "/transfer" (method := "POST") (body := "src=0&dst=1&amount=30")
  let after ← fetch port "/accounts/0"
  let mixed ← Async.concurrentlyAll ((List.range 40).toArray.map fun n =>
    if n % 4 == 0 then fetch port "/transfer" (method := "POST") (body := s!"src={n % 3}&dst={(n + 1) % 3}&amount=1")
    else fetch port "/total")
  let totals := (mixed.toList.zipIdx.filter (·.2 % 4 != 0)).map (body ·.1)
  server.stop
  let inputs := (← server.trace).toList.countP (· matches .input _)
  return [
    ("reads: over a socket a balance is read from the state, and the account that answered a "
        ++ "transfer has it",
      body before == "<span>100</span>" && moved.startsWith "HTTP/1.1 200"
        && body after == "<span>70</span>"),
    ("reads: a total read beside concurrent transfers misses at most the transfers in flight",
      totals.length == 30 && totals.all fun t => t.toNat?.any fun n => 290 ≤ n && n ≤ 300),
    ("reads: only the transfers enter the system", inputs == 11) ]

/-! A read's deadline and bound, beside a shard held up by its output handler. -/

inductive Ask where
  | add (id : Http.ReqId)
  | stall (id : Http.ReqId)
  deriving DecidableEq, Repr, Hashable

inductive Told where
  | done (id : Http.ReqId) (count : Nat)
  | stalled
  deriving DecidableEq, Repr, Hashable

def counter : Service Ask Told Nat where
  init := 0
  step n
    | .add id => (n + 1, [.done id (n + 1)])
    | .stall id => (n, [.stalled, .done id n])

abbrev counterSys := Server.system counter

def counterBridge : Bridge (Server.sig Ask Told) where
  decode id r := if r.path == ["stall"] then .ok (.stall id) else .ok (.add id)
  encode
    | .done id n => some (id, .text s!"{n}")
    | .stalled => none

def countView (r : Request) : Option (View counterSys) :=
  if r.path == ["count"] then some { reads := [()], answer := fun get _ => .text s!"{get () List.mem_cons_self}" }
  else none

def deadlineTest : Async (List (String × Bool)) := do
  let onOutput : Told → Async Unit
    | .stalled => IO.sleep 400
    | _ => pure ()
  let server ← serveFronted counterSys counterBridge
    { port := 0, reads := { requestTimeout_ms := 50 } } {} onOutput (view := countView)
  let some port := server.port | return [("reads: the server reports its port", false)]
  let added ← fetch port "/add" (method := "POST")
  let stall ← async (fetch port "/stall" (method := "POST"))
  Async.sleep 60
  let late ← fetch port "/count"
  let stalled ← await stall
  let read ← fetch port "/count"
  let left ← server.inFlight
  server.stop
  let full ← serveFronted counterSys counterBridge { port := 0, reads := { maxPending := 0 } }
    (view := countView)
  let some port := full.port | return [("reads: the server reports its port", false)]
  let refused ← fetch port "/count"
  let written ← fetch port "/add" (method := "POST")
  full.stop
  return [
    ("reads: a read the shard cannot answer by its deadline gets 504, and the shard goes on",
      body added == "1" && late.startsWith "HTTP/1.1 504" && body stalled == "1"
        && body read == "1" && left == 0),
    ("reads: beyond its bound a read gets 503, and requests still enter",
      refused.startsWith "HTTP/1.1 503" && body written == "1") ]

def live : Async (List (String × Bool)) := do
  return (← peekTest) ++ (← socketTest) ++ (← deadlineTest)

def tests : List (String × Bool) := loopbackTests

end Tests.Reads
