/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-!
Conformance tests of the concurrent runtime: run a system on real tasks with trace recording
on, then replay the recorded events through `SysState.run`. The semantics must accept the trace
and end in the state the runtime is in.
-/

namespace Tests.Runtime

open Lanes Std Std.Async

/-! A system that exercises stopping, lost mail, restarts and timers. -/

inductive Id where
  | worker (k : Fin 3)
  | collector
  deriving DecidableEq, Repr, Hashable

inductive WorkerMsg where
  | job (n : Nat)
  | tick
  deriving DecidableEq, Repr, Hashable

inductive CollectorMsg where
  | done (k : Fin 3) (n : Nat)
  | ticked (k : Fin 3)
  deriving DecidableEq, Repr, Hashable

abbrev Msg : Id → Type
  | .worker _ => WorkerMsg
  | .collector => CollectorMsg

instance : ∀ i, DecidableEq (Msg i)
  | .worker _ => inferInstanceAs (DecidableEq WorkerMsg)
  | .collector => inferInstanceAs (DecidableEq CollectorMsg)

abbrev sig : Signature where
  Id := Id
  Msg := Msg
  In := Fin 3 × Nat
  Out := Nat

/-- A worker forwards jobs to the collector, stops itself on every seventh job, and ticks once
shortly after each start. -/
def worker (k : Fin 3) : sig.Actor (.worker k) Nat where
  init := 0
  step s
    | .job n =>
      if n % 7 == 0 then (s, [.send .collector (.done k n), .stop])
      else (s + 1, [.send .collector (.done k n)])
    | .tick => (s, [.send .collector (.ticked k)])
  recover s := (s, [.after 1 .tick])

/-- The collector counts what it hears and reports every tenth job. -/
def collector : sig.Actor .collector (Nat × Nat) where
  init := (0, 0)
  step s
    | .done _ _ =>
      let jobs := s.1 + 1
      ((jobs, s.2), if jobs % 10 == 0 then [.emit jobs] else [])
    | .ticked _ => ((s.1, s.2 + 1), [])
  recover s := (s, [])

abbrev flaky : System sig where
  State
    | .worker _ => Nat
    | .collector => Nat × Nat
  actor
    | .worker k => worker k
    | .collector => collector
  accept x := ⟨.worker x.1, .job x.2⟩
  boot := [.collector]

/-- Whether the semantics accepts the recorded trace, and the state it leads to. -/
def replay {σ : Signature} (sys : System σ) [Hashable σ.Id] (rt : Runtime sys)
    (config : Runtime.Config σ) : BaseIO (Option (SysState sys)) := do
  let events ← rt.trace
  return (SysState.init sys config.env).run config.env events.toList

def flakyTest : Async (List (String × Bool)) := do
  let config : Runtime.Config sig := { record := true, mailboxCapacity := 8 }
  let outputs ← IO.mkRef (#[] : Array Nat)
  let rt ← Runtime.start flaky config fun out => outputs.modify (·.push out)
  -- Three clients send 100 jobs each, concurrently.
  let clients := (List.finRange 3).toArray.map fun (k : Fin 3) => (do
    for n in [0:100] do
      rt.input (k, n * 3 + k.val + 1) : Async Unit)
  discard <| Async.concurrentlyAll clients
  rt.idle
  Async.sleep 20
  rt.idle
  let events ← rt.trace
  let some c ← replay flaky rt config | return [("flaky: the semantics accepts the trace", false)]
  let collectorState ← rt.state .collector
  let workerStates ← (List.finRange 3).mapM fun k => rt.state (.worker k)
  let stops := events.toList.countP fun
    | .start _ => true
    | _ => false
  return [
    ("flaky: the semantics accepts the trace", true),
    ("flaky: replayed collector state equals the runtime's",
      c.state .collector == collectorState),
    ("flaky: replayed worker states equal the runtime's",
      (List.finRange 3).zip workerStates |>.all fun (k, s) => c.state (.worker k) == s),
    ("flaky: workers stopped and restarted", stops > 3),
    ("flaky: timers fired", collectorState.2 > 0),
    ("flaky: outputs reached the handler", (← outputs.get).size == collectorState.1 / 10) ]

/-! The bank under concurrent clients. -/

open Examples.Bank in
def bankTest : Async (List (String × Bool)) := do
  let config : Runtime.Config (Examples.Bank.sig (Fin 3)) := { record := true }
  let responses ← IO.mkRef 0
  let rt ← Runtime.start (bank (Fin 3) 100) config fun _ => responses.modify (· + 1)
  let clients := (List.finRange 3).toArray.map fun (k : Fin 3) => (do
    for n in [0:200] do
      rt.input (.transfer ⟨k.val * 1000 + n, k, k + 1, n % 7⟩) : Async Unit)
  discard <| Async.concurrentlyAll clients
  rt.idle
  let balances ← (List.finRange 3).mapM fun a => rt.state a
  let total := (balances.map (·.balance)).sum
  let replayed ← replay (bank (Fin 3) 100) rt config
  return [
    ("bank on the runtime: money conserved once idle", total == 300),
    ("bank on the runtime: every request answered", (← responses.get) == 600),
    ("bank on the runtime: the semantics accepts the trace and agrees on balances",
      match replayed with
      | some c => (List.finRange 3).zip balances |>.all fun (a, s) => c.state a == s
      | none => false) ]

def tests : IO (List (String × Bool)) := do
  let a ← flakyTest.block
  let b ← bankTest.block
  return a ++ b

end Tests.Runtime
