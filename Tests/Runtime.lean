/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-!
Tests of the runtime shell: run a system on a real task with recording on, then replay the
recorded events through `SysState.run`. `Kernel.run1_sound` proves the kernel's events are a run
of the semantics; these tests check that the shell passes them on and wires timers, inputs and
outputs correctly.
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

def worker (k : Fin 3) : sig.Actor (.worker k) Nat where
  init := 0
  step s
    | .job n =>
      if n % 7 == 0 then (s, [.send .collector (.done k n), .stop])
      else (s + 1, [.send .collector (.done k n)])
    | .tick => (s, [.send .collector (.ticked k)])
  recover s := (s, [.after 1 .tick])

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

def replay {σ : Signature} (sys : System σ) [Hashable σ.Id] (rt : Runtime sys) :
    BaseIO (Option (SysState sys)) := do
  let events ← rt.trace
  return (SysState.init sys Kernel.env).run Kernel.env events.toList

def flakyTest : Async (List (String × Bool)) := do
  let config : Runtime.Config := { record := true, inboxCapacity := 8 }
  let outputs ← IO.mkRef (#[] : Array Nat)
  let rt ← Runtime.start flaky config fun out => outputs.modify (·.push out)
  let clients := (List.finRange 3).toArray.map fun (k : Fin 3) => (do
    for n in [0:100] do
      rt.input (k, n * 3 + k.val + 1) : Async Unit)
  discard <| Async.concurrentlyAll clients
  rt.idle (timers := true)
  let events ← rt.trace
  let some c ← replay flaky rt | return [("flaky: the semantics accepts the trace", false)]
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
  let config : Runtime.Config := { record := true }
  let responses ← IO.mkRef 0
  let rt ← Runtime.start (bank (Fin 3) 100) config fun _ => responses.modify (· + 1)
  let clients := (List.finRange 3).toArray.map fun (k : Fin 3) => (do
    for n in [0:200] do
      rt.input (.transfer ⟨k.val * 1000 + n, k, k + 1, n % 7⟩) : Async Unit)
  discard <| Async.concurrentlyAll clients
  rt.idle
  let balances ← (List.finRange 3).mapM fun a => rt.state a
  let total := (balances.map (·.balance)).sum
  let replayed ← replay (bank (Fin 3) 100) rt
  return [
    ("bank on the runtime: money conserved once idle", total == 300),
    ("bank on the runtime: every request answered", (← responses.get) == 600),
    ("bank on the runtime: the semantics accepts the trace and agrees on balances",
      match replayed with
      | some c => (List.finRange 3).zip balances |>.all fun (a, s) => c.state a == s
      | none => false) ]

/-! A small inbox: actors that flood themselves and each other, behind an inbox of capacity 2. -/

inductive FloodMsg where
  | burst (n : Nat)
  | ping
  | pong
  | note
  deriving DecidableEq, Repr, Hashable

abbrev floodSig : Signature where
  Id := Fin 2
  Msg _ := FloodMsg
  In := Fin 2 × Nat

def flooder (self : Fin 2) : floodSig.Actor self (Nat × Nat) where
  init := (0, 0)
  step s
    | .burst n =>
      (s, (List.replicate n (.send self .note)) ++ (List.replicate n (.send (self + 1) .ping)))
    | .ping => (s, [.send (self + 1) .pong])
    | .pong => ((s.1, s.2 + 1), [])
    | .note => ((s.1 + 1, s.2), [])
  recover s := (s, [])

abbrev flood : System floodSig where
  State _ := Nat × Nat
  actor := flooder
  accept x := ⟨x.1, .burst x.2⟩

def floodTest : Async (List (String × Bool)) := do
  let config : Runtime.Config := { record := true, inboxCapacity := 2 }
  let rt ← Runtime.start flood config
  discard <| Async.concurrentlyAll #[rt.input (0, 200), rt.input (1, 200)]
  rt.idle
  let states ← (List.finRange 2).mapM fun k => rt.state k
  let replayed ← replay flood rt
  return [
    ("flood: self-sends and a cycle of sends all arrive",
      states == [(200, 200), (200, 200)]),
    ("flood: the semantics accepts the trace, with sends kept in order",
      match replayed with
      | some c => (List.finRange 2).zip states |>.all fun (k, s) => c.state k == s
      | none => false) ]

/-! Admission: `tryInput` either accepts an input or refuses it and leaves no trace of it. Whether
a given call finds the inbox full depends on timing, so the test checks what must hold either
way. -/

def busyTest : Async (List (String × Bool)) := do
  let config : Runtime.Config := { record := true, inboxCapacity := 1 }
  let rt ← Runtime.start flood config
  let accepted := (← (List.range 200).mapM fun _ => rt.tryInput (0, 1)).countP (·)
  rt.idle
  let inputs := (← rt.trace).toList.countP fun
    | .input _ => true
    | _ => false
  return [
    ("tryInput: every accepted input is handled and no refused one is",
      (← rt.state 0) == (accepted, accepted)),
    ("tryInput: the trace holds exactly the accepted inputs and still replays",
      inputs == accepted && (← replay flood rt).isSome) ]

def tests : IO (List (String × Bool)) := do
  let a ← flakyTest.block
  let b ← bankTest.block
  let c ← floodTest.block
  let d ← busyTest.block
  return a ++ b ++ c ++ d

end Tests.Runtime
