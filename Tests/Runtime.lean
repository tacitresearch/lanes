/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Fixtures.Bank

/-!
Tests of the runtime shell: run a system on a real thread with recording on, then replay the
recorded events through `SysState.run`. `Kernel.exec_reachable` proves the kernel's events are a
run of the semantics; these tests check that the shell passes them on and wires inputs, the
clock, outputs and stopping correctly.
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

instance : ∀ i, DecidableEq (Msg i) := by instance_by_cases

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
  let some c ← replay flaky rt
    | rt.stop; return [("flaky: the semantics accepts the trace", false)]
  let collectorState ← rt.state .collector
  let workerStates ← (List.finRange 3).mapM fun k => rt.state (.worker k)
  let stops := events.toList.countP fun
    | .start _ => true
    | _ => false
  let results := [
    ("flaky: the semantics accepts the trace", true),
    ("flaky: replayed collector state equals the runtime's",
      c.state .collector == collectorState),
    ("flaky: replayed worker states equal the runtime's",
      (List.finRange 3).zip workerStates |>.all fun (k, s) => c.state (.worker k) == s),
    ("flaky: workers stopped and restarted", stops > 3),
    ("flaky: timers fired", collectorState.2 > 0),
    ("flaky: outputs reached the handler", (← outputs.get).size == collectorState.1 / 10) ]
  rt.stop
  return results

/-! The bank under concurrent clients. -/

open Tests.Fixtures.Bank in
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
  let results := [
    ("bank on the runtime: money conserved once idle", total == 300),
    ("bank on the runtime: every request answered", (← responses.get) == 600),
    ("bank on the runtime: the semantics accepts the trace and agrees on balances",
      match replayed with
      | some c => (List.finRange 3).zip balances |>.all fun (a, s) => c.state a == s
      | none => false) ]
  rt.stop
  return results

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
  let results := [
    ("flood: self-sends and a cycle of sends all arrive",
      states == [(200, 200), (200, 200)]),
    ("flood: the semantics accepts the trace, with sends kept in order",
      match replayed with
      | some c => (List.finRange 2).zip states |>.all fun (k, s) => c.state k == s
      | none => false) ]
  rt.stop
  return results

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
  let results := [
    ("tryInput: every accepted input is handled and no refused one is",
      (← rt.state 0) == (accepted, accepted)),
    ("tryInput: the trace holds exactly the accepted inputs and still replays",
      inputs == accepted && (← replay flood rt).isSome) ]
  rt.stop
  return results

/-! Timers, back-pressure and stopping, with nothing left to timing but lower bounds. -/

inductive ClockMsg where
  | echo (n : Nat)
  | arm (delay_ms : Nat)
  | disarm
  | tick
  deriving DecidableEq, Repr, Hashable

abbrev clockSig : Signature where
  Id := Unit
  Msg _ := ClockMsg
  In := ClockMsg
  Out := Nat

def tickOutput : Nat := 1000

/-- The state counts the ticks. -/
def clock : clockSig.Actor () Nat where
  init := 0
  step s
    | .echo n => (s, [.emit n])
    | .arm delay_ms => (s, [.after delay_ms .tick])
    | .disarm => (s, [.cancel .tick])
    | .tick => (s + 1, [.emit tickOutput])
  recover s := (s, [])

abbrev clockSystem : System clockSig where
  State _ := Nat
  actor _ := clock
  accept x := ⟨(), x⟩

def throws {α : Type} (action : Async α) : Async Bool := do
  try discard action; return false
  catch _ => return true

def timerTest : Async (List (String × Bool)) := do
  let rt ← Runtime.start clockSystem
  let t0 ← IO.monoMsNow
  rt.input (.arm 60)
  rt.idle (timers := true)
  let fired ← IO.monoMsNow
  rt.input (.arm 5000)
  rt.input .disarm
  rt.idle (timers := true)
  let cancelled ← IO.monoMsNow
  let afterCancel ← rt.state ()
  let t1 ← IO.monoMsNow
  rt.input (.arm 5000)
  rt.input (.arm 90)
  rt.idle (timers := true)
  let rearmed ← IO.monoMsNow
  let results := [
    ("timer: it fires no earlier than asked", fired - t0 ≥ 60 && afterCancel == 1),
    ("timer: a cancelled timer is not waited for and never fires",
      cancelled - fired < 2500 && afterCancel == 1),
    ("timer: arming again replaces the pending timer",
      rearmed - t1 ≥ 90 && rearmed - t1 < 2500 && (← rt.state ()) == 2) ]
  rt.stop
  return results

/-- The shard is held inside the output handler, so what the inbox does is not a matter of
timing: it takes `inboxCapacity` inputs and refuses the next. -/
def backPressureTest : Async (List (String × Bool)) := do
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let outputs ← IO.mkRef #[]
  let rt ← Runtime.start clockSystem { inboxCapacity := 2 } fun out => do
    outputs.modify (·.push out)
    if out == 0 then
      entered.resolve ()
      await release
  rt.input (.echo 0)
  await entered
  let offered ← [1, 2, 3].mapM fun n => rt.tryInput (.echo n)
  release.resolve ()
  rt.idle
  let results := [
    ("back-pressure: a full inbox refuses, and what it accepted is handled",
      offered == [true, true, false] && (← outputs.get) == #[0, 1, 2]) ]
  rt.stop
  return results

def stopTest : Async (List (String × Bool)) := do
  let rt ← Runtime.start clockSystem
  rt.input (.arm 60000)
  rt.input (.echo 1)
  let waiter ← IO.Promise.new
  background do waiter.resolve (← throws (rt.idle (timers := true)))
  rt.idle
  rt.stop
  let waiterThrew ← await waiter
  return [
    ("stop: a caller waiting for timers is told the runtime stopped", waiterThrew),
    ("stop: input, idle and state fail instead of hanging",
      (← throws (rt.input (.echo 2))) && (← throws rt.idle) && (← throws (rt.state ()))),
    ("stop: tryInput refuses", !(← rt.tryInput (.echo 3))) ]

def batchTest : Async (List (String × Bool)) := do
  let rt ← Runtime.start clockSystem { batch := 0 }
  rt.input (.arm 1)
  rt.idle (timers := true)
  let results := [("batch: a batch of zero still makes progress", (← rt.state ()) == 1)]
  rt.stop
  return results

/-! The one thing the shell is trusted for: handing outputs on, all of them, in order. -/

abbrev burstSig : Signature where
  Id := Unit
  Msg _ := Nat
  In := Nat
  Out := Nat

abbrev burst : System burstSig where
  State _ := Unit
  actor _ := { init := (), step := fun _ n => ((), [.emit n, .emit (n + 1), .emit (n + 2)]),
               recover := fun _ => ((), [.emit 99]) }
  accept x := ⟨(), x⟩
  boot := [()]

def outputsTest : Async (List (String × Bool)) := do
  let outputs ← IO.mkRef #[]
  let rt ← Runtime.start burst {} fun out => outputs.modify (·.push out)
  rt.input 10
  rt.input 20
  rt.idle
  rt.stop
  return [("outputs: every output is handed over once, in order, boot's included",
    (← outputs.get) == #[99, 10, 11, 12, 20, 21, 22])]

/-! A shard that always has work must still stop. -/

abbrev pingSig : Signature where
  Id := Bool
  Msg _ := Unit
  In := Unit

abbrev ping : System pingSig where
  State _ := Nat
  actor self := { init := 0, step := fun s _ => (s + 1, [.send (!self) ()]),
                  recover := fun s => (s, []) }
  accept _ := ⟨true, ()⟩

def busyStopTest : Async (List (String × Bool)) := do
  let rt ← Runtime.start ping
  rt.input ()
  Async.sleep 20
  rt.stop
  return [("stop: a shard that never runs out of work still ends",
    (← throws (rt.input ())) && !(← rt.tryInput ()))]

def soon {α : Type} (ms : Nat) (action : Async α) : Async (Option α) :=
  Async.race (some <$> action) (do Async.sleep (.ofNat ms); return none)

/-- Commands handed over before `stop` are finished by it, an inbox configured with no room
still takes one input at a time, and a handler that throws does not end the shard. -/
def dutiesTest : Async (List (String × Bool)) := do
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let outputs ← IO.mkRef #[]
  let rt ← Runtime.start clockSystem {} fun out => do
    outputs.modify (·.push out)
    if out == 0 then
      entered.resolve ()
      await release
  rt.input (.echo 0)
  await entered
  for n in [1:6] do discard <| rt.tryInput (.echo n)
  let stopped ← IO.Promise.new
  background do
    rt.stop
    stopped.resolve ()
  Async.sleep 20
  release.resolve ()
  let ended ← soon 2000 (await stopped.result?)
  let narrow ← Runtime.start clockSystem { inboxCapacity := 0 }
  let taken ← soon 2000 (narrow.input (.echo 1))
  narrow.stop
  let seen ← IO.mkRef #[]
  let throwing ← Runtime.start clockSystem {} fun out => do
    if out == 2 then throw (IO.userError "this handler fails on 2")
    seen.modify (·.push out)
  let alive ← soon 2000 do
    try
      for n in [1:4] do throwing.input (.echo n)
      throwing.idle
      pure true
    catch _ => pure false
  throwing.stop
  return [
    ("stop: commands handed over before it are finished", ended.isSome
      && (← outputs.get) == #[0, 1, 2, 3, 4, 5]),
    ("inbox: a capacity of zero still takes an input", taken.isSome),
    ("outputs: a handler that throws does not end the shard, and is not called again for that "
      ++ "output", alive == some true && (← seen.get) == #[1, 3]) ]

/-- A shard started on a journal goes on from the journal's clock, so a timer armed after the
restart is due after its delay, not after the uptime of the run before. And a shard whose
journal has failed takes nothing more, also while the journal is still being closed. -/
def afterRestartTest : Async (List (String × Bool)) := do
  let ticked ← IO.Promise.new
  let log : Journal.Log clockSystem := {
    past := [.advance 3600000, .batch 1]
    append := fun _ => pure (), note := fun _ => pure (), close := pure () }
  let rt ← Runtime.start clockSystem {} (journal := some log) fun out => do
    if out == tickOutput then ticked.resolve ()
  rt.input (.arm 30)
  let fired ← soon 2000 (await ticked.result?)
  rt.stop
  let failed ← IO.Promise.new
  let failing : Journal.Log clockSystem := {
    past := []
    append := fun _ => do failed.resolve (); throw (IO.userError "no room on the device")
    note := fun _ => pure ()
    close := IO.sleep 400 }
  let dying ← Runtime.start clockSystem {} (journal := some failing)
  discard <| dying.tryInput (.echo 1)
  discard <| await failed.result?
  Async.sleep 100
  let accepted ← dying.tryInput (.echo 2)
  discard <| soon 2000 dying.ended
  return [
    ("timers: one armed after a restart on a journal is due after its own delay", fired.isSome),
    ("durable: a shard whose journal has failed takes nothing more while it ends", !accepted) ]

/-- A parker: an `unpark` before the `park` is kept, a timed park ends, a task and an `Async`
are waited for on one. -/
def parkerTest : IO (List (String × Bool)) := do
  let p ← Parker.new
  p.unpark
  let t0 ← IO.monoMsNow
  p.park
  let kept := (← IO.monoMsNow) - t0 < 1000
  let t1 ← IO.monoMsNow
  p.parkAtMost 50
  let timed := (← IO.monoMsNow) - t1
  let later ← IO.asTask (do IO.sleep 30; return 7)
  let waited ← Parker.wait later
  let blocked ← Lanes.block (do Async.sleep 20; return 8 : Async Nat)
  let failed ← (Lanes.block (throw (IO.userError "no") : Async Nat)).toBaseIO
  return [
    ("parker: an unpark before the park is kept", kept),
    ("parker: a park of at most 50 ms ends, and not long before", 40 ≤ timed && timed < 2000),
    ("parker: a task is waited for on a parker", waited matches .ok 7),
    ("parker: an Async is blocked on with a parker, its error thrown",
      blocked == 8 && failed matches .error _) ]

def tests : IO (List (String × Bool)) := do
  let a ← flakyTest.block
  let b ← bankTest.block
  let c ← floodTest.block
  let d ← busyTest.block
  let e ← timerTest.block
  let f ← backPressureTest.block
  let g ← stopTest.block
  let h ← batchTest.block
  let i ← outputsTest.block
  let j ← busyStopTest.block
  return a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i ++ j ++ (← dutiesTest.block)
    ++ (← afterRestartTest.block) ++ (← parkerTest)

end Tests.Runtime
