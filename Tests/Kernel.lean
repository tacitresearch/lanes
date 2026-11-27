/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Model checks of what `Lanes.Runtime.KernelTimers` proves about the kernel's timer agenda (rule
5.1): every sequence of operations a shell can perform, up to a bound, on two actors that arm,
arm again, cancel and stop, one of them in a timer's handler. The shell here is hostile: it fires
any timer the agenda names at either actor, for either message.

A timer that is due and a message that is queued take turns. The two exceptions the fairness
theorems name are shown to be real, and so is the starvation the turns prevent.
-/

namespace Tests.Kernel

open Lanes Lanes.Check

inductive Msg where
  | arm (alarm : Bool) (delay_ms : Nat)
  | disarm (alarm : Bool)
  | halt
  | ring (alarm : Bool)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Bool
  Msg _ := Msg
  In := Bool × Msg

abbrev alarms : System sig where
  State _ := Unit
  actor _ := {
    init := ()
    step := fun _ msg => ((), match msg with
      | .arm alarm delay_ms => [.after delay_ms (.ring alarm)]
      | .disarm alarm => [.cancel (.ring alarm)]
      | .halt => [.stop]
      | .ring alarm => if alarm then [] else [.stop])
    recover := fun _ => ((), [.after 1 (.ring false)]) }
  accept x := ⟨x.1, x.2⟩
  boot := [false]

abbrev Shard := Kernel alarms

def ids : List Bool := [false, true]

def pending (k : Shard) : List (Bool × Msg × Kernel.Due) :=
  ids.flatMap fun i => (k.cell i).timers.map fun (msg, due) => (i, msg, due)

def scheduled (k : Shard) : List (Bool × Msg × Kernel.Due) :=
  k.agenda.toList.map fun (due, ⟨i, msg⟩) => (i, msg, due)

def view (k : Shard) :=
  ((pending k).map fun (i, msg, due) => (i, msg, due.deadline_ms, due.token),
    (scheduled k).map fun (i, msg, due) => (i, msg, due.deadline_ms, due.token),
    ids.map fun i => (k.cell i).up,
    k.queue.toList.map fun e => (e.src, e.dst, (e.msg : Msg)),
    k.nextToken, k.clock_ms, k.timerTurn)

instance : BEq Shard := ⟨fun a b => view a == view b⟩
instance : Hashable Shard := ⟨fun k => hash (view k)⟩

def ops (k : Shard) : List (Kernel.Op sig) :=
  let inputs := ids.flatMap fun i =>
    [.arm false 0, .arm false 2, .arm true 1, .disarm false, .halt].map fun msg =>
      Kernel.Op.input (i, msg)
  let fires := (scheduled k).flatMap fun (_, _, due) =>
    ids.flatMap fun i => [true, false].map fun alarm =>
      Kernel.Op.fire (σ := sig) i (Msg.ring alarm) due
  inputs ++ [.advance (k.clock_ms + 1), .advance (k.clock_ms + 2), .step, .batch 2] ++ fires

def shell : Model Shard (Kernel.Op sig) where
  init := [(Kernel.boot alarms).1]
  next k := (ops k).map fun op => (op, (k.apply op).kernel)

def firesTimer (k : Shard) : Bool :=
  match k.step.events with
  | .timeout _ _ :: _ => true
  | _ => false

def isDue (k : Shard) (t : Bool × Msg × Kernel.Due) : Bool :=
  t.2.2.deadline_ms ≤ k.clock_ms

def serves (k : Shard) (e : Envelope sig) : Bool :=
  match k.step.events with
  | .deliver e' :: _ => e' == e
  | .start i :: _ => i == e.dst
  | _ => false

def firesBy (k : Shard) (due : Kernel.Due) : Bool :=
  match k.step.events with
  | .timeout i msg :: _ =>
    (k.cell i).timers.any fun (m, first) => m == msg && first.deadline_ms ≤ due.deadline_ms
  | _ => false

def stopsByTimer (k : Shard) (i : Bool) : Bool :=
  match k.step.events with
  | .timeout j _ :: _ => i == j && !(k.step.kernel.cell i).up
  | _ => false

def oldest (k : Shard) (p : Envelope sig → Bool) : Bool :=
  k.queue.toList.head?.all p

def due (k : Shard) (p : Bool × Msg × Kernel.Due → Bool) : Bool :=
  (pending k).all fun t => !isDue k t || p t

def properties : List (Property Shard) :=
  [ .always "every pending timer is on the agenda" fun k =>
      (pending k).all (scheduled k).contains,
    .always "every agenda entry is a pending timer" fun k =>
      (scheduled k).all (pending k).contains,
    .always "tokens on the agenda are older than the next one" fun k =>
      (scheduled k).all fun (_, _, due) => due.token < k.nextToken,
    .always "an actor has at most one timer for a message" fun k =>
      ids.all fun i => ((k.cell i).timers.map (·.1)).eraseDups.length == (k.cell i).timers.length,
    .always "an actor that is down has no timers" fun k =>
      ids.all fun i => (k.cell i).up || (k.cell i).timers.isEmpty,
    .always "no lost timer: when one is due the shell does not sleep" fun k =>
      !(pending k).any (isDue k) || k.wait == .none,
    .always "messages are not starved" fun k =>
      oldest k fun e => serves k e || serves k.step.kernel e || stopsByTimer k e.dst,
    .always "timers are not starved" fun k =>
      due k fun t => firesBy k t.2.2 || firesBy k.step.kernel t.2.2
        || !(pending k.step.kernel).contains t,
    .always "no spin: when the shell does not sleep, a step does something" fun k =>
      k.wait != .none || !k.step.events.isEmpty,
    .always "idle means no queued message and no pending timer" fun k =>
      k.quiet true == (k.queue.toList.isEmpty && (pending k).isEmpty),
    .always "the shell sleeps until the earliest deadline" fun k =>
      match k.wait with
      | .for_ms ms =>
        ((pending k).all fun (_, _, due) => k.clock_ms + ms ≤ due.deadline_ms)
          && (pending k).any fun (_, _, due) => due.deadline_ms == k.clock_ms + ms
      | _ => true,
    .sometimes "a timer is due" fun k => (pending k).any (isDue k),
    .sometimes "a timer and a message are both ready" fun k =>
      (pending k).any (isDue k) && !k.queue.isEmpty,
    .sometimes "a message waits for one timer" fun k =>
      !oldest k fun e => serves k e || !serves k.step.kernel e,
    .sometimes "a timer waits for one message" fun k =>
      !due k fun t => firesBy k t.2.2 || !firesBy k.step.kernel t.2.2,
    .sometimes "the timer that goes first stops the receiver of the oldest message" fun k =>
      !oldest k fun e => serves k e || serves k.step.kernel e,
    .sometimes "the message that goes first disarms a timer that is due" fun k =>
      !due k fun t => firesBy k t.2.2 || firesBy k.step.kernel t.2.2,
    .sometimes "one actor has two timers" fun k => ids.any fun i => (k.cell i).timers.length == 2,
    .sometimes "both actors have a timer" fun k => ids.all fun i => !(k.cell i).timers.isEmpty,
    .sometimes "the booted actor has stopped and the other has a timer" fun k =>
      !(k.cell false).up && !(k.cell true).timers.isEmpty,
    .sometimes "the shell sleeps" fun k => k.wait matches .for_ms _,
    .sometimes "idle after a timer was armed" fun k => k.quiet true && k.nextToken > 0 ]

/-- Actor `false` armed a timer when it booted, and the shell fires that timer's `due` at actor
`true`. The kernel must not forget whose timer that `due` is. -/
def misfire : List (Kernel.Op sig) :=
  [.fire true (.ring false) ⟨1, 0⟩, .advance 1]

inductive Beat where
  | tick
  | work
  deriving DecidableEq, Repr

abbrev beatSig : Signature where
  Id := Bool
  Msg _ := Beat
  In := Unit

/-- Actor `false` has a timer that is always due: its handler arms it again at once. Actor
`true` counts the messages it has handled. -/
abbrev busy : System beatSig where
  State _ := Nat
  actor i := {
    init := 0
    step := fun n msg => match msg with
      | .tick => (n, [.after 0 .tick])
      | .work => (n + 1, [])
    recover := fun n => (n, if i then [] else [.after 0 .tick]) }
  accept _ := ⟨true, .work⟩
  boot := [false, true]

def worked (k : Kernel busy) : Nat :=
  (k.cell true).state

def ticks (events : List (Event beatSig)) : Nat :=
  events.countP (· matches .timeout ..)

/-! Waves: three counters that are up, with mail for each, and one stopping on its second
message, which drops the mail still queued for it. The steps of a wave are worked out ahead for
every actor with mail, and the batch is `runBatch`'s (`Kernel.runWaves_eq` proves it; this shows
the plan is used). -/

abbrev countSig : Signature where
  Id := Fin 3
  Msg _ := Nat
  In := Fin 3 × Nat
  Out := Nat

abbrev counters : System countSig where
  State _ := Nat
  actor i := {
    init := 0
    step := fun s n => (s + n, .emit (s + n) :: if i = 2 && n = 0 then [.stop] else [])
    recover := fun s => (s, []) }
  accept x := ⟨x.1, x.2⟩
  boot := [0, 1, 2]

def countInputs : List countSig.In :=
  [(0, 1), (1, 2), (2, 3), (0, 4), (2, 0), (1, 5), (2, 6), (0, 7)]

def waveTests : List (String × Bool) :=
  let k := ((Kernel.boot counters).1.acceptAll countInputs)
  let planned := k.plan { workers := 4 } (k.queue.toList.take 8)
  let waves := k.runWaves { workers := 4 } 64
  let batch := k.runBatch 64
  [ ("kernel waves: the steps of every actor with mail are worked out ahead",
      planned.steps.size == 3 && (planned.get 2).length == 3),
    ("kernel waves: the batch's outputs and states are runBatch's, a stop included",
      waves.outputs == batch.outputs && batch.outputs.length == 7
        && (List.finRange 3).all fun i =>
          (waves.kernel.cell i).state == (batch.kernel.cell i).state
            && (waves.kernel.cell i).up == (batch.kernel.cell i).up) ]

def tests : List (String × Bool) :=
  let r := search shell properties { maxDepth := some 4, constraint := fun k => k.nextToken ≤ 3 }
  let lost := ((Kernel.boot alarms).1.exec misfire).kernel
  let queued := ((Kernel.boot busy).1.accept ()).kernel
  let shared := (Kernel.boot busy).1.exec [.input (), .input (), .input (), .batch 6]
  [ ("kernel agenda: invariant and consequences hold whatever the shell does",
      r.ok && r.witnesses.length == 11),
    ("kernel agenda: a timer fired at the wrong actor still fires at its own",
      pending lost == [(false, .ring false, ⟨1, 0⟩)] && lost.wait == .none && firesTimer lost
        && !lost.quiet true),
    ("kernel fairness: a timer that is always due does not starve a message",
      worked queued == 0 && worked queued.step.kernel.step.kernel == 1),
    ("kernel fairness: a timer that is always due and a queue that is not empty take turns",
      worked shared.kernel == 3 && ticks shared.events == 3) ] ++ waveTests

end Tests.Kernel
