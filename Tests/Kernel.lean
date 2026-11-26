/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Model checks of what `Lanes.Actors.KernelTimers` proves about the kernel's timer agenda (rule
5.1): every sequence of operations a shell can perform, up to a bound, on two actors that arm,
arm again, cancel and stop. The shell here is hostile: it fires any timer the agenda names at
either actor, for either message.
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
      | .ring _ => [])
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
    k.nextToken, k.clock_ms)

instance : BEq Shard := ⟨fun a b => view a == view b⟩
instance : Hashable Shard := ⟨fun k => hash (view k)⟩

def ops (k : Shard) : List (Kernel.Op sig) :=
  let inputs := ids.flatMap fun i =>
    [.arm false 0, .arm false 2, .arm true 1, .disarm false, .halt].map fun msg =>
      Kernel.Op.input (i, msg)
  let fires := (scheduled k).flatMap fun (_, _, due) =>
    ids.flatMap fun i => [true, false].map fun alarm =>
      Kernel.Op.fire (σ := sig) i (Msg.ring alarm) due
  inputs ++ [.advance (k.clock_ms + 1), .advance (k.clock_ms + 2), .step] ++ fires

def shell : Model Shard (Kernel.Op sig) where
  init := [(Kernel.boot alarms).1]
  next k := (ops k).map fun op => (op, (k.apply op).kernel)

def firesTimer (k : Shard) : Bool :=
  match k.step.events with
  | .timeout _ _ :: _ => true
  | _ => false

def isDue (k : Shard) (t : Bool × Msg × Kernel.Due) : Bool :=
  t.2.2.deadline_ms ≤ k.clock_ms

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
    .always "no lost timer: when one is due the shell does not sleep and one fires" fun k =>
      !(pending k).any (isDue k) || (k.wait == .none && firesTimer k),
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

def tests : List (String × Bool) :=
  let r := search shell properties { maxDepth := some 4, constraint := fun k => k.nextToken ≤ 3 }
  let lost := ((Kernel.boot alarms).1.exec misfire).kernel
  [ ("kernel agenda: invariant and consequences hold whatever the shell does",
      r.ok && r.witnesses.length == 6),
    ("kernel agenda: a timer fired at the wrong actor still fires at its own",
      pending lost == [(false, .ring false, ⟨1, 0⟩)] && lost.wait == .none && firesTimer lost
        && !lost.quiet true) ]

end Tests.Kernel
