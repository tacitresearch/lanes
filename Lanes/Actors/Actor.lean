/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Actors

An `Actor` is the unit of logic in Lanes: a pure, total step function over a private state. It
performs no I/O. Everything it wants done is returned as a list of effect values (rule 2.4), so the
same function runs in production, in the simulator, in the model checker and in proofs.

The effect type `Eff` is a parameter. Library actors keep it abstract and are reused by mapping
their effects into a concrete system (`Actor.mapEff`). Actors that live in a `System` use
`Effect σ i` (see `Lanes.Actors.System`).

## Main definitions

- `Actor S Msg Eff`: initial state, `step` and `recover`.
- `Actor.Reachable`: the states an actor can be in, over every message sequence and every crash.
- `Actor.Invariant`, `Actor.Inductive`: per-actor invariants and the induction principle that
  proves them, with the obligation shape `P s → P (A.step s m).1`.
-/

@[expose] public section

namespace Lanes

/--
An actor with private state `S`, handling messages of type `Msg` and returning effects of type
`Eff`.

Crash-only (rule 3.3): there is no shutdown path. An actor starts only through `recover`, on its
first start and on every restart, so the recovery path is exercised on every start.
-/
structure Actor (S Msg Eff : Type) where
  /-- The state of an actor that has never started. -/
  init : S
  /-- Handle one message: the next state and the effects to perform. Pure and total. -/
  step : S → Msg → S × List Eff
  /--
  Runs on every start. It maps the state that survived (durable state) to the state to resume
  from, and returns startup effects such as arming timers.

  The default keeps nothing: all state is volatile and a restart resumes from `init`. An actor
  whose state is persisted overrides this; `fun s => (s, [])` says all of it survives.
  -/
  recover : S → S × List Eff := fun _ => (init, [])

namespace Actor

variable {S Msg Eff : Type}

/-- Handle a list of messages in order, collecting the effects. -/
def run (A : Actor S Msg Eff) (s : S) : List Msg → S × List Eff
  | [] => (s, [])
  | m :: ms =>
    let r := A.step s m
    let rs := A.run r.1 ms
    (rs.1, r.2 ++ rs.2)

@[simp] theorem run_nil (A : Actor S Msg Eff) (s : S) : A.run s [] = (s, []) := rfl

@[simp] theorem run_cons (A : Actor S Msg Eff) (s : S) (m : Msg) (ms : List Msg) :
    A.run s (m :: ms) = ((A.run (A.step s m).1 ms).1, (A.step s m).2 ++ (A.run (A.step s m).1 ms).2) :=
  rfl

/-- Reuse an actor in another setting by translating each of its effects. -/
def mapEff {Eff' : Type} (f : Eff → List Eff') (A : Actor S Msg Eff) : Actor S Msg Eff' where
  init := A.init
  step s m := ((A.step s m).1, (A.step s m).2.flatMap f)
  recover s := ((A.recover s).1, (A.recover s).2.flatMap f)

/-- Reuse an actor behind a different message type. -/
def comapMsg {Msg' : Type} (f : Msg' → Msg) (A : Actor S Msg Eff) : Actor S Msg' Eff where
  init := A.init
  step s m := A.step s (f m)
  recover := A.recover

/--
The states an actor can reach: `init`, closed under handling any message and under recovery
(a crash followed by a start) at any point.
-/
inductive Reachable (A : Actor S Msg Eff) : S → Prop
  | init : Reachable A A.init
  | step {s : S} (m : Msg) : Reachable A s → Reachable A (A.step s m).1
  | recover {s : S} : Reachable A s → Reachable A (A.recover s).1

/-- `P` is an invariant of `A` if it holds in every reachable state. -/
def Invariant (A : Actor S Msg Eff) (P : S → Prop) : Prop :=
  ∀ s, A.Reachable s → P s

/--
`P` is inductive for `A`: it holds initially and is preserved by every message and by recovery.
This is the proof obligation for a per-actor invariant.
-/
structure Inductive (A : Actor S Msg Eff) (P : S → Prop) : Prop where
  /-- `P` holds before the actor has ever run. -/
  init : P A.init
  /-- Every message preserves `P`. -/
  step : ∀ s m, P s → P (A.step s m).1
  /-- Recovery preserves `P`. -/
  recover : ∀ s, P s → P (A.recover s).1

/-- An inductive predicate is an invariant. -/
theorem Inductive.invariant {A : Actor S Msg Eff} {P : S → Prop} (h : A.Inductive P) :
    A.Invariant P := by
  intro s hs
  induction hs with
  | init => exact h.init
  | step m _ ih => exact h.step _ m ih
  | recover _ ih => exact h.recover _ ih

/-- The conjunction of two inductive predicates is inductive. -/
theorem Inductive.and {A : Actor S Msg Eff} {P Q : S → Prop} (hP : A.Inductive P)
    (hQ : A.Inductive Q) : A.Inductive (fun s => P s ∧ Q s) where
  init := ⟨hP.init, hQ.init⟩
  step s m h := ⟨hP.step s m h.1, hQ.step s m h.2⟩
  recover s h := ⟨hP.recover s h.1, hQ.recover s h.2⟩

/-- Invariants are closed under conjunction. -/
theorem Invariant.and {A : Actor S Msg Eff} {P Q : S → Prop} (hP : A.Invariant P)
    (hQ : A.Invariant Q) : A.Invariant (fun s => P s ∧ Q s) :=
  fun s hs => ⟨hP s hs, hQ s hs⟩

/-- A weaker predicate inherits invariance. -/
theorem Invariant.mono {A : Actor S Msg Eff} {P Q : S → Prop} (hP : A.Invariant P)
    (h : ∀ s, P s → Q s) : A.Invariant Q :=
  fun s hs => h s (hP s hs)

/--
Prove `Q` invariant using an already proved invariant `P` as a hypothesis in each case.
This is how invariants are strengthened step by step.
-/
theorem Invariant.of_inductive_under {A : Actor S Msg Eff} {P Q : S → Prop}
    (hP : A.Invariant P) (init : Q A.init)
    (step : ∀ s m, A.Reachable s → P s → Q s → Q (A.step s m).1)
    (recover : ∀ s, A.Reachable s → P s → Q s → Q (A.recover s).1) : A.Invariant Q := by
  intro s hs
  induction hs with
  | init => exact init
  | step m hr ih => exact step _ m hr (hP _ hr) ih
  | recover hr ih => exact recover _ hr (hP _ hr) ih

/-- Reachable states of a translated actor are reachable states of the original. -/
theorem Reachable.of_mapEff {Eff' : Type} {f : Eff → List Eff'} {A : Actor S Msg Eff} {s : S}
    (h : (A.mapEff f).Reachable s) : A.Reachable s := by
  induction h with
  | init => exact .init
  | step m _ ih => exact .step m ih
  | recover _ ih => exact .recover ih

/-- Invariants transfer along `mapEff`: translating effects does not change the state logic. -/
theorem Invariant.mapEff {Eff' : Type} (f : Eff → List Eff') {A : Actor S Msg Eff} {P : S → Prop}
    (h : A.Invariant P) : (A.mapEff f).Invariant P :=
  fun s hs => h s hs.of_mapEff

end Actor

end Lanes
