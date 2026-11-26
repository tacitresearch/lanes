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
-/

@[expose] public section

namespace Lanes

/--
Crash-only (rule 3.3): there is no shutdown path. An actor starts only through `recover`, on its
first start and on every restart, so the recovery path is exercised on every start.
-/
structure Actor (S Msg Eff : Type) where
  init : S
  step : S → Msg → S × List Eff
  /--
  Runs on every start. It maps the state that survived (durable state) to the state to resume
  from, and returns startup effects such as arming timers.

  The default keeps nothing: all state is volatile and a restart resumes from `init`. An actor
  whose state is persisted overrides this; `fun s => (s, [])` says all of it survives.
  -/
  recover : S → S × List Eff := fun _ => (init, [])
  /--
  States that starting the actor anew gives, with nothing to do. An actor in one of them, with
  no timers, can be released from memory, since starting it again gives it back
  (`DECISIONS.md` D42). The default declares none.
  -/
  fresh : S → Bool := fun _ => false
  fresh_recover : ∀ s, fresh s = true → recover init = (s, []) := by
    intro _ h; exact absurd h (by decide)

namespace Actor

variable {S Msg Eff : Type}

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

def mapEff {Eff' : Type} (f : Eff → List Eff') (A : Actor S Msg Eff) : Actor S Msg Eff' where
  init := A.init
  step s m := ((A.step s m).1, (A.step s m).2.flatMap f)
  recover s := ((A.recover s).1, (A.recover s).2.flatMap f)
  fresh := A.fresh
  fresh_recover s h := by simp [A.fresh_recover s h]

def comapMsg {Msg' : Type} (f : Msg' → Msg) (A : Actor S Msg Eff) : Actor S Msg' Eff where
  init := A.init
  step s m := A.step s (f m)
  recover := A.recover
  fresh := A.fresh
  fresh_recover := A.fresh_recover

inductive Reachable (A : Actor S Msg Eff) : S → Prop
  | init : Reachable A A.init
  | step {s : S} (m : Msg) : Reachable A s → Reachable A (A.step s m).1
  | recover {s : S} : Reachable A s → Reachable A (A.recover s).1

def Invariant (A : Actor S Msg Eff) (P : S → Prop) : Prop :=
  ∀ s, A.Reachable s → P s

structure Inductive (A : Actor S Msg Eff) (P : S → Prop) : Prop where
  init : P A.init
  step : ∀ s m, P s → P (A.step s m).1
  recover : ∀ s, P s → P (A.recover s).1

theorem Inductive.invariant {A : Actor S Msg Eff} {P : S → Prop} (h : A.Inductive P) :
    A.Invariant P := by
  intro s hs
  induction hs with
  | init => exact h.init
  | step m _ ih => exact h.step _ m ih
  | recover _ ih => exact h.recover _ ih

theorem Inductive.and {A : Actor S Msg Eff} {P Q : S → Prop} (hP : A.Inductive P)
    (hQ : A.Inductive Q) : A.Inductive (fun s => P s ∧ Q s) where
  init := ⟨hP.init, hQ.init⟩
  step s m h := ⟨hP.step s m h.1, hQ.step s m h.2⟩
  recover s h := ⟨hP.recover s h.1, hQ.recover s h.2⟩

theorem Invariant.and {A : Actor S Msg Eff} {P Q : S → Prop} (hP : A.Invariant P)
    (hQ : A.Invariant Q) : A.Invariant (fun s => P s ∧ Q s) :=
  fun s hs => ⟨hP s hs, hQ s hs⟩

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

theorem Reachable.of_mapEff {Eff' : Type} {f : Eff → List Eff'} {A : Actor S Msg Eff} {s : S}
    (h : (A.mapEff f).Reachable s) : A.Reachable s := by
  induction h with
  | init => exact .init
  | step m _ ih => exact .step m ih
  | recover _ ih => exact .recover ih

theorem Invariant.mapEff {Eff' : Type} (f : Eff → List Eff') {A : Actor S Msg Eff} {P : S → Prop}
    (h : A.Invariant P) : (A.mapEff f).Invariant P :=
  fun s hs => h s hs.of_mapEff

end Actor

/--
`actor_invariant [defs]` proves a goal `A.Invariant P` by induction: `P` holds initially, every
message preserves it and recovery preserves it. It splits on the message, unfolds the listed
definitions (normally the actor itself) and closes each case with `grind`, which splits the
`if`s of the handler and does the arithmetic.

Cases it cannot close are left as goals, one per message constructor, with the actor unfolded.
-/
syntax (name := actorInvariant) "actor_invariant" (" [" Lean.Parser.Tactic.simpLemma,* "]")? :
  tactic

macro_rules
  | `(tactic| actor_invariant [$defs,*]) => `(tactic|
      (apply Lanes.Actor.Inductive.invariant
       refine ⟨?_, ?_, ?_⟩
       · first | (simp [$defs,*]; done) | skip
       · intro s m h
         cases m <;> (try simp only [$defs,*]) <;> (try simp only [$defs,*] at h) <;>
           first | grind | skip
       · intro s h
         (try simp only [$defs,*]) <;> first | grind | skip))
  | `(tactic| actor_invariant) => `(tactic| actor_invariant [])

end Lanes
