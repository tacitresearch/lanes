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
`Effect σ i` (see `Lanes.Core.System`).
-/

@[expose] public section

namespace Lanes

/-- What the environment gives a step at its moment: the time and some entropy. The runtime
reads them, the checker and the simulator choose them, and a trace records them (`Event.tick`),
so a step stays a function of what it is given. -/
structure Moment where
  /-- Wall time, in milliseconds since the Unix epoch, as the runtime read it. -/
  now_ms : Nat := 0
  /-- 64 bits nobody outside can predict: for a token, jitter or a sample, never for uniqueness,
  since the environment may give any seed, two equal ones included. -/
  seed : UInt64 := 0
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- Who sent the message a step handles: the outside world, an actor, or one of the receiver's
own timers. -/
inductive Sender (Id : Type) where
  | outside
  | actor (i : Id)
  | timer
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- The sender of a message that came from `src` (`none` is the outside world). -/
def Sender.ofSrc {Id : Type} : Option Id → Sender Id
  | none => .outside
  | some i => .actor i

/-- The sender with its actor renamed by `f`. -/
def Sender.map {Id Id' : Type} (f : Id → Id') : Sender Id → Sender Id'
  | .outside => .outside
  | .actor i => .actor (f i)
  | .timer => .timer

/-- What a step is told besides its state and its message: the moment and who sent it. -/
structure Ctx (Id : Type) extends Moment where
  src : Sender Id := .outside
  deriving DecidableEq, Repr

/--
Crash-only (rule 3.3): there is no shutdown path. An actor starts only through `recover`, on its
first start and on every restart, so the recovery path is exercised on every start.

The semantics runs `stepAt` and `recoverAt`, which are given the step's context (`Ctx`). An actor
that does not read it gives `step` and `recover`, and the context is ignored: that is the default
of `stepAt` and `recoverAt`. An actor that reads it gives `stepAt` (and `recoverAt`); its `step` is
then `stepAt` at the default context, which nothing in the semantics uses. `Id` is the type of the
actors that may send to it, as `Sender` names them.
-/
structure Actor (S Msg Eff : Type) (Id : Type := Unit) where
  init : S
  step : S → Msg → S × List Eff := fun s m => stepAt {} s m
  stepAt : Ctx Id → S → Msg → S × List Eff := fun _ => step
  /--
  Runs on every start. It maps the state that survived to the state to resume from, and returns
  startup effects such as arming timers.

  The default keeps nothing: a restart resumes from `init`. `fun s => (s, [])` keeps the state
  the actor had when it stopped, while the process lives.
  -/
  recover : S → S × List Eff := fun _ => (init, [])
  recoverAt : Moment → S → S × List Eff := fun _ => recover
  /--
  States that starting the actor anew gives, with nothing to do. An actor in one of them, with
  no timers, can be released from memory, since starting it again gives it back
  (`docs/decisions/D51-release-actors-at-rest.md`). The default declares none.
  -/
  fresh : S → Bool := fun _ => false
  fresh_recover : ∀ t s, fresh s = true → recoverAt t init = (s, []) := by
    intro _ _ h; exact absurd h (by decide)

namespace Actor

variable {S Msg Eff Id : Type}

/-- The state after handling the messages in order from `s`, and the effects of all the steps, in
the order they were returned. -/
def run (A : Actor S Msg Eff Id) (s : S) : List Msg → S × List Eff
  | [] => (s, [])
  | m :: ms =>
    let r := A.step s m
    let rs := A.run r.1 ms
    (rs.1, r.2 ++ rs.2)

@[simp] theorem run_nil (A : Actor S Msg Eff Id) (s : S) : A.run s [] = (s, []) := rfl

@[simp] theorem run_cons (A : Actor S Msg Eff Id) (s : S) (m : Msg) (ms : List Msg) :
    A.run s (m :: ms) = ((A.run (A.step s m).1 ms).1, (A.step s m).2 ++ (A.run (A.step s m).1 ms).2) :=
  rfl

/-- The same actor with each effect replaced by those `f` gives: how an actor written over an
abstract `Eff` is put into a system. -/
def mapEff {Eff' : Type} (f : Eff → List Eff') (A : Actor S Msg Eff Id) : Actor S Msg Eff' Id where
  init := A.init
  step s m := ((A.step s m).1, (A.step s m).2.flatMap f)
  stepAt c s m := ((A.stepAt c s m).1, (A.stepAt c s m).2.flatMap f)
  recover s := ((A.recover s).1, (A.recover s).2.flatMap f)
  recoverAt t s := ((A.recoverAt t s).1, (A.recoverAt t s).2.flatMap f)
  fresh := A.fresh
  fresh_recover t s h := by simp [A.fresh_recover t s h]

/-- The same actor told of senders of type `Id'`, which `f` names as senders of type `Id`: how an
actor of one system is put into a bigger one, as a side of a join. -/
def mapSrc {Id' : Type} (f : Sender Id' → Sender Id) (A : Actor S Msg Eff Id) : Actor S Msg Eff Id' where
  init := A.init
  step := A.step
  stepAt c s m := A.stepAt { c with src := f c.src } s m
  recover := A.recover
  recoverAt := A.recoverAt
  fresh := A.fresh
  fresh_recover := A.fresh_recover

/-- The states the actor reaches on its own, by any messages at any moments and any restarts.
Restarts are included because the semantics may crash an actor at any step (rule 3.3). -/
inductive Reachable (A : Actor S Msg Eff Id) : S → Prop
  | init : Reachable A A.init
  | step {s : S} (c : Ctx Id) (m : Msg) : Reachable A s → Reachable A (A.stepAt c s m).1
  | recover {s : S} (t : Moment) : Reachable A s → Reachable A (A.recoverAt t s).1

/-- `P` holds in every state the actor reaches. `System.invariant_of_actor` lifts it to every
system the actor is in, under every environment model. -/
def Invariant (A : Actor S Msg Eff Id) (P : S → Prop) : Prop :=
  ∀ s, A.Reachable s → P s

/-- `P` holds at `init` and every step and every restart keeps it: the three cases
`actor_invariant` proves, which give `Invariant` (`Inductive.invariant`). -/
structure Inductive (A : Actor S Msg Eff Id) (P : S → Prop) : Prop where
  init : P A.init
  step : ∀ c s m, P s → P (A.stepAt c s m).1
  recover : ∀ t s, P s → P (A.recoverAt t s).1

theorem Inductive.invariant {A : Actor S Msg Eff Id} {P : S → Prop} (h : A.Inductive P) :
    A.Invariant P := by
  intro s hs
  induction hs with
  | init => exact h.init
  | step c m _ ih => exact h.step c _ m ih
  | recover t _ ih => exact h.recover t _ ih

theorem Inductive.and {A : Actor S Msg Eff Id} {P Q : S → Prop} (hP : A.Inductive P)
    (hQ : A.Inductive Q) : A.Inductive (fun s => P s ∧ Q s) where
  init := ⟨hP.init, hQ.init⟩
  step c s m h := ⟨hP.step c s m h.1, hQ.step c s m h.2⟩
  recover t s h := ⟨hP.recover t s h.1, hQ.recover t s h.2⟩

theorem Invariant.and {A : Actor S Msg Eff Id} {P Q : S → Prop} (hP : A.Invariant P)
    (hQ : A.Invariant Q) : A.Invariant (fun s => P s ∧ Q s) :=
  fun s hs => ⟨hP s hs, hQ s hs⟩

theorem Invariant.mono {A : Actor S Msg Eff Id} {P Q : S → Prop} (hP : A.Invariant P)
    (h : ∀ s, P s → Q s) : A.Invariant Q :=
  fun s hs => h s (hP s hs)

/--
Prove `Q` invariant using an already proved invariant `P` as a hypothesis in each case.
This is how invariants are strengthened step by step.
-/
theorem Invariant.of_inductive_under {A : Actor S Msg Eff Id} {P Q : S → Prop}
    (hP : A.Invariant P) (init : Q A.init)
    (step : ∀ c s m, A.Reachable s → P s → Q s → Q (A.stepAt c s m).1)
    (recover : ∀ t s, A.Reachable s → P s → Q s → Q (A.recoverAt t s).1) : A.Invariant Q := by
  intro s hs
  induction hs with
  | init => exact init
  | step c m hr ih => exact step c _ m hr (hP _ hr) ih
  | recover t hr ih => exact recover t _ hr (hP _ hr) ih

theorem Reachable.of_mapEff {Eff' : Type} {f : Eff → List Eff'} {A : Actor S Msg Eff Id} {s : S}
    (h : (A.mapEff f).Reachable s) : A.Reachable s := by
  induction h with
  | init => exact .init
  | step c m _ ih => exact .step c m ih
  | recover t _ ih => exact .recover t ih

theorem Invariant.mapEff {Eff' : Type} (f : Eff → List Eff') {A : Actor S Msg Eff Id}
    {P : S → Prop} (h : A.Invariant P) : (A.mapEff f).Invariant P :=
  fun s hs => h s hs.of_mapEff

theorem Reachable.of_mapSrc {Id' : Type} {f : Sender Id' → Sender Id} {A : Actor S Msg Eff Id}
    {s : S} (h : (A.mapSrc f).Reachable s) : A.Reachable s := by
  induction h with
  | init => exact .init
  | step c m _ ih => exact .step _ m ih
  | recover t _ ih => exact .recover t ih

theorem Invariant.mapSrc {Id' : Type} (f : Sender Id' → Sender Id) {A : Actor S Msg Eff Id}
    {P : S → Prop} (h : A.Invariant P) : (A.mapSrc f).Invariant P :=
  fun s hs => h s hs.of_mapSrc

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
       · intro c s m h
         cases m <;> (try simp only [$defs,*]) <;> (try simp only [$defs,*] at h) <;>
           first | grind | skip
       · intro t s h
         (try simp only [$defs,*]) <;> first | grind | skip))
  | `(tactic| actor_invariant) => `(tactic| actor_invariant [])

end Lanes
