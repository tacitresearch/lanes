/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Step
public import Lanes.Semantics.System
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Cslib.Foundations.Data.OmegaSequence.Temporal

/-!
# Liveness: infinite runs, fairness and leads-to

A safety property is about the states a system can reach. "Every request is eventually answered"
is about what a system does if it is left to run, so it is a property of infinite runs, and it
holds only of runs in which the system is not held back forever. This file defines those runs
and the rule that proves such properties from single steps.

A run is infinite. At each position it takes one enabled event or stutters, so a system with
nothing left to do still has runs. A run is fair when the system is not held back forever from
anything it owes: an `Obligation` that is due at every position from some point on is taken.
The obligations are the events the system itself makes happen: delivering a message to an actor
that is up, firing an armed timer of an actor that is up, starting a stopped actor that has
mail, and handing over an output. Inputs, drops, duplicates and crashes are the choice of the
environment, are not obligations, and so no fairness can be assumed of them. Nor is restarting
an actor that has no mail, even where the environment model says it may happen. Fairness is
stated for each obligation on its own (this message, this timer). Fairness of all of them
together would let one timer wait forever while others fire.

Fairness says "eventually" and gives no bound. And it reads a timer as the semantics does: an
actor that arms a pending timer again leaves it armed here, where the runtime starts its delay
again. A liveness theorem that rests on a timer is therefore about an actor that does not keep
restarting that timer.

CSLib provides the infinite sequences (`ωSequence`), infinite executions of a transition system
(`LTS.OmegaExecution`) and leads-to along one sequence (`ωSequence.LeadsTo`), and they are used
here. It has no transition system with stuttering and no fairness of events (the one in its FLP
development is of processes in that algorithm), so those two are defined here.

## Main definitions

- `Spec.stutter`: a spec with a step that changes nothing.
- `System.Run`: an infinite run of a system from its initial state.
- `Obligation`, `Obligation.Due`: what a system owes, and when.
- `System.Run.WeakFair`, `System.Run.Fair`: weak fairness, and the runs that are fair to every
  obligation.
- `System.LeadsTo`: in every fair run, a state satisfying `P` is followed by one satisfying `Q`.

## Main statements

- `System.LeadsTo.ensures_of_invariant`: the proof rule (Lamport's WF1). `P` leads to `Q` when
  every step from `P` keeps `P` or reaches `Q`, some obligation is due throughout `P`, and
  taking it reaches `Q`.
- `System.LeadsTo.trans`, `System.LeadsTo.mono`: leads-to is transitive and monotone.
- `Obligation.Due.enabled`: an obligation that is due can be taken, so fairness never asks for
  a step the semantics does not have.
- `System.Run.Fair.output_taken`: an emitted output is eventually handed over.
-/

@[expose] public section

namespace Lanes

open Cslib

variable {σ : Signature}

/-- `spec` with a stuttering step: the label `none` changes nothing. A state with nothing
enabled then still has infinite executions. -/
def Spec.stutter {State Label : Type*} (spec : Spec State Label) : LTS State (Option Label) where
  Tr s μ s' :=
    match μ with
    | none => s' = s
    | some μ => spec.Tr s μ s'

/-- What a system owes: the events it makes happen itself. The environment's events (inputs,
drops, duplicates, crashes) have no obligation, so fairness cannot be assumed of them. -/
inductive Obligation (σ : Signature) : Type where
  /-- Deliver a message in flight. -/
  | deliver (e : Envelope σ)
  /-- Fire a timer. -/
  | timeout (i : σ.Id) (msg : σ.Msg i)
  /-- Start a stopped actor. -/
  | start (i : σ.Id)
  /-- Hand an emitted output to the outside world. -/
  | output (out : σ.Out)

namespace Obligation

variable {sys : System σ} {env : EnvModel σ} {c : SysState sys} {ob : Obligation σ}

/-- The event that meets an obligation. -/
def event : Obligation σ → Event σ
  | .deliver e => .deliver e
  | .timeout i msg => .timeout i msg
  | .start i => .start i
  | .output out => .output out

/-- When an obligation is due: the message is deliverable and its receiver is up, the timer is
armed and its actor is up, the actor is stopped and has mail, the output is waiting. -/
def Due (env : EnvModel σ) (c : SysState sys) : Obligation σ → Prop
  | .deliver e => c.up e.dst = true ∧ c.deliverable env e = true
  | .timeout i msg => c.up i = true ∧ msg ∈ c.timers i
  | .start i => c.up i = false ∧ c.hasMail i = true
  | .output out => out ∈ c.outbox

/-- An obligation that is due can be taken. -/
theorem Due.enabled (h : ob.Due env c) : ∃ c', c.step env ob.event = some c' := by
  cases ob with
  | deliver e => exact ⟨_, SysState.step_deliver.mpr ⟨h.1, h.2, rfl⟩⟩
  | timeout i msg => exact ⟨_, SysState.step_timeout.mpr ⟨h.1, h.2, rfl⟩⟩
  | start i => exact ⟨_, SysState.step_start.mpr ⟨h.1, .inl h.2, rfl⟩⟩
  | output out => exact ⟨_, SysState.step_output.mpr ⟨h, rfl⟩⟩

end Obligation

namespace System

variable {sys : System σ} {env : EnvModel σ}

/-- An infinite run of `sys` under `env`, from the initial state. -/
structure Run (sys : System σ) (env : EnvModel σ) where
  /-- The state at each position. -/
  state : ωSequence (SysState sys)
  /-- The event taken at each position, or `none` where the run stutters. -/
  event : ωSequence (Option (Event σ))
  /-- The run starts in the freshly booted state. -/
  init : state 0 = SysState.init sys env
  /-- Each position takes an enabled event or stutters. -/
  exec : (sys.sem env).stutter.OmegaExecution state event

namespace Run

variable {r : sys.Run env} {n : ℕ}

/-- The run that stutters forever. -/
def idle (sys : System σ) (env : EnvModel σ) : sys.Run env where
  state := .const (SysState.init sys env)
  event := .const none
  init := rfl
  exec _ := rfl

/-- Every system has a run, whether or not anything is enabled. -/
instance : Nonempty (sys.Run env) := ⟨idle sys env⟩

/-- A position that takes an event steps by it. -/
theorem step_some {ev : Event σ} (h : r.event n = some ev) :
    (r.state n).step env ev = some (r.state (n + 1)) := by
  simpa [Spec.stutter, System.sem, h] using r.exec n

/-- A position that stutters keeps the state. -/
theorem step_none (h : r.event n = none) : r.state (n + 1) = r.state n := by
  simpa [Spec.stutter, h] using r.exec n

/-- Every state of a run is reachable, so invariants hold along runs. -/
theorem reachable (r : sys.Run env) (n : ℕ) : sys.Reachable env (r.state n) := by
  induction n with
  | zero => exact r.init ▸ .init
  | succ n ih =>
    cases h : r.event n with
    | none => exact step_none h ▸ ih
    | some ev => exact .step ev ih (step_some h)

/-- Weak fairness of a set of obligations: if from some position on one of them is due at every
position, then one of them is taken at that position or a later one. -/
def WeakFair (r : sys.Run env) (obs : Set (Obligation σ)) : Prop :=
  ∀ n, (∀ m, n ≤ m → ∃ ob ∈ obs, ob.Due env (r.state m)) →
    ∃ m, n ≤ m ∧ ∃ ob ∈ obs, r.event m = some ob.event

/-- A fair run is weakly fair to each obligation on its own. -/
def Fair (r : sys.Run env) : Prop :=
  ∀ ob : Obligation σ, r.WeakFair {ob}

/-- In a fair run, an obligation that stays due is taken. -/
theorem Fair.taken (hfair : r.Fair) {ob : Obligation σ}
    (hdue : ∀ m, n ≤ m → ob.Due env (r.state m)) : ∃ m, n ≤ m ∧ r.event m = some ob.event := by
  obtain ⟨m, hm, _, rfl, hev⟩ := hfair ob n fun m hm => ⟨ob, rfl, hdue m hm⟩
  exact ⟨m, hm, hev⟩

/-- In a fair run, an emitted output is eventually handed over. -/
theorem Fair.output_taken (hfair : r.Fair) {out : σ.Out} (hout : out ∈ (r.state n).outbox) :
    ∃ m, n ≤ m ∧ r.event m = some (.output out) := by
  by_contra hnever
  refine hnever (hfair.taken (ob := .output out) fun m hm => ?_)
  induction m, hm using Nat.le_induction with
  | base => exact hout
  | succ m hm ih =>
    cases hev : r.event m with
    | none => exact step_none hev ▸ ih
    | some ev =>
      refine SysState.mem_outbox_of_step ih (step_some hev) ?_
      rintro rfl
      exact hnever ⟨m, hm, hev⟩

end Run

/-- `P` leads to `Q`: in every fair run, at every position where `P` holds, `Q` holds at that
position or a later one. -/
def LeadsTo (sys : System σ) (env : EnvModel σ) (P Q : SysState sys → Prop) : Prop :=
  ∀ r : sys.Run env, r.Fair → r.state.LeadsTo {c | P c} {c | Q c}

namespace LeadsTo

variable {I P P' Q Q' R : SysState sys → Prop}

/-- The definition of leads-to, without the sets. -/
theorem iff : sys.LeadsTo env P Q ↔
    ∀ r : sys.Run env, r.Fair → ∀ n, P (r.state n) → ∃ m, n ≤ m ∧ Q (r.state m) :=
  Iff.rfl

/--
The proof rule for leads-to (Lamport's WF1), for states that satisfy an invariant `I`. From a
state satisfying `P` and not yet `Q`:

- `step`: every step keeps `P` or reaches `Q`;
- `due`: the obligation `ob` is due;
- `progress`: taking `ob` reaches `Q`.

Then `P` leads to `Q`: `P` holds until `Q` does, so `ob` stays due, so a fair run takes it.
-/
theorem ensures_of_invariant (hI : sys.Invariant env I) (ob : Obligation σ)
    (step : ∀ c ev c', I c → P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, I c → P c → ¬Q c → ob.Due env c)
    (progress : ∀ c c', I c → P c → ¬Q c → c.step env ob.event = some c' → Q c') :
    sys.LeadsTo env P Q := by
  intro r hfair n hP
  by_contra hnever
  have hQ (m : ℕ) (hm : n ≤ m) : ¬Q (r.state m) := fun h => hnever ⟨m, hm, h⟩
  have hP (m : ℕ) (hm : n ≤ m) : P (r.state m) := by
    induction m, hm using Nat.le_induction with
    | base => exact hP
    | succ m hm ih =>
      cases hev : r.event m with
      | none => exact Run.step_none hev ▸ ih
      | some ev =>
        exact (step _ ev _ (hI _ (r.reachable m)) ih (hQ m hm) (Run.step_some hev)).resolve_right
          (hQ (m + 1) (by omega))
  obtain ⟨m, hm, hev⟩ := hfair.taken fun m hm =>
    due _ (hI _ (r.reachable m)) (hP m hm) (hQ m hm)
  exact hQ (m + 1) (by omega)
    (progress _ _ (hI _ (r.reachable m)) (hP m hm) (hQ m hm) (Run.step_some hev))

/-- The proof rule for leads-to, with no invariant. -/
theorem ensures (ob : Obligation σ)
    (step : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, P c → ¬Q c → ob.Due env c)
    (progress : ∀ c c', P c → ¬Q c → c.step env ob.event = some c' → Q c') :
    sys.LeadsTo env P Q :=
  ensures_of_invariant (I := fun _ => True) (fun _ _ => trivial) ob
    (fun c ev c' _ => step c ev c') (fun c _ => due c) (fun c c' _ => progress c c')

/-- What already holds is reached at once. -/
theorem of_imp (h : ∀ c, P c → Q c) : sys.LeadsTo env P Q :=
  fun r _ n hP => ⟨n, Nat.le_refl n, h (r.state n) hP⟩

/-- Leads-to is transitive. -/
theorem trans (h₁ : sys.LeadsTo env P Q) (h₂ : sys.LeadsTo env Q R) : sys.LeadsTo env P R :=
  fun r hfair => ωSequence.leadsTo_trans (h₁ r hfair) (h₂ r hfair)

/-- Leads-to is monotone: it survives a stronger start and a weaker goal. Both may assume an
invariant. -/
theorem mono_of_invariant (hI : sys.Invariant env I) (hP : ∀ c, I c → P' c → P c)
    (hQ : ∀ c, I c → Q c → Q' c) (h : sys.LeadsTo env P Q) : sys.LeadsTo env P' Q' := by
  intro r hfair n hP'
  obtain ⟨m, hm, hQm⟩ := h r hfair n (hP _ (hI _ (r.reachable n)) hP')
  exact ⟨m, hm, hQ _ (hI _ (r.reachable m)) hQm⟩

/-- Leads-to is monotone: it survives a stronger start and a weaker goal. -/
theorem mono (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) (h : sys.LeadsTo env P Q) :
    sys.LeadsTo env P' Q' :=
  mono_of_invariant (I := fun _ => True) (fun _ _ => trivial) (fun c _ => hP c) (fun c _ => hQ c) h

end LeadsTo

end System

end Lanes
