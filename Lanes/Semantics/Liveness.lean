/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.FairScheduler
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
anything it owes: an `Obligation` that is due at every position from some point on, and whose
wait no step starts again, is taken. The obligations are the events the system itself makes
happen: delivering a message to an actor that is up, firing an armed timer of an actor that is
up, starting a stopped actor that has mail, and handing over an output. Inputs, drops,
duplicates and crashes are the choice of the environment, are not obligations, and so no
fairness can be assumed of them. Nor is restarting an actor that has no mail, even where the
environment model says it may happen. Fairness is stated for each obligation on its own (this
message, this timer). Fairness of all of them together would let one timer wait forever while
others fire. Fairness rules out no finite run: `Lanes.Semantics.FairRuns` proves that each one
extends to a fair run.

A timer is the one obligation whose wait can start again. An actor that arms a pending timer
again leaves it as it is in the semantics, and in the runtime gives it a new deadline: the
delay starts again. That is what a keep-alive is for, and a timer that every heartbeat arms
again must not be obliged to fire while heartbeats arrive. So fairness obliges a timer to fire
only if it stays pending and no step arms it again (`Obligation.Restarted`), which is what the
runtime provides. This asks less of a run than firing every timer that stays pending
(`System.Run.Impatient`). There are more fair runs, and a leads-to theorem that rests on a
timer has one more thing to show: that the timer is left alone. Fairness says "eventually" and
gives no bound.

CSLib provides the infinite sequences (`ωSequence`), infinite executions of a transition system
(`LTS.OmegaExecution`) and leads-to along one sequence (`ωSequence.LeadsTo`), and they are used
here. It has no transition system with stuttering and no fairness of events (the one in its FLP
development is of processes in that algorithm), so those two are defined here.

## Main definitions

- `Spec.stutter`: a spec with a step that changes nothing.
- `System.Run`: an infinite run of a system from its initial state.
- `Obligation`, `Obligation.Due`: what a system owes, and when.
- `Obligation.Restarted`: the steps that start the wait for an obligation again, which are the
  steps that arm a timer.
- `System.Run.WeakFair`, `System.Run.Fair`: weak fairness, and the runs that are fair to every
  obligation.
- `System.Run.Impatient`: the runs that also fire a timer whose actor keeps arming it.
- `System.LeadsTo`: in every fair run, a state satisfying `P` is followed by one satisfying `Q`.

## Main statements

- `System.LeadsTo.ensures_of_invariant`: the proof rule (Lamport's WF1). `P` leads to `Q` when
  every step from `P` keeps `P` or reaches `Q`, some obligation is due throughout `P`, no step
  from `P` restarts it, and taking it reaches `Q`.
- `System.LeadsTo.trans`, `System.LeadsTo.mono`: leads-to is transitive and monotone.
- `Obligation.Due.enabled`: an obligation that is due can be taken, so fairness never asks for
  a step the semantics does not have.
- `System.Run.Fair.output_taken`: an emitted output is eventually handed over.
- `System.Run.Impatient.fair`: a run that fires every timer that stays pending is fair.
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

/-- Whether taking `ev` from `c` starts the wait for an obligation again. Only a timer waits
again, when a step of its actor arms it: the runtime then gives it a new deadline. Nothing
starts the wait for a delivery, a start or an output again. -/
def Restarted (c : SysState sys) (ev : Event σ) : Obligation σ → Prop
  | .timeout i msg => .timeout i msg ∈ c.arms ev
  | .deliver _ | .start _ | .output _ => False

end Obligation

namespace Effect

variable {i : σ.Id} {effs : List (Effect σ i)}

/-- Effects arm a timer when `after` with its message is among them. -/
theorem mem_timeouts {msg : σ.Msg i} :
    Event.timeout i msg ∈ timeouts i effs ↔ ∃ delay_ms, after delay_ms msg ∈ effs := by
  simp only [timeouts, List.mem_filterMap]
  constructor
  · rintro ⟨eff, heff, h⟩
    cases eff <;> simp_all
    exact ⟨_, heff⟩
  · rintro ⟨delay_ms, h⟩
    exact ⟨_, h, rfl⟩

/-- The effects of an actor arm that actor's timers. -/
theorem eq_of_mem_timeouts {e : Event σ} (h : e ∈ timeouts i effs) : ∃ msg, e = .timeout i msg := by
  obtain ⟨eff, -, heff⟩ := List.mem_filterMap.mp h
  cases eff <;> simp_all [eq_comm]

end Effect

/-- An event arms timers of the actor that takes the step, and of no other. -/
theorem SysState.actor?_of_mem_arms {sys : System σ} {c : SysState sys} {ev e : Event σ}
    (h : e ∈ c.arms ev) : ∃ i msg, e = .timeout i msg ∧ ev.actor? = some i := by
  cases ev with
  | deliver _ | duplicate _ | timeout _ _ | start _ =>
    obtain ⟨msg, rfl⟩ := Effect.eq_of_mem_timeouts h
    exact ⟨_, msg, rfl, rfl⟩
  | input _ | drop _ | output _ | crash _ => exact absurd h List.not_mem_nil

/-- A step restarts an obligation exactly when it arms the timer that the obligation fires. -/
theorem Obligation.restarted_iff_mem_arms {sys : System σ} {c : SysState sys} {ev : Event σ}
    {ob : Obligation σ} : ob.Restarted c ev ↔ ob.event ∈ c.arms ev := by
  cases ob with
  | timeout i msg => rfl
  | deliver _ | start _ | output _ =>
    refine iff_of_false id fun h => ?_
    obtain ⟨_, _, h, -⟩ := SysState.actor?_of_mem_arms h
    cases h

/-- Fills in the premise `quiet` of the leads-to rule for an obligation that is not a timer:
no step restarts it. -/
macro "never_restarted" : tactic =>
  `(tactic| first
    | (intros; exact False.elim (by assumption))
    | fail "a step that arms this timer restarts it: give the premise `quiet`")

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

/-- The step taken at position `n` starts the wait for `ob` again. -/
def Restarts (r : sys.Run env) (n : ℕ) (ob : Obligation σ) : Prop :=
  ∃ ev, r.event n = some ev ∧ ob.Restarted (r.state n) ev

/-- Weak fairness of a set of obligations: if from some position on, at every position one of
them is due and the step taken there does not restart it, then one of them is taken at that
position or a later one. -/
def WeakFair (r : sys.Run env) (obs : Set (Obligation σ)) : Prop :=
  ∀ n, (∀ m, n ≤ m → ∃ ob ∈ obs, ob.Due env (r.state m) ∧ ¬r.Restarts m ob) →
    ∃ m, n ≤ m ∧ ∃ ob ∈ obs, r.event m = some ob.event

/-- A fair run is weakly fair to each obligation on its own. -/
def Fair (r : sys.Run env) : Prop :=
  ∀ ob : Obligation σ, r.WeakFair {ob}

/-- Fairness, without the sets: an obligation that stays due and is not restarted is taken. -/
theorem fair_iff : r.Fair ↔ ∀ (ob : Obligation σ) (n : ℕ),
    (∀ m, n ≤ m → ob.Due env (r.state m) ∧ ¬r.Restarts m ob) →
      ∃ m, n ≤ m ∧ r.event m = some ob.event := by
  simp [Fair, WeakFair]

/-- In a fair run, an obligation that stays due and is not restarted is taken. -/
theorem Fair.taken (hfair : r.Fair) {ob : Obligation σ}
    (hdue : ∀ m, n ≤ m → ob.Due env (r.state m)) (hquiet : ∀ m, n ≤ m → ¬r.Restarts m ob) :
    ∃ m, n ≤ m ∧ r.event m = some ob.event :=
  fair_iff.mp hfair ob n fun m hm => ⟨hdue m hm, hquiet m hm⟩

/-- A run that takes every obligation that stays due, a timer that is armed again and again
included. The runtime's runs are not like this: an actor that keeps arming a timer again keeps
it from firing. -/
def Impatient (r : sys.Run env) : Prop :=
  ∀ (ob : Obligation σ) (n : ℕ), (∀ m, n ≤ m → ob.Due env (r.state m)) →
    ∃ m, n ≤ m ∧ r.event m = some ob.event

/-- Fairness asks less than firing every timer that stays pending. -/
theorem Impatient.fair (h : r.Impatient) : r.Fair :=
  fair_iff.mpr fun ob n hdue => h ob n fun m hm => (hdue m hm).1

/-- In a fair run, an emitted output is eventually handed over. -/
theorem Fair.output_taken (hfair : r.Fair) {out : σ.Out} (hout : out ∈ (r.state n).outbox) :
    ∃ m, n ≤ m ∧ r.event m = some (.output out) := by
  by_contra hnever
  refine hnever (hfair.taken (ob := .output out) (fun m hm => ?_) fun _ _ ⟨_, _, h⟩ => h)
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
- `progress`: taking `ob` reaches `Q`;
- `quiet`: no step restarts `ob`, unless it reaches `Q`. Only a timer can be restarted, by a
  step of its actor that arms it, so for any other obligation there is nothing to show and
  the premise is filled in.

Then `P` leads to `Q`: `P` holds until `Q` does, so `ob` stays due and is left to wait, so a
fair run takes it.
-/
theorem ensures_of_invariant (hI : sys.Invariant env I) (ob : Obligation σ)
    (step : ∀ c ev c', I c → P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, I c → P c → ¬Q c → ob.Due env c)
    (progress : ∀ c c', I c → P c → ¬Q c → c.step env ob.event = some c' → Q c')
    (quiet : ∀ c ev c', I c → P c → ¬Q c → c.step env ev = some c' → ob.Restarted c ev → Q c' := by
      never_restarted) :
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
  have hquiet (m : ℕ) (hm : n ≤ m) : ¬r.Restarts m ob := fun ⟨ev, hev, hrestarted⟩ =>
    hQ (m + 1) (by omega)
      (quiet _ ev _ (hI _ (r.reachable m)) (hP m hm) (hQ m hm) (Run.step_some hev) hrestarted)
  obtain ⟨m, hm, hev⟩ := hfair.taken
    (fun m hm => due _ (hI _ (r.reachable m)) (hP m hm) (hQ m hm)) hquiet
  exact hQ (m + 1) (by omega)
    (progress _ _ (hI _ (r.reachable m)) (hP m hm) (hQ m hm) (Run.step_some hev))

/-- The proof rule for leads-to, with no invariant. -/
theorem ensures (ob : Obligation σ)
    (step : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → P c' ∨ Q c')
    (due : ∀ c, P c → ¬Q c → ob.Due env c)
    (progress : ∀ c c', P c → ¬Q c → c.step env ob.event = some c' → Q c')
    (quiet : ∀ c ev c', P c → ¬Q c → c.step env ev = some c' → ob.Restarted c ev → Q c' := by
      never_restarted) :
    sys.LeadsTo env P Q :=
  ensures_of_invariant (I := fun _ => True) (fun _ _ => trivial) ob
    (fun c ev c' _ => step c ev c') (fun c _ => due c) (fun c c' _ => progress c c')
    (fun c ev c' _ => quiet c ev c')

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

/-- What each of a family of starts leads to, their union leads to. -/
theorem exists_left {α : Type*} {P : α → SysState sys → Prop}
    (h : ∀ x, sys.LeadsTo env (P x) Q) : sys.LeadsTo env (fun c => ∃ x, P x c) Q :=
  iff.mpr fun r hfair n ⟨x, hx⟩ => iff.mp (h x) r hfair n hx

/-- Leads-to by a measure that goes down: if `P` with measure `n` leads to `Q`, or to `P` with
a smaller measure, then `P` leads to `Q`. -/
theorem induction (f : SysState sys → ℕ)
    (h : ∀ n, sys.LeadsTo env (fun c => P c ∧ f c = n) fun c => Q c ∨ (P c ∧ f c < n)) :
    sys.LeadsTo env P Q := by
  refine iff.mpr fun r hfair n hP => ?_
  suffices hk : ∀ k n, P (r.state n) → f (r.state n) = k → ∃ m, n ≤ m ∧ Q (r.state m) from
    hk _ n hP rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hP hf
    obtain ⟨m, hm, hQ | ⟨hP', hlt⟩⟩ := iff.mp (h k) r hfair n ⟨hP, hf⟩
    · exact ⟨m, hm, hQ⟩
    · obtain ⟨m', hm', hQ'⟩ := ih _ hlt m hP' rfl
      exact ⟨m', Nat.le_trans hm hm', hQ'⟩

end LeadsTo

end System

end Lanes
