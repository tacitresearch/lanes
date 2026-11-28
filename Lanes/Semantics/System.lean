/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.Lift
public import Lanes.Semantics.Refinement

/-!
# The semantics of a system as a transition system

`System.sem sys env` presents `SysState.step` as a `Spec`, and so as an `LTS`: states are
`SysState sys`, labels are `Event σ`, and there is a transition exactly when the step function
returns the target state. Nothing is redefined here. Proofs are about the function that the
scheduler and the model checker run.

## Main definitions

- `System.sem`: the semantics of a system under an environment model.
- `System.Refines`: a system refines a spec whose labels are the system's visible events.

## Main statements

- `System.reachable_iff`: reachability through `SysState.step` and reachability in the `LTS`
  agree.
- `System.sem_deterministic`: an event determines the next state.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace System

/-- The semantics of `sys` under `env`: the freshly booted state, and one transition for every
enabled event. -/
def sem (sys : System σ) (env : EnvModel σ) : Spec (SysState sys) (Event σ) where
  init c := c = SysState.init sys env
  Tr c ev c' := c.step env ev = some c'

variable {sys : System σ} {env : EnvModel σ}

/-- An event determines the next state: all nondeterminism is in which event happens. -/
theorem sem_deterministic {c c₁ c₂ : SysState sys} {ev : Event σ}
    (h₁ : (sys.sem env).Tr c ev c₁) (h₂ : (sys.sem env).Tr c ev c₂) : c₁ = c₂ :=
  Option.some.inj (h₁.symm.trans h₂)

/-- A state is reachable through `SysState.step` exactly when it is reachable in the `LTS`. -/
theorem reachable_iff {c : SysState sys} : sys.Reachable env c ↔ (sys.sem env).Reachable c := by
  constructor
  · intro h
    induction h with
    | init => exact Spec.Reachable.init rfl
    | step ev _ hstep ih => exact ih.step hstep
  · rintro ⟨c₀, rfl, μs, hμs⟩
    suffices h : ∀ c₀, sys.Reachable env c₀ → (sys.sem env).lts.MTr c₀ μs c →
        sys.Reachable env c from h _ .init hμs
    clear hμs
    intro c₀ h₀ hμs
    induction hμs with
    | refl => exact h₀
    | stepL htr _ ih => exact ih (.step _ h₀ htr)

/-- Invariants of the system are invariants of its semantics. -/
theorem invariant_iff {P : SysState sys → Prop} :
    sys.Invariant env P ↔ (sys.sem env).Invariant P :=
  ⟨fun h c hc => h c (reachable_iff.mpr hc), fun h c hc => h c (reachable_iff.mp hc)⟩

/-- A run of the step function is a run of the semantics with the same events. -/
theorem mTr_of_run {c c' : SysState sys} {evs : List (Event σ)} (h : c.run env evs = some c') :
    (sys.sem env).lts.MTr c evs c' := by
  induction evs generalizing c with
  | nil => exact (Option.some.inj h) ▸ .refl
  | cons ev evs ih =>
    simp only [SysState.run] at h
    cases hstep : c.step env ev with
    | none => simp [hstep] at h
    | some c₁ => exact .stepL hstep (ih (by simpa [hstep] using h))

/--
`sys` refines `spec` under `env`: everything the outside world can observe of the running system
is allowed by the spec. Inputs and outputs are visible, and so are the timers `deadlines` names
and the deliveries `delivered` names, each passing the deadline of the spec it is; other
deliveries and timeouts, crashes and restarts are internal.
-/
abbrev Refines {S T : Type} (sys : System σ) (env : EnvModel σ)
    (spec : Spec S (Option (Visible σ.In σ.Out T)))
    (deadlines : Deadlines σ T := fun _ _ => none)
    (delivered : Deadlines σ T := fun _ _ => none) : Prop :=
  Lanes.Refines (sys.sem env) spec (Event.timed deadlines delivered)

/-- The visible events of a run from the initial state, in order, are a trace of what the
system refines. Shown a run whose trace the spec does not have, a system does not refine it. -/
theorem Refines.traces_of_run {S T : Type} {spec : Spec S (Option (Visible σ.In σ.Out T))}
    {deadlines delivered : Deadlines σ T} (h : sys.Refines env spec deadlines delivered)
    {evs : List (Event σ)} {c : SysState sys}
    (hrun : (SysState.init sys env).run env evs = some c) :
    ∃ t t', spec.init t ∧
      spec.lts.SMTr t ((evs.filterMap (Event.timed deadlines delivered)).map some) t' := by
  have hlabels : ∀ evs : List (Event σ),
      (evs.map (Event.timed deadlines delivered)).filter (· ≠ HasTau.τ) =
        (evs.filterMap (Event.timed deadlines delivered)).map some := by
    intro evs
    induction evs with
    | nil => rfl
    | cons ev evs ih =>
      cases hv : ev.timed deadlines delivered <;> simp_all [HasTau.τ]
  rw [← hlabels]
  exact Lanes.Refines.traces h rfl (mTr_of_run hrun)

end System

end Lanes
