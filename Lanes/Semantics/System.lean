/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Lift
public import Lanes.Semantics.Refinement

/-!
# The semantics of a system as a transition system

`System.sem sys env` presents `SysState.step` as a `Spec`, and so as a CSLib `LTS`: states are
`SysState sys`, labels are `Event σ`, and there is a transition exactly when the step function
returns the target state. Nothing is redefined here. Proofs are about the function that the
scheduler and the model checker run.

## Main definitions

- `System.sem`: the semantics of a system under an environment model.
- `System.Refines`: a system refines a service spec whose labels are the system's visible events.

## Main statements

- `System.reachable_iff`: reachability through `SysState.step` and reachability in the `LTS`
  agree.
- `System.sem_deterministic`: an event determines the next state.
-/

@[expose] public section

namespace Lanes

open Cslib

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

/--
`sys` refines `spec` under `env`: everything the outside world can observe of the running system
is allowed by the spec. Inputs and outputs are the visible labels; deliveries, timeouts, crashes
and restarts are internal.
-/
abbrev Refines {S : Type} (sys : System σ) (env : EnvModel σ)
    (spec : Spec S (Option (Visible σ))) : Prop :=
  Lanes.Refines (sys.sem env) spec Event.visible

end System

end Lanes
