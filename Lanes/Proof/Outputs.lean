/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Proof.Monotone

/-!
# What a system hands to the outside

An output handed to the outside world is one an actor emitted. So what holds of every output
each step and each start may emit holds of every output in every run, under every environment
model. A model of something outside (`Outside`) that is shown to behave whenever the outputs it
sees are of some form is then shown to behave beside the system (`Outside.after_invariant`).
-/

@[expose] public section

namespace Lanes.System

variable {σ : Signature} {sys : System σ}

/-- Every output an actor's step or start emits is one `good` admits. -/
def Emits (sys : System σ) (good : σ.Out → Prop) : Prop :=
  (∀ i s msg out, Effect.emit out ∈ ((sys.actor i).step s msg).2 → good out) ∧
    ∀ i s out, Effect.emit out ∈ ((sys.actor i).recover s).2 → good out

theorem Emits.outbox {good : σ.Out → Prop} (h : sys.Emits good) :
    sys.Monotone fun c => ∀ out ∈ c.outbox, good out where
  blank := by simp [SysState.blank]
  below _ _ hc hbelow out hout := hc out (hbelow.outbox out hout)
  input c _ hc := hc
  step c i msg hc _ out hout := by
    simp only [SysState.grow, List.mem_append] at hout
    exact hout.elim (hc out) fun hout => h.1 i _ msg out (Effect.mem_emits.mp hout)
  recover c i hc out hout := by
    simp only [SysState.grow, List.mem_append] at hout
    exact hout.elim (hc out) fun hout => h.2 i _ out (Effect.mem_emits.mp hout)

/-- Every output of a run is one `good` admits, if every output an actor emits is. -/
theorem Emits.outputs {good : σ.Out → Prop} (h : sys.Emits good) {env : EnvModel σ}
    {events : List (Event σ)} {c : SysState sys}
    (hrun : (SysState.init sys env).run env events = some c) :
    ∀ out, Event.output out ∈ events → good out := by
  have hinv := (h.outbox.invariant env)
  refine Reachable.run_induction (P := fun events _ => ∀ out, Event.output out ∈ events → good out)
    .init hrun (by simp) ?_
  intro evs c₁ ev c₂ hc₁ hP hstep out hout
  rcases List.mem_append.mp hout with hout | hout
  · exact hP out hout
  · simp only [List.mem_singleton] at hout
    subst hout
    exact hinv c₁ hc₁ out (SysState.step_output.mp hstep).1

end Lanes.System
