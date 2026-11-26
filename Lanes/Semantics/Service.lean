/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Step
public import Lanes.Behaviours.Server
public import Lanes.Semantics.System
public import Mathlib.Data.Multiset.AddSub

/-!
# Implementing a service

`Service.spec` turns a sequential `Service` into the transition system a concurrent
implementation must refine: inputs arrive and wait, each takes effect atomically at some later
moment, and its outputs wait to be delivered. Arrival and delivery are the visible steps; taking
effect is internal. `System.Implements` is refinement to that spec. For a service of operations
and responses it is linearizability, stated as a refinement.

Waiting inputs and outputs are multisets here: their order is not observable. `Lanes.Check`
runs the same definition on lists (`Service.State`).

## Main definitions

- `Service.Abs`: the state of a service used concurrently, with multisets.
- `Service.spec`: the transition system of a service.
- `System.Implements`: a system refines a service.

## Main statements

- `Server.implements`: a `Server` implements the service it runs, in any faultless environment.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {S : Type}

namespace Service

/-- The state of a service used concurrently. -/
structure Abs (σ : Signature) (S : Type) where
  /-- The state of the sequential spec. -/
  value : S
  /-- Inputs that have arrived and not yet taken effect. -/
  pending : Multiset σ.In
  /-- Outputs produced and not yet delivered. -/
  outbox : Multiset σ.Out

/--
The transition system of a service: an input arrives (visible), a pending input takes effect
(internal), an output is delivered (visible).
-/
def spec (svc : Service σ S) : Spec (Abs σ S) (Option (Visible σ)) where
  init st := st = ⟨svc.init, 0, 0⟩
  Tr st label st' :=
    match label with
    | some (.input x) => st' = { st with pending := x ::ₘ st.pending }
    | some (.output out) => out ∈ st.outbox ∧ st' = { st with outbox := st.outbox.erase out }
    | none => ∃ x ∈ st.pending,
        st' = ⟨(svc.step st.value x).1, st.pending.erase x, st.outbox + (svc.step st.value x).2⟩

/-- `P` survives any pending input taking effect: the spec's internal steps keep it. -/
def Stable (svc : Service σ S) (P : Abs σ S → Prop) : Prop :=
  ∀ a x, x ∈ a.pending → P a →
    P ⟨(svc.step a.value x).1, a.pending.erase x, a.outbox + (svc.step a.value x).2⟩

/-- What every pending input taking effect keeps, any number of internal steps keep. -/
theorem Stable.τSTr {svc : Service σ S} {P : Abs σ S → Prop} (hP : svc.Stable P)
    {a b : Abs σ S} (h : svc.spec.lts.τSTr a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ htr ih =>
    obtain ⟨x, hx, rfl⟩ := htr
    exact hP _ x hx ih

/-- A visible step of the spec, with internal steps around it, from where `P` holds to where `Q`
holds, when both are stable. This is how a trace is followed one label at a time. -/
theorem Stable.sTr {svc : Service σ S} {P Q : Abs σ S → Prop} {e : Visible σ}
    (hP : svc.Stable P) (hQ : svc.Stable Q) (step : ∀ a b, P a → svc.spec.Tr a (some e) b → Q b)
    {a b : Abs σ S} (h : svc.spec.lts.STr a (some e) b) (ha : P a) : Q b := by
  generalize hμ : some e = μ at h
  cases h with
  | refl => cases hμ
  | tr h₁ htr h₂ =>
    subst hμ
    exact hQ.τSTr h₂ (step _ _ (hP.τSTr h₁ ha) htr)

end Service

/--
`sys` implements the service `svc` under `env`: everything a client can observe of the running
system is a behaviour of the service with each input taking effect at one instant.
-/
abbrev System.Implements (sys : System σ) (env : EnvModel σ) (svc : Service σ S) : Prop :=
  sys.Refines env svc.spec

namespace Server

variable {In Out : Type} [DecidableEq In] [DecidableEq Out]

/-- How a server's state reads as a state of its service: the actor's state, the requests in
its mailbox, and the outputs not yet handed over. -/
def abs {svc : Service (sig In Out) S} (c : SysState (system svc)) : Service.Abs (sig In Out) S where
  value := c.state ()
  pending := (c.net.map fun e => (e.msg : In) : List In)
  outbox := (c.outbox : List Out)

/-- What handling a request does: the service's step on the state, its outputs appended. -/
theorem handle_eq (svc : Service (sig In Out) S) (env : EnvModel (sig In Out))
    (c : SysState (system svc)) (x : In) :
    c.handle env () x =
      { c with state := update c.state () (svc.step (c.state ()) x).1
               outbox := c.outbox ++ (svc.step (c.state ()) x).2 } := by
  have h : ∀ s, (actor svc).step s x = ((svc.step s x).1, (svc.step s x).2.map .emit) :=
    fun _ => rfl
  simp only [SysState.handle, SysState.settle, h]
  rw [SysState.any_isStop_emit]
  exact SysState.performAll_emit (sys := system svc) _ _ _

/--
A server implements the service it runs. Concurrent clients of `Server.system svc` observe
exactly the behaviours of `svc` applied one request at a time, in any environment that loses,
duplicates and crashes nothing.
-/
theorem implements (svc : Service (sig In Out) S) (env : EnvModel (sig In Out))
    (henv : env.Faultless) : (system svc).Implements env svc := by
  refine Refines.of_map abs (fun c => c.timers () = []) ?_ ?_ ?_
  · rintro c rfl
    exact ⟨rfl, rfl⟩
  · -- No step arms a timer.
    intro c ev c' hinv hstep
    cases ev with
    | input x => obtain rfl := SysState.step_input.mp hstep; exact hinv
    | deliver e =>
      obtain ⟨src, ⟨⟩, msg⟩ := e
      obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
      rw [handle_eq]
      exact hinv
    | duplicate e =>
      obtain ⟨_, hdup, _⟩ := SysState.step_duplicate.mp hstep
      simp [henv.noDuplicates] at hdup
    | drop e =>
      obtain ⟨hlossy, _⟩ := SysState.step_drop.mp hstep
      simp [henv.lossless] at hlossy
    | timeout i msg =>
      obtain ⟨_, hpending, _⟩ := SysState.step_timeout.mp hstep
      simp [hinv] at hpending
    | output out => obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep; exact hinv
    | crash i =>
      obtain ⟨_, hcrash, _⟩ := SysState.step_crash.mp hstep
      simp [henv.noCrashes] at hcrash
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      simpa [SysState.startActor, SysState.settle, actor] using hinv
  · intro c ev c' hinv hstep
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      refine .inr ?_
      simp [Event.visible, Service.spec, abs, ← Multiset.coe_add, add_comm]
    | deliver e =>
      obtain ⟨_, hdeliverable, rfl⟩ := SysState.step_deliver.mp hstep
      have hmem := SysState.mem_of_deliverable hdeliverable
      obtain ⟨src, ⟨⟩, msg⟩ := e
      refine .inr ⟨msg, ?_, ?_⟩
      · exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨_, hmem, rfl⟩)
      · rw [handle_eq]
        simp only [abs, update_self, Service.Abs.mk.injEq, true_and]
        refine ⟨?_, by simp⟩
        rw [← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.coe_erase]
        exact Multiset.map_erase_of_mem _ _ (Multiset.mem_coe.mpr hmem)
    | duplicate e =>
      obtain ⟨_, hdup, _⟩ := SysState.step_duplicate.mp hstep
      simp [henv.noDuplicates] at hdup
    | drop e =>
      obtain ⟨hlossy, _⟩ := SysState.step_drop.mp hstep
      simp [henv.lossless] at hlossy
    | timeout i msg =>
      obtain ⟨_, hpending, _⟩ := SysState.step_timeout.mp hstep
      simp [hinv] at hpending
    | output out =>
      obtain ⟨hmem, rfl⟩ := SysState.step_output.mp hstep
      refine .inr ?_
      simp [Event.visible, Service.spec, abs, hmem]
    | crash i =>
      obtain ⟨_, hcrash, _⟩ := SysState.step_crash.mp hstep
      simp [henv.noCrashes] at hcrash
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      refine .inl ⟨rfl, ?_⟩
      simp [abs, SysState.startActor, SysState.settle, actor]

end Server

end Lanes
