/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Step
public import Lanes.Behaviours.Server
public import Lanes.Semantics.System
public import Lanes.Semantics.Bag

/-!
# Implementing a service

`Service.spec` turns a sequential `Service` into the transition system a concurrent
implementation must refine: inputs arrive and wait, each takes effect atomically at some later
moment, and its outputs wait to be delivered. Arrival and delivery are the visible steps; taking
effect is internal. A deadline passing is visible too, and takes effect at that moment, so a
pending input may take effect before or after it. `System.Implements` is refinement to that
spec, with the system's timers that are the deadlines firing them. For a service of operations
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

variable {In Out S T : Type} [DecidableEq In] [DecidableEq Out]

namespace Service

/-- The state of a service used concurrently. -/
structure Abs (In Out S : Type) where
  /-- The state of the sequential spec. -/
  value : S
  /-- Inputs that have arrived and not yet taken effect. -/
  pending : Bag In
  /-- Outputs produced and not yet delivered. -/
  outbox : Bag Out

/--
The transition system of a service: an input arrives (visible), a pending input takes effect
(internal), an output is delivered (visible), an armed deadline passes (visible).
-/
def spec (svc : Service In Out S T) : Spec (Abs In Out S) (Option (Visible In Out T)) where
  init st := st = ⟨svc.init, 0, 0⟩
  Tr st label st' :=
    match label with
    | some (.input x) => st' = { st with pending := x ::ₘ st.pending }
    | some (.output out) => out ∈ st.outbox ∧ st' = { st with outbox := st.outbox.erase out }
    | some (.fire t) => svc.armed st.value t = true ∧
        st' = ⟨(svc.fire st.value t).1, st.pending, st.outbox + (svc.fire st.value t).2⟩
    | none => ∃ x ∈ st.pending,
        st' = ⟨(svc.step st.value x).1, st.pending.erase x, st.outbox + (svc.step st.value x).2⟩

/-- `P` survives any pending input taking effect: the spec's internal steps keep it. -/
def Stable (svc : Service In Out S T) (P : Abs In Out S → Prop) : Prop :=
  ∀ a x, x ∈ a.pending → P a →
    P ⟨(svc.step a.value x).1, a.pending.erase x, a.outbox + (svc.step a.value x).2⟩

/-- What every pending input taking effect keeps, any number of internal steps keep. -/
theorem Stable.τSTr {svc : Service In Out S T} {P : Abs In Out S → Prop} (hP : svc.Stable P)
    {a b : Abs In Out S} (h : svc.spec.lts.τSTr a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ htr ih =>
    obtain ⟨x, hx, rfl⟩ := htr
    exact hP _ x hx ih

/-- A visible step of the spec, with internal steps around it, from where `P` holds to where `Q`
holds, when both are stable. This is how a trace is followed one label at a time. -/
theorem Stable.sTr {svc : Service In Out S T} {P Q : Abs In Out S → Prop} {e : Visible In Out T}
    (hP : svc.Stable P) (hQ : svc.Stable Q) (step : ∀ a b, P a → svc.spec.Tr a (some e) b → Q b)
    {a b : Abs In Out S} (h : svc.spec.lts.STr a (some e) b) (ha : P a) : Q b := by
  generalize hμ : some e = μ at h
  cases h with
  | refl => cases hμ
  | tr h₁ htr h₂ =>
    subst hμ
    exact hQ.τSTr h₂ (step _ _ (hP.τSTr h₁ ha) htr)

/-- Every pending input is one of `A`, the value one of `V`, and every output waiting one of
`O`: what a trace argument follows the spec with, between two visible steps. -/
def Only (A : In → Prop) (V : S → Prop) (O : Out → Prop) (a : Abs In Out S) : Prop :=
  (∀ x ∈ a.pending, A x) ∧ V a.value ∧ ∀ o ∈ a.outbox, O o

omit [DecidableEq Out] in
/-- `Only` is stable when every input of `A` keeps `V` and outputs only `O`. -/
theorem Only.stable {svc : Service In Out S T} {A : In → Prop} {V : S → Prop} {O : Out → Prop}
    (h : ∀ v x, A x → V v → V (svc.step v x).1 ∧ ∀ o ∈ (svc.step v x).2, O o) :
    svc.Stable (Only A V O) := by
  rintro a x hx ⟨hpending, hvalue, houtbox⟩
  obtain ⟨hvalue', houtbox'⟩ := h a.value x (hpending x hx) hvalue
  refine ⟨fun y hy => hpending y (Bag.mem_of_mem_erase hy), hvalue', fun o ho => ?_⟩
  rcases Bag.mem_add.mp ho with ho | ho
  · exact houtbox o ho
  · exact houtbox' o ho

/-- An output carrying `x₀`'s id (`oid o = id x₀`) waits only once `x₀` has taken effect:
`x₀` is then no longer pending, if it arrived at most once, and `V`, which it establishes,
holds. -/
def Took {K : Type} (id : In → K) (oid : Out → K) (x₀ : In) (V : S → Prop)
    (a : Abs In Out S) : Prop :=
  a.pending.count x₀ ≤ 1 ∧ ∀ o ∈ a.outbox, oid o = id x₀ → x₀ ∉ a.pending ∧ V a.value

omit [DecidableEq Out] in
/-- `Took` is stable, with `Only` beside it, when every output carries the id of the input that
produced it, `x₀` is the only input of `A` with its id, `x₀` establishes `V`, and every other
input of `A` keeps it. -/
theorem Took.stable {svc : Service In Out S T} {K : Type} {id : In → K} {oid : Out → K}
    {A : In → Prop} {W : S → Prop} {O : Out → Prop} {x₀ : In} {V : S → Prop}
    (hOnly : ∀ v x, A x → W v → W (svc.step v x).1 ∧ ∀ o ∈ (svc.step v x).2, O o)
    (hid : ∀ v x, ∀ o ∈ (svc.step v x).2, oid o = id x) (hA : ∀ x, A x → id x = id x₀ → x = x₀)
    (h₀ : ∀ v, V (svc.step v x₀).1) (hkeep : ∀ v x, A x → x ≠ x₀ → V v → V (svc.step v x).1) :
    svc.Stable fun a => Only A W O a ∧ Took id oid x₀ V a := by
  rintro a x hx ⟨honly, hcount, htook⟩
  refine ⟨Only.stable hOnly a x hx honly,
    Nat.le_trans (Bag.count_le_of_le _ (Bag.erase_le _ _)) hcount, fun o ho hid₀ => ?_⟩
  have hgone : x₀ ∉ a.pending.erase x₀ := by
    rw [← Bag.count_eq_zero, Bag.count_erase_self]
    omega
  rcases Bag.mem_add.mp ho with ho | ho
  · obtain ⟨hnot, hvalue⟩ := htook o ho hid₀
    have hne : x ≠ x₀ := fun h => hnot (h ▸ hx)
    exact ⟨fun h => hnot (Bag.mem_of_mem_erase h), hkeep _ x (honly.1 x hx) hne hvalue⟩
  · obtain rfl := hA x (honly.1 x hx) ((hid _ x o ho).symm.trans hid₀)
    exact ⟨hgone, h₀ _⟩

end Service

/--
`sys` implements the service `svc` under `env`: everything a client can observe of the running
system is a behaviour of the service with each input taking effect at one instant, each
timer `deadlines` names passing that deadline as it fires, and each message `delivered` names
passing it as it is handled.
-/
abbrev System.Implements {σ : Signature} (sys : System σ) (env : EnvModel σ)
    (svc : Service σ.In σ.Out S T) (deadlines : Deadlines σ T := fun _ _ => none)
    (delivered : Deadlines σ T := fun _ _ => none) : Prop :=
  sys.Refines env svc.spec deadlines delivered

namespace Server

/-- How a server's state reads as a state of its service: the actor's state, the requests in
its mailbox, and the outputs not yet handed over. -/
def abs {svc : Service In Out S} (c : SysState (system svc)) : Service.Abs In Out S where
  value := c.state ()
  pending := (c.net.map fun e => (e.msg : In) : List In)
  outbox := (c.outbox : List Out)

/-- What handling a request does: the service's step on the state, its outputs appended. -/
theorem handle_eq (svc : Service In Out S) (env : EnvModel (sig In Out))
    (c : SysState (system svc)) (x : In) (src : Sender Unit) :
    c.handle env () x src =
      { c with state := update c.state () (svc.step (c.state ()) x).1
               outbox := c.outbox ++ (svc.step (c.state ()) x).2 } := by
  have h : ∀ ctx s, (actor svc).stepAt ctx s x =
      ((svc.step s x).1, (svc.step s x).2.map (Effect.emit (σ := sig In Out))) :=
    fun _ _ => rfl
  simp only [SysState.handle, SysState.settle, h]
  rw [SysState.any_isStop_emit]
  exact SysState.performAll_emit (sys := system svc) _ _ _

/--
A server implements the service it runs. Concurrent clients of `Server.system svc` observe
exactly the behaviours of `svc` applied one request at a time, in any environment that loses,
duplicates, crashes and restarts nothing. A restart would not: the server's state goes back to
`svc.init` while the spec's does not.
-/
theorem implements (svc : Service In Out S) (env : EnvModel (sig In Out))
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
    | restart =>
      obtain ⟨hmay, -⟩ := SysState.step_restart.mp hstep
      simp [henv.noRestarts] at hmay
    | tick m => obtain rfl := SysState.step_tick.mp hstep; exact hinv
  · intro c ev c' hinv hstep
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      refine .inr ?_
      simp [Service.spec, abs, ← Bag.coe_add, Bag.add_comm]
    | deliver e =>
      obtain ⟨_, hdeliverable, rfl⟩ := SysState.step_deliver.mp hstep
      have hmem := SysState.mem_of_deliverable hdeliverable
      obtain ⟨src, ⟨⟩, msg⟩ := e
      refine .inr ⟨msg, ?_, ?_⟩
      · exact Bag.mem_coe.mpr (List.mem_map.mpr ⟨_, hmem, rfl⟩)
      · rw [handle_eq]
        simp only [abs, update_self, Service.Abs.mk.injEq, true_and]
        refine ⟨?_, by simp⟩
        rw [← Bag.map_coe, ← Bag.map_coe, ← Bag.coe_erase]
        exact Bag.map_erase_of_mem _ _ (Bag.mem_coe.mpr hmem)
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
      simp [Service.spec, abs, hmem]
    | crash i =>
      obtain ⟨_, hcrash, _⟩ := SysState.step_crash.mp hstep
      simp [henv.noCrashes] at hcrash
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      refine .inl ⟨rfl, ?_⟩
      simp [abs, SysState.startActor, SysState.settle, actor]
    | restart =>
      obtain ⟨hmay, -⟩ := SysState.step_restart.mp hstep
      simp [henv.noRestarts] at hmay
    | tick m =>
      obtain rfl := SysState.step_tick.mp hstep
      exact .inl ⟨rfl, rfl⟩

end Server

end Lanes
