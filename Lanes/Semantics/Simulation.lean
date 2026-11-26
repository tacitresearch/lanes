/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Ghost
public import Lanes.Actors.Loses
public import Lanes.Semantics.System

/-!
# Refinement by a relation

`Refines.of_map` asks for a function from implementation states to spec states and one spec
step for each implementation step. A replicated system offers neither. What its spec state is
depends on what was observed before (a request that was lost is still one the spec may serve),
and one step of one node can make several requests take effect at once.

`Refines` itself allows both: it asks for a relation, and answers a step with any number of
internal steps of the spec. The rules here make that usable for a `System`.

## Main statements

- `Refines.of_invariant`: refinement from a relation, with a proved invariant of the
  implementation available at both ends of every step.
- `Refines.of_lift`: refinement carried back along a function that loses state the steps do not
  read.
- `System.Refines.of_ghost`: what a system with ghosts refines, the system without them refines.
- `System.Refines.of_steps`: refinement of a system in the cases of `Inductive.of_monotone`,
  for a relation that losing messages and timers cannot break.
- `System.Refines.of_handles`: the same with handling a message as one case, whether the message
  stays in flight or not, in every environment.
-/

@[expose] public section

namespace Lanes

open Cslib

universe u v w

variable {S₁ : Type u} {S₁' : Type w} {S₂ : Type v} {L₁ L₂ : Type*}

namespace Refines

/--
Refinement from a relation and an invariant. The relation holds initially, and every step of
`impl` between two states where `inv` holds is answered by a saturated step of `spec`: the same
visible label with internal steps around it, or internal steps alone for an internal label.
-/
theorem of_invariant [HasTau L₂] {impl : Spec S₁ L₁} {spec : Spec S₂ L₂} {f : L₁ → L₂}
    {inv : S₁ → Prop} (hinv : impl.Invariant inv) (rel : S₁ → S₂ → Prop)
    (init : ∀ s, impl.init s → ∃ t, spec.init t ∧ rel s t)
    (step : ∀ s t μ s', inv s → inv s' → rel s t → impl.Tr s μ s' →
      ∃ t', spec.lts.STr t (f μ) t' ∧ rel s' t') :
    Refines impl spec f := by
  refine ⟨fun s t => impl.Reachable s ∧ rel s t, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, hrel⟩ := init s hs
    exact ⟨t, ht, .init hs, hrel⟩
  · rintro s t ⟨hreach, hrel⟩ μ s' htr
    have hreach' := hreach.step htr
    obtain ⟨t', ht', hrel'⟩ := step s t μ s' (hinv s hreach) (hinv s' hreach') hrel htr
    exact ⟨t', ht', hreach', hrel'⟩

/--
Refinement carried back along `erase`. If `impl'` is `impl` with more state, in that every
initial state and every step of `impl` is the image of one of `impl'`, then what `impl'` refines,
`impl` refines.
-/
theorem of_lift [HasTau L₂] {impl : Spec S₁ L₁} {impl' : Spec S₁' L₁} {spec : Spec S₂ L₂}
    {f : L₁ → L₂} (erase : S₁' → S₁)
    (init : ∀ s, impl.init s → ∃ s', impl'.init s' ∧ erase s' = s)
    (lift : ∀ s' μ s₂, impl.Tr (erase s') μ s₂ → ∃ s₂', impl'.Tr s' μ s₂' ∧ erase s₂' = s₂)
    (h : Refines impl' spec f) : Refines impl spec f := by
  obtain ⟨rel, hinit, hstep⟩ := h
  refine ⟨fun s t => ∃ s', erase s' = s ∧ rel s' t, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := init s hs
    obtain ⟨t, ht, hrel⟩ := hinit s' hs'
    exact ⟨t, ht, s', rfl, hrel⟩
  · rintro _ t ⟨s', rfl, hrel⟩ μ s₂ htr
    obtain ⟨s₂', htr', rfl⟩ := lift s' μ s₂ htr
    obtain ⟨t', ht', hrel'⟩ := hstep s' t hrel μ s₂' htr'
    exact ⟨t', ht', s₂', rfl, hrel'⟩

end Refines

variable {σ : Signature} {sys : System σ} {env : EnvModel σ} {S : Type}
  {spec : Spec S (Option (Visible σ))}

namespace System

/--
Ghosts do not change what a system refines. A simulation may therefore be built on the system
with ghosts, where the invariants that read the past are stated, and its conclusion is about
the system that runs.
-/
theorem Refines.of_ghost (g : Ghost sys) (h : (sys.withGhost g).Refines env spec) :
    sys.Refines env spec := by
  refine Lanes.Refines.of_lift SysState.erase ?_ ?_ h
  · rintro _ rfl
    exact ⟨_, rfl, SysState.erase_init sys g env⟩
  · intro c ev c' hstep
    have hmap : (c.step env ev).map SysState.erase = some c' :=
      (SysState.erase_step env c ev).trans hstep
    obtain ⟨c'', hstep', rfl⟩ := Option.map_eq_some_iff.mp hmap
    exact ⟨c'', hstep', rfl⟩

/-- A system with ghosts refines what the system without them refines. -/
theorem Refines.to_ghost (g : Ghost sys) (h : sys.Refines env spec) :
    (sys.withGhost g).Refines env spec := by
  obtain ⟨rel, hinit, hstep⟩ := h
  refine ⟨fun c t => rel c.erase t, ?_, ?_⟩
  · rintro _ rfl
    obtain ⟨t, ht, hrel⟩ := hinit _ rfl
    refine ⟨t, ht, ?_⟩
    show rel (SysState.init (sys.withGhost g) env).erase t
    rwa [SysState.erase_init]
  · intro c t hrel ev c' htr
    have htr' : c.erase.step env ev = some c'.erase := by
      rw [← SysState.erase_step, show c.step env ev = some c' from htr]
      rfl
    exact hstep c.erase t hrel ev c'.erase htr'

/--
Refinement of a system, for a relation that losing messages and timers cannot break (`loses`).
What is left to show is that the relation holds initially, that an input and an output handed
over are answered by the same visible step of the spec, and that an actor handling a message or
recovering, with nothing lost, is answered by internal steps of the spec. The invariant `inv` is
available where each step starts.

A message delivered leaves the network before it is handled; one handled a second time stays;
a timer that fires may be taken to stay, since losing it afterwards is `loses`.
-/
theorem Refines.of_steps {inv : SysState sys → Prop} (hinv : sys.Invariant env inv)
    (rel : SysState sys → S → Prop)
    (init : ∃ t, spec.init t ∧ rel (SysState.init sys env) t)
    (loses : ∀ c c' t, rel c t → c'.Loses c → rel c' t)
    (input : ∀ c t x, inv c → rel c t → ∃ t', spec.lts.STr t (some (.input x)) t' ∧
      rel { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] } t')
    (output : ∀ c t out, inv c → rel c t → out ∈ c.outbox →
      ∃ t', spec.lts.STr t (some (.output out)) t' ∧
        rel { c with outbox := c.outbox.erase out } t')
    (deliver : ∀ c t e, inv c → rel c t → e ∈ c.net → ∃ t', spec.lts.τSTr t t' ∧
      rel (({ c with net := c.net.erase e }).grow e.dst
        ((sys.actor e.dst).step (c.state e.dst) e.msg)) t')
    (duplicate : ∀ c t e, inv c → rel c t → e ∈ c.net →
      (env.link e.src e.dst).duplicating = true → ∃ t', spec.lts.τSTr t t' ∧
        rel (c.grow e.dst ((sys.actor e.dst).step (c.state e.dst) e.msg)) t')
    (timeout : ∀ c t i msg, inv c → rel c t → msg ∈ c.timers i → ∃ t', spec.lts.τSTr t t' ∧
      rel (c.grow i ((sys.actor i).step (c.state i) msg)) t')
    (recover : ∀ c t i, inv c → rel c t → ∃ t', spec.lts.τSTr t t' ∧
      rel (c.grow i ((sys.actor i).recover (c.state i))) t') :
    sys.Refines env spec := by
  refine Lanes.Refines.of_invariant (invariant_iff.mp hinv) rel ?_ ?_
  · rintro _ rfl
    exact init
  intro c t ev c' hc _ hrel hstep
  have internal : ∀ {t'}, spec.lts.τSTr t t' → spec.lts.STr t HasTau.τ t' :=
    (LTS.sTr_τSTr_iff spec.lts).mpr
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    exact input c t x hc hrel
  | deliver e =>
    obtain ⟨_, hdeliverable, rfl⟩ := SysState.step_deliver.mp hstep
    obtain ⟨t', ht', hrel'⟩ := deliver c t e hc hrel (SysState.mem_of_deliverable hdeliverable)
    exact ⟨t', internal ht', loses _ _ t' hrel' (SysState.Loses.handle (.refl _) ..)⟩
  | duplicate e =>
    obtain ⟨_, hdup, hdeliverable, rfl⟩ := SysState.step_duplicate.mp hstep
    obtain ⟨t', ht', hrel'⟩ :=
      duplicate c t e hc hrel (SysState.mem_of_deliverable hdeliverable) hdup
    exact ⟨t', internal ht', loses _ _ t' hrel' (SysState.Loses.handle (.refl _) ..)⟩
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact ⟨t, .refl, loses _ _ t hrel ⟨rfl, List.erase_sublist, fun _ _ h => h, rfl⟩⟩
  | timeout i msg =>
    obtain ⟨_, hmem, rfl⟩ := SysState.step_timeout.mp hstep
    obtain ⟨t', ht', hrel'⟩ := timeout c t i msg hc hrel hmem
    have hlost : SysState.Loses
        { c with timers := update c.timers i ((c.timers i).erase msg) } c := by
      refine ⟨rfl, List.Sublist.refl _, fun j m hm => ?_, rfl⟩
      by_cases hj : j = i
      · subst hj
        simp only [update_self] at hm
        exact List.mem_of_mem_erase hm
      · simpa [hj] using hm
    exact ⟨t', internal ht', loses _ _ t' hrel' (SysState.Loses.handle hlost ..)⟩
  | output out =>
    obtain ⟨hmem, rfl⟩ := SysState.step_output.mp hstep
    exact output c t out hc hrel hmem
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    exact ⟨t, .refl, loses _ _ t hrel (SysState.Loses.down env c i)⟩
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    obtain ⟨t', ht', hrel'⟩ := recover c t i hc hrel
    exact ⟨t', internal ht', loses _ _ t' hrel' (SysState.Loses.startActor c env i)⟩

/--
`of_steps` with a delivery, a duplicate and a timeout as one case: an actor handles a message in
flight or a timer armed, with any part of the network left (`net`). A relation that reads
messages in flight as a set proves this as easily for the message kept as for the message
taken, and the statement then holds in every environment, whatever the links duplicate.
-/
theorem Refines.of_handles {inv : SysState sys → Prop} (hinv : sys.Invariant env inv)
    (rel : SysState sys → S → Prop)
    (init : ∃ t, spec.init t ∧ rel (SysState.init sys env) t)
    (loses : ∀ c c' t, rel c t → c'.Loses c → rel c' t)
    (input : ∀ c t x, inv c → rel c t → ∃ t', spec.lts.STr t (some (.input x)) t' ∧
      rel { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] } t')
    (output : ∀ c t out, inv c → rel c t → out ∈ c.outbox →
      ∃ t', spec.lts.STr t (some (.output out)) t' ∧
        rel { c with outbox := c.outbox.erase out } t')
    (handle : ∀ c t (net : List (Envelope σ)) i (msg : σ.Msg i), inv c → rel c t →
      net.Sublist c.net → ((∃ src, (⟨src, i, msg⟩ : Envelope σ) ∈ c.net) ∨ msg ∈ c.timers i) →
      ∃ t', spec.lts.τSTr t t' ∧
        rel (({ c with net }).grow i ((sys.actor i).step (c.state i) msg)) t')
    (recover : ∀ c t i, inv c → rel c t → ∃ t', spec.lts.τSTr t t' ∧
      rel (c.grow i ((sys.actor i).recover (c.state i))) t') :
    sys.Refines env spec :=
  Refines.of_steps hinv rel init loses input output
    (fun c t e hc h he => handle c t _ e.dst e.msg hc h List.erase_sublist (.inl ⟨e.src, he⟩))
    (fun c t e hc h he _ => handle c t c.net e.dst e.msg hc h (.refl _) (.inl ⟨e.src, he⟩))
    (fun c t i msg hc h hm => handle c t c.net i msg hc h (.refl _) (.inr hm))
    recover

end System

end Lanes
