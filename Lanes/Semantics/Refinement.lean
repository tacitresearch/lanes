/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Semantics.Lts

/-!
# Specs and refinement

A `Spec` is a labelled transition system with initial states. It is the form of everything Lanes
relates by refinement: a service spec, a protocol model, and the semantics of a running system.

`Refines impl spec f` says that `impl` implements `spec` when each `impl` label `μ` is read as
the `spec` label `f μ`. It is a weak forward simulation: every step of `impl` is matched by the
same visible step of `spec`, surrounded by any number of internal (`τ`) steps of `spec`, and a
step that `f` maps to `τ` may be matched by no step at all. That last case is stuttering.

`Lanes.Semantics.Lts` provides the transition systems (`LTS`), internal steps (`HasTau`) and
saturated transitions (`LTS.STr`). The one-directional weak simulation with a label map is
defined here on top of `LTS.STr`.

## Main definitions

- `Spec State Label`: an `LTS` with initial states.
- `Refines impl spec f`: `impl` refines `spec` along the label map `f`.

## Main statements

- `Refines.of_map`: refinement from a refinement mapping (a function on states) and an invariant.
- `Refines.trans`: refinements compose, so `impl → model → spec` gives `impl → spec`.
- `Refines.traces`: every observable behaviour of `impl` is an observable behaviour of `spec`.
-/

@[expose] public section

namespace Lanes

universe u v w u₁ u₂ u₃

/-- A labelled transition system with initial states. -/
structure Spec (State : Type u) (Label : Type v) where
  /-- Whether a state is initial. -/
  init : State → Prop
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

namespace Spec

variable {State : Type u} {Label : Type v}

/-- The underlying transition system. -/
def lts (spec : Spec State Label) : LTS State Label where
  Tr := spec.Tr

/-- The states a spec can reach from an initial state. -/
def Reachable (spec : Spec State Label) (s : State) : Prop :=
  ∃ s₀, spec.init s₀ ∧ spec.lts.CanReach s₀ s

/-- `P` holds in every reachable state. -/
def Invariant (spec : Spec State Label) (P : State → Prop) : Prop :=
  ∀ s, spec.Reachable s → P s

theorem Reachable.init {spec : Spec State Label} {s : State} (h : spec.init s) :
    spec.Reachable s :=
  ⟨s, h, LTS.CanReach.refl _ s⟩

theorem Reachable.step {spec : Spec State Label} {s s' : State} {μ : Label}
    (hs : spec.Reachable s) (htr : spec.Tr s μ s') : spec.Reachable s' := by
  obtain ⟨s₀, h₀, μs, hμs⟩ := hs
  exact ⟨s₀, h₀, μs ++ [μ], LTS.MTr.stepR spec.lts hμs htr⟩

/-- Prove an invariant by induction: it holds initially and every transition preserves it. -/
theorem invariant_of_inductive {spec : Spec State Label} {P : State → Prop}
    (init : ∀ s, spec.init s → P s) (step : ∀ s μ s', P s → spec.Tr s μ s' → P s') :
    spec.Invariant P := by
  rintro s ⟨s₀, h₀, μs, hμs⟩
  have h : P s₀ := init s₀ h₀
  clear h₀
  induction hμs with
  | refl => exact h
  | stepL htr _ ih => exact ih (step _ _ _ h htr)

end Spec

variable {S₁ : Type u} {S₂ : Type v} {S₃ : Type w} {L₁ : Type u₁} {L₂ : Type u₂} {L₃ : Type u₃}

/--
`impl` refines `spec` along the label map `f`: there is a relation between their states that
holds initially and is preserved when every step of `impl`, labelled `μ`, is answered by the
saturated step `f μ` of `spec`. If `f μ` is `τ` the answer may be no step at all.
-/
def Refines [HasTau L₂] (impl : Spec S₁ L₁) (spec : Spec S₂ L₂) (f : L₁ → L₂) : Prop :=
  ∃ rel : S₁ → S₂ → Prop,
    (∀ s, impl.init s → ∃ t, spec.init t ∧ rel s t) ∧
    (∀ s t, rel s t → ∀ μ s', impl.Tr s μ s' → ∃ t', spec.lts.STr t (f μ) t' ∧ rel s' t')

namespace Refines

/--
Refinement from a refinement mapping. `abs` reads each implementation state as a spec state and
`inv` is an invariant of the implementation. Each implementation step must either leave `abs`
unchanged while mapping to `τ`, or be one spec step with the mapped label.

This is the obligation the model checker's refinement check tests on small instances.
-/
theorem of_map [HasTau L₂] {impl : Spec S₁ L₁} {spec : Spec S₂ L₂} {f : L₁ → L₂}
    (abs : S₁ → S₂) (inv : S₁ → Prop)
    (init : ∀ s, impl.init s → inv s ∧ spec.init (abs s))
    (inv_step : ∀ s μ s', inv s → impl.Tr s μ s' → inv s')
    (step : ∀ s μ s', inv s → impl.Tr s μ s' →
      (f μ = HasTau.τ ∧ abs s' = abs s) ∨ spec.Tr (abs s) (f μ) (abs s')) :
    Refines impl spec f := by
  refine ⟨fun s t => inv s ∧ t = abs s, ?_, ?_⟩
  · intro s hs
    exact ⟨abs s, (init s hs).2, (init s hs).1, rfl⟩
  · rintro s t ⟨hinv, rfl⟩ μ s' htr
    refine ⟨abs s', ?_, inv_step s μ s' hinv htr, rfl⟩
    rcases step s μ s' hinv htr with ⟨hτ, habs⟩ | hspec
    · rw [hτ, habs]
      exact LTS.STr.refl
    · exact LTS.STr.single hspec

/-- A spec refines itself. -/
theorem refl [HasTau L₁] (spec : Spec S₁ L₁) : Refines spec spec id :=
  ⟨Eq, fun s hs => ⟨s, hs, rfl⟩, by
    rintro s _ rfl μ s' htr
    exact ⟨s', LTS.STr.single htr, rfl⟩⟩

/-- Internal steps of the middle system are answered by internal steps of the spec. -/
private theorem follow_τ [HasTau L₂] [HasTau L₃] {mid : Spec S₂ L₂} {spec : Spec S₃ L₃}
    {g : L₂ → L₃} (hg : g HasTau.τ = HasTau.τ) {rel : S₂ → S₃ → Prop}
    (hstep : ∀ s t, rel s t → ∀ μ s', mid.Tr s μ s' →
      ∃ t', spec.lts.STr t (g μ) t' ∧ rel s' t')
    {s s' : S₂} {t : S₃} (hrel : rel s t) (h : mid.lts.τSTr s s') :
    ∃ t', spec.lts.τSTr t t' ∧ rel s' t' := by
  induction h with
  | refl => exact ⟨t, LTS.τSTr.refl, hrel⟩
  | tail _ htr ih =>
    obtain ⟨t₁, ht₁, hrel₁⟩ := ih
    obtain ⟨t₂, ht₂, hrel₂⟩ := hstep _ _ hrel₁ _ _ htr
    rw [hg, LTS.sTr_τSTr_iff] at ht₂
    exact ⟨t₂, ReflTransGen.trans ht₁ ht₂, hrel₂⟩

/-- Saturated steps of the middle system are answered by saturated steps of the spec. -/
private theorem follow_sTr [HasTau L₂] [HasTau L₃] {mid : Spec S₂ L₂} {spec : Spec S₃ L₃}
    {g : L₂ → L₃} (hg : g HasTau.τ = HasTau.τ) {rel : S₂ → S₃ → Prop}
    (hstep : ∀ s t, rel s t → ∀ μ s', mid.Tr s μ s' →
      ∃ t', spec.lts.STr t (g μ) t' ∧ rel s' t')
    {s s' : S₂} {t : S₃} {μ : L₂} (hrel : rel s t) (h : mid.lts.STr s μ s') :
    ∃ t', spec.lts.STr t (g μ) t' ∧ rel s' t' := by
  cases h with
  | refl => exact ⟨t, hg ▸ LTS.STr.refl, hrel⟩
  | tr h₁ htr h₂ =>
    obtain ⟨t₁, ht₁, hrel₁⟩ := follow_τ hg hstep hrel h₁
    obtain ⟨t₂, ht₂, hrel₂⟩ := hstep _ _ hrel₁ _ _ htr
    obtain ⟨t₃, ht₃, hrel₃⟩ := follow_τ hg hstep hrel₂ h₂
    exact ⟨t₃, LTS.STr.comp ((LTS.sTr_τSTr_iff spec.lts).mpr ht₁) ht₂
      ((LTS.sTr_τSTr_iff spec.lts).mpr ht₃), hrel₃⟩

/--
Refinements compose. If the implementation refines a protocol model and the model refines the
service spec, the implementation refines the service spec. The second label map must keep
internal steps internal.
-/
theorem trans [HasTau L₂] [HasTau L₃] {impl : Spec S₁ L₁} {mid : Spec S₂ L₂}
    {spec : Spec S₃ L₃} {f : L₁ → L₂} {g : L₂ → L₃} (h₁ : Refines impl mid f)
    (h₂ : Refines mid spec g) (hg : g HasTau.τ = HasTau.τ) : Refines impl spec (g ∘ f) := by
  obtain ⟨r₁, init₁, step₁⟩ := h₁
  obtain ⟨r₂, init₂, step₂⟩ := h₂
  refine ⟨fun s u => ∃ t, r₁ s t ∧ r₂ t u, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := init₁ s hs
    obtain ⟨u, hu, htu⟩ := init₂ t ht
    exact ⟨u, hu, t, hst, htu⟩
  · rintro s u ⟨t, hst, htu⟩ μ s' htr
    obtain ⟨t', ht', hst'⟩ := step₁ s t hst μ s' htr
    obtain ⟨u', hu', htu'⟩ := follow_sTr hg step₂ htu ht'
    exact ⟨u', hu', t', hst', htu'⟩

/--
Refinement gives trace inclusion: for every finite run of the implementation from an initial
state, the spec has a run from an initial state with the same visible labels, where the internal
steps of each side are not counted.
-/
theorem traces [HasTau L₂] [DecidableEqTau L₂] {impl : Spec S₁ L₁} {spec : Spec S₂ L₂}
    {f : L₁ → L₂} (h : Refines impl spec f) {s s' : S₁} {μs : List L₁} (hs : impl.init s)
    (hrun : impl.lts.MTr s μs s') :
    ∃ t t', spec.init t ∧ spec.lts.SMTr t ((μs.map f).filter (· ≠ HasTau.τ)) t' := by
  obtain ⟨rel, init, step⟩ := h
  obtain ⟨t, ht, hrel⟩ := init s hs
  refine ⟨t, ?_⟩
  suffices h : ∀ t, rel s t → ∃ t', spec.lts.SMTr t ((μs.map f).filter (· ≠ HasTau.τ)) t' by
    obtain ⟨t', ht'⟩ := h t hrel
    exact ⟨t', ht, ht'⟩
  clear hrel ht hs t
  induction hrun with
  | refl => exact fun t _ => ⟨t, LTS.SMTr.refl _ t⟩
  | @stepL s μ s₂ μs s₃ htr _ ih =>
    intro t hrel
    obtain ⟨t₂, ht₂, hrel₂⟩ := step _ _ hrel _ _ htr
    obtain ⟨t₃, ht₃⟩ := ih t₂ hrel₂
    by_cases hτ : f μ = HasTau.τ
    · refine ⟨t₃, ?_⟩
      have h := LTS.SMTr.comp (LTS.SMTr.τ (hτ ▸ ht₂)) ht₃
      simpa [hτ] using h
    · refine ⟨t₃, ?_⟩
      simpa [hτ] using LTS.SMTr.stepL ht₂ ht₃

end Refines

end Lanes
