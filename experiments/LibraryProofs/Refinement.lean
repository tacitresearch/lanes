import Lanes.Semantics.Refinement

/-!
`Lanes.Refines` read as a CSLib simulation, and `Lanes.Refines.trans` proved with CSLib's
`IsSimulation.comp`, `IsSimulation.isSimulation_saturate_left` and `saturate_tr_saturate_sTr`
in place of the hand-written `follow_τ` and `follow_sTr` (`Lanes/Semantics/Refinement.lean`).
Run with `lake env lean experiments/LibraryProofs/Refinement.lean`.

`Refines impl spec f` asks each step of `impl` labelled `μ` to be answered by a saturated step of
`spec` labelled `f μ`. That is a simulation of `impl` by `spec`'s saturation pulled back along
`f` (CSLib's `LTS.mapLabel`). CSLib's simulations keep one label type on both sides, so what
Lanes has to add is the label map: the pulled-back saturation of `spec` is saturated already
when `f` keeps `τ` (`collapse` below).
-/

namespace Experiment

open Lanes Cslib LTS

variable {S₁ S₂ S₃ L₁ L₂ L₃ : Type}

/-- CSLib's `LTS.mapLabel` (`Cslib/Foundations/Semantics/LTS/MapHom.lean`), copied because that
module is not among the CSLib modules this checkout has built: the same transitions, read through
`f`. CSLib defines it through `mapHom` and proves `mapLabel_tr`, which is `Iff.rfl` here. -/
def pull {S L L' : Type} (lts : LTS S L) (f : L' → L) : LTS S L' where
  Tr s μ s' := lts.Tr s (f μ) s'

@[simp] theorem pull_tr {S L L' : Type} {lts : LTS S L} {f : L' → L} {s s' : S} {μ : L'} :
    (pull lts f).Tr s μ s' ↔ lts.Tr s (f μ) s' := Iff.rfl

/-- The step clause of `Lanes.Refines` is a CSLib simulation. -/
theorem refines_iff [HasTau L₂] {impl : Spec S₁ L₁} {spec : Spec S₂ L₂} {f : L₁ → L₂} :
    Refines impl spec f ↔ ∃ rel : S₁ → S₂ → Prop, (∀ s, impl.init s → ∃ t, spec.init t ∧ rel s t)
      ∧ IsSimulation impl.lts (pull spec.lts.saturate f) rel :=
  Iff.rfl

/-- If `g` keeps `τ`, the saturation of `spec` pulled back along `g` is saturated already. -/
theorem collapse [HasTau L₂] [HasTau L₃] {spec : Spec S₃ L₃} {g : L₂ → L₃}
    (hg : g HasTau.τ = HasTau.τ) {s t : S₃} {μ : L₂}
    (h : (pull spec.lts.saturate g).saturate.Tr s μ t) : (pull spec.lts.saturate g).Tr s μ t := by
  have hτ : ∀ {a b}, (pull spec.lts.saturate g).τSTr a b → spec.lts.saturate.τSTr a b :=
    fun h => Relation.ReflTransGen.mono (fun _ _ h => by simpa [Tr.toRelation, hg] using h) _ _ h
  rw [pull_tr, saturate_tr_saturate_sTr]
  cases h with
  | refl => rw [hg]; exact STr.refl
  | tr h₁ h₂ h₃ => exact STr.tr (hτ h₁) h₂ (hτ h₃)

/-- `Lanes.Refines.trans` from CSLib: 14 lines of proof where Lanes has 53 (`follow_τ`,
`follow_sTr` and `trans` itself); `collapse` and `pull` add 17. -/
theorem trans [HasTau L₂] [HasTau L₃] {impl : Spec S₁ L₁} {mid : Spec S₂ L₂}
    {spec : Spec S₃ L₃} {f : L₁ → L₂} {g : L₂ → L₃} (h₁ : Refines impl mid f)
    (h₂ : Refines mid spec g) (hg : g HasTau.τ = HasTau.τ) : Refines impl spec (g ∘ f) := by
  obtain ⟨r₁, init₁, sim₁⟩ := refines_iff.mp h₁
  obtain ⟨r₂, init₂, sim₂⟩ := refines_iff.mp h₂
  -- `mid`'s saturation is simulated too, and so is its pull-back along `f`.
  have sat : IsSimulation mid.lts.saturate (pull spec.lts.saturate g) r₂ :=
    (IsSimulation.isSimulation_saturate_left (sim₂.mono le_rfl (tr_le_tr_saturate _))).mono
      le_rfl fun _ _ _ => collapse hg
  have sat' : IsSimulation (pull mid.lts.saturate f) (pull spec.lts.saturate (g ∘ f)) r₂ :=
    fun _ _ hr μ _ htr => sat hr (f μ) _ htr
  refine refines_iff.mpr ⟨Relation.Comp r₁ r₂, fun s hs => ?_, IsSimulation.comp _ _ sim₁ sat'⟩
  obtain ⟨t, ht, hst⟩ := init₁ s hs
  obtain ⟨u, hu, htu⟩ := init₂ t ht
  exact ⟨u, hu, t, hst, htu⟩

end Experiment
