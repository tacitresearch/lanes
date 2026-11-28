import Mathlib.Data.List.Count

/-!
Heavy proofs of `Lanes/Proof/List/` again, with Mathlib's lemmas or core's `grind`. Each states
the same as the Lanes theorem of the same name. Run with
`lake env lean experiments/libraries/ListProofs.lean`.
-/

namespace Experiment

variable {α β : Type}

/-- `Lanes.countP_erase_add` (`Lanes/Proof/List/Erase.lean`, 10 lines of proof) from Mathlib's
`List.countP_erase`. -/
theorem countP_erase_add [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {a : α}
    (h : a ∈ l) : (l.erase a).countP p + (p a).toNat = l.countP p := by
  cases hp : p a
  · simp [List.countP_erase, h, hp]
  · have := List.countP_pos_iff.mpr ⟨a, h, hp⟩
    simp [List.countP_erase, h, hp]
    omega

/-- The same with core's `grind` only, as Mathlib proves `List.countP_erase`. -/
theorem countP_erase_add' [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {a : α}
    (h : a ∈ l) : (l.erase a).countP p + (p a).toNat = l.countP p := by
  grind [List.countP_eq_length_filter]

/-- `Lanes.exists_filterMap_erase` (23 lines of proof): the induction stays, `grind` closes the
cases. -/
theorem exists_filterMap_erase [DecidableEq α] [DecidableEq β] {f : α → Option β} {b : β} :
    ∀ l : List α, b ∈ l.filterMap f →
      ∃ a ∈ l, f a = some b ∧ (l.erase a).filterMap f = (l.filterMap f).erase b := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    intro h
    by_cases hx : f x = some b
    · exact ⟨x, List.mem_cons_self, hx, by simp [hx]⟩
    · have hl : b ∈ l.filterMap f := by
        cases hfx : f x <;> simp_all; grind
      obtain ⟨a, ha, hfa, heq⟩ := ih hl
      have hxa : x ≠ a := by rintro rfl; exact hx hfa
      refine ⟨a, List.mem_cons_of_mem _ ha, hfa, ?_⟩
      cases hfx : f x <;> simp_all

end Experiment
