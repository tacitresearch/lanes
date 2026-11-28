import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
The ledger's money conservation rests on one lemma about sums, `Lanes.sum_map_set`
(`Lanes/Proof/List/Basic.lean`, 15 lines), used twice in `Ledger.Book.transfer_sound`
(`examples/ledger/Ledger/Proofs/Book.lean`). Here it is again from Mathlib's `List.sum_set'`.
The rest of `transfer_sound` is about the book (which accounts change, by how much) and no
library has it. Run with `lake env lean experiments/libraries/Ledger.lean`.
-/

namespace Experiment

variable {α : Type}

/-- The statement of `Lanes.sum_map_set`, from `List.map_set` and `List.sum_set'`. -/
theorem sum_map_set (f : α → Int) {l : List α} {i : Nat} {a : α} (v : α) (h : l[i]? = some a) :
    ((l.set i v).map f).sum + f a = (l.map f).sum + f v := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  simp [List.map_set, List.sum_set', hi]
  omega

end Experiment
