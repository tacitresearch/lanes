/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.World
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Abel

/-!
# Sums over actors and over messages in flight

Conservation properties (money, quota, tokens) are sums over all actors plus sums over the
messages in flight. A step changes one actor and adds or removes a few messages, so these two
lemmas are what such proofs rewrite with.

## Main statements

- `update_eq_functionUpdate`: Lanes' `update` is Mathlib's `Function.update`.
- `sum_update`: how a sum over all actors changes when one actor's state changes.
- `sum_map_erase`: how a sum over messages in flight changes when one is consumed.
-/

public section

namespace Lanes

open Finset

/-- Lanes' `update` is Mathlib's `Function.update`, so Mathlib's lemmas apply. -/
theorem update_eq_functionUpdate {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    (i : ι) (v : β i) : update f i v = Function.update f i v := by
  funext j
  simp only [update, Function.update]

/--
Changing one actor's state changes a sum over all actors by the difference at that actor.
`g` reads the summed quantity (a balance, a count) from a state.
-/
theorem sum_update {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type} {M : Type}
    [AddCommGroup M] (g : (i : ι) → β i → M) (f : (i : ι) → β i) (i : ι) (v : β i) :
    ∑ j, g j (update f i v j) = ∑ j, g j (f j) - g i (f i) + g i v := by
  rw [← add_sum_erase univ (fun j => g j (update f i v j)) (mem_univ i),
    ← add_sum_erase univ (fun j => g j (f j)) (mem_univ i)]
  have h : ∑ j ∈ univ.erase i, g j (update f i v j) = ∑ j ∈ univ.erase i, g j (f j) :=
    sum_congr rfl fun j hj => by rw [update_of_ne _ _ (ne_of_mem_erase hj)]
  rw [h, update_self]
  abel

/-- Consuming one message removes its contribution from a sum over the messages in flight. -/
theorem sum_map_erase {α : Type} [DecidableEq α] {M : Type} [AddCommGroup M] (g : α → M)
    {l : List α} {a : α} (h : a ∈ l) : ((l.erase a).map g).sum = (l.map g).sum - g a := by
  rw [← List.sum_map_erase g h]
  abel

end Lanes
