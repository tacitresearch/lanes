/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
`take` and `drop` of a log and of a start of it, and what follows the first occurrence of an
element.
-/

public section

namespace Lanes

variable {α β : Type}

theorem take_of_prefix {a b : List α} (h : a <+: b) {n : Nat} (hn : n ≤ a.length) :
    b.take n = a.take n := by
  obtain ⟨rest, rfl⟩ := h
  exact List.take_append_of_le_length hn

theorem drop_take_of_le (l : List α) {a b : Nat} (h : a ≤ b) : (l.take a).drop b = [] :=
  List.drop_eq_nil_of_le (by rw [List.length_take]; omega)

/-- A start of what follows `n` in `l` is what follows `n` in a start of `l`. -/
theorem drop_take_of_prefix {l part : List α} {n : Nat} (h : part <+: l.drop n) :
    (l.take (n + part.length)).drop n = part := by
  rw [List.drop_take, Nat.add_sub_cancel_left]
  exact (List.prefix_iff_eq_take.mp h).symm

theorem append_singleton_eq_append_cons {l before after : List α} {a b : α}
    (h : l ++ [a] = before ++ b :: after) :
    (before = l ∧ b = a ∧ after = []) ∨ ∃ rest, l = before ++ b :: rest ∧ after = rest ++ [a] := by
  rcases List.eq_nil_or_concat after with rfl | ⟨rest, c, rfl⟩
  · obtain ⟨hl, hab⟩ := List.append_inj' h rfl
    exact .inl ⟨hl.symm, (List.singleton_inj.mp hab).symm, rfl⟩
  · rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at h
    obtain ⟨hl, hac⟩ := List.append_inj' h rfl
    exact .inr ⟨rest, hl, by rw [List.concat_eq_append, List.singleton_inj.mp hac]⟩

theorem getElem?_of_prefix {a b : List α} (h : a <+: b) {k : Nat} {x : α}
    (hx : a[k]? = some x) : b[k]? = some x := by
  obtain ⟨rest, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

/-- What follows the first `a` in `l`, if `a` is in it. -/
@[expose] def afterFirst [DecidableEq α] (a : α) : List α → Option (List α)
  | [] => none
  | x :: xs => if x = a then some xs else afterFirst a xs

theorem eq_of_afterFirst [DecidableEq α] {a : α} {l rest : List α}
    (h : afterFirst a l = some rest) : ∃ skipped, l = skipped ++ a :: rest := by
  induction l with
  | nil => simp [afterFirst] at h
  | cons x xs ih =>
    simp only [afterFirst] at h
    split at h
    · next hx => exact ⟨[], by simp [hx, Option.some.inj h]⟩
    · obtain ⟨skipped, rfl⟩ := ih h
      exact ⟨x :: skipped, rfl⟩

/-- Taking the first `a` out of a list that `a :: l` is a sublist of leaves one that `l` is a
sublist of. -/
theorem afterFirst_of_cons_sublist [DecidableEq α] {a : α} {l p : List α} (h : (a :: l).Sublist p) :
    ∃ rest, afterFirst a p = some rest ∧ l.Sublist rest := by
  induction p with
  | nil => simp at h
  | cons x xs ih =>
    simp only [afterFirst]
    split
    · next hx =>
      subst hx
      exact ⟨xs, rfl, (List.cons_sublist_cons.mp h)⟩
    · next hx =>
      rcases h with _ | ⟨_, h⟩ | ⟨_, h⟩
      · exact ih ‹_›
      · exact absurd rfl hx

end Lanes
