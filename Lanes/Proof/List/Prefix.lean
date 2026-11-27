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

/-- What comes before the first `a` in `l`: all of `l` if `a` is not in it. -/
@[expose] def beforeFirst [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then [] else x :: beforeFirst a xs

section BeforeFirst

variable [DecidableEq α] {a b : α}

theorem not_mem_beforeFirst (l : List α) : a ∉ beforeFirst a l := by
  induction l with
  | nil => simp [beforeFirst]
  | cons x xs ih =>
    simp only [beforeFirst]
    split
    · simp
    · next hx => simp [Ne.symm hx, ih]

theorem eq_beforeFirst_append {l : List α} (h : a ∈ l) :
    ∃ rest, l = beforeFirst a l ++ a :: rest := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [beforeFirst]
    split
    · next hx => exact ⟨xs, by simp [hx]⟩
    · next hx =>
      obtain ⟨rest, hrest⟩ := ih ((List.mem_cons.mp h).resolve_left (Ne.symm hx))
      exact ⟨rest, by rw [List.cons_append, ← hrest]⟩

theorem beforeFirst_append {l : List α} (h : a ∈ l) (l' : List α) :
    beforeFirst a (l ++ l') = beforeFirst a l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.cons_append, beforeFirst]
    split
    · rfl
    · next hx => rw [ih ((List.mem_cons.mp h).resolve_left (Ne.symm hx))]

theorem beforeFirst_filter {p : α → Bool} (hp : p a = true) (l : List α) :
    beforeFirst a (l.filter p) = (beforeFirst a l).filter p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, ↓reduceIte, beforeFirst]
      split
      · rfl
      · simp [hx, ih]
    · have hne : x ≠ a := fun h => hx (h ▸ hp)
      simp [hx, beforeFirst, hne, ih]

theorem beforeFirst_erase (hb : b ≠ a) (l : List α) :
    beforeFirst a (l.erase b) = (beforeFirst a l).erase b := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxb : x = b
    · subst hxb
      simp [beforeFirst, hb]
    · rw [List.erase_cons_tail (by simpa using hxb)]
      by_cases hxa : x = a
      · simp [beforeFirst, hxa]
      · simp only [beforeFirst, hxa, ↓reduceIte, ih]
        rw [List.erase_cons_tail (by simpa using hxb)]

/-- Where `a` is in `l` and `p` holds of it, the first element of `l` that satisfies `p` is
`a` or comes before it. -/
theorem find?_eq_or_beforeFirst {p : α → Bool} (hp : p a = true) {l : List α} (h : a ∈ l) :
    l.find? p = ((beforeFirst a l).find? p).or (some a) := by
  obtain ⟨rest, hrest⟩ := eq_beforeFirst_append h
  have hl : l.find? p = (beforeFirst a l ++ a :: rest).find? p := by rw [← hrest]
  rw [hl, List.find?_append, List.find?_cons_of_pos hp]

end BeforeFirst

/-- An element of a window `(l.drop a).take m` of a list is at a position from `a` to below
`a + m`. -/
theorem mem_take_drop {α : Type} {l : List α} {a m : Nat} {x : α} (h : x ∈ (l.drop a).take m) :
    ∃ k, a ≤ k ∧ k < a + m ∧ l[k]? = some x := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_take] at hj
  split at hj
  · next hjm =>
    rw [List.getElem?_drop] at hj
    exact ⟨a + j, by omega, by omega, hj⟩
  · cases hj

/-- A window of a list split at one of its elements. -/
theorem take_drop_split {α : Type} {l : List α} {a j m : Nat} {x : α} (haj : a ≤ j) (hjm : j < m)
    (hx : l[j]? = some x) :
    (l.drop a).take (m - a) = (l.drop a).take (j - a) ++ x :: (l.drop (j + 1)).take (m - (j + 1)) := by
  have hj : j < l.length := (List.getElem?_eq_some_iff.mp hx).1
  rw [show m - a = (j - a) + (m - j) by omega, List.take_add, List.drop_drop,
    show a + (j - a) = j by omega, List.drop_eq_getElem_cons hj,
    show m - j = (m - (j + 1)) + 1 by omega, List.take_succ_cons]
  have : l[j] = x := (List.getElem?_eq_some_iff.mp hx).2
  rw [this]

end Lanes
