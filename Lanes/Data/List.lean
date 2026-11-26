/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Facts about lists that proofs about systems share: what `erase` does under `map`, `filter`,
`filterMap` and `countP`. Messages in flight, timers and outputs waiting are lists, and an event
takes one element out, so every proof that reads a state through a map or a filter needs these.
-/

public section

namespace Lanes

variable {α β : Type}

theorem filter_erase_of_pos [DecidableEq α] (p : α → Bool) (l : List α) {a : α}
    (_ : p a = true) : (l.erase a).filter p = (l.filter p).erase a :=
  List.erase_filter.symm

theorem filter_erase_of_neg [DecidableEq α] (p : α → Bool) (l : List α) {a : α}
    (h : p a = false) : (l.erase a).filter p = l.filter p := by
  rw [← List.erase_filter, List.erase_of_not_mem]
  simp [h]

/-- `f` need only tell `a` from the other elements of `l`. -/
theorem map_erase [DecidableEq α] [DecidableEq β] {f : α → β} {l : List α} {a : α}
    (inj : ∀ x ∈ l, f x = f a → x = a) : (l.erase a).map f = (l.map f).erase (f a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih fun y hy => inj y (List.mem_cons_of_mem _ hy)
    by_cases hx : x = a
    · subst hx
      simp
    · have hfx : f x ≠ f a := fun h => hx (inj x List.mem_cons_self h)
      simp [hx, hfx, ih]

theorem filterMap_erase [DecidableEq α] [DecidableEq β] {f : α → Option β} {a : α} {b : β}
    (h : ∀ x, f x = some b ↔ x = a) (l : List α) :
    (l.erase a).filterMap f = (l.filterMap f).erase b := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [(h x).mpr rfl]
    · cases hfx : f x with
      | none => simp [hx, hfx, ih]
      | some y =>
        have hy : y ≠ b := fun hyb => hx ((h x).mp (hyb ▸ hfx))
        simp [hx, hfx, ih, hy]

theorem filterMap_erase_of_none [DecidableEq α] {f : α → Option β} {a : α} (h : f a = none)
    (l : List α) : (l.erase a).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx
      simp [h]
    · cases hfx : f x <;> simp [hx, hfx, ih]

theorem filterMap_erase_perm [DecidableEq α] [DecidableEq β] {f : α → Option β} {l : List α}
    {a : α} {b : β} (ha : a ∈ l) (hb : f a = some b) :
    ((l.filterMap f).erase b).Perm ((l.erase a).filterMap f) := by
  have h := ((List.perm_cons_erase ha).filterMap f).erase b
  rwa [List.filterMap_cons_some hb, List.erase_cons_head] at h

/-- Erasing `b` from what `f` shows of `l` is erasing from `l` the first element shown as `b`. -/
theorem exists_filterMap_erase [DecidableEq α] [DecidableEq β] {f : α → Option β} {b : β} :
    ∀ l : List α, b ∈ l.filterMap f →
      ∃ a ∈ l, f a = some b ∧ (l.erase a).filterMap f = (l.filterMap f).erase b := by
  intro l
  induction l with
  | nil => exact fun h => absurd h (by simp)
  | cons x l ih =>
    intro h
    cases hfx : f x with
    | none =>
      rw [List.filterMap_cons_none hfx] at h
      obtain ⟨a, ha, hfa, heq⟩ := ih h
      have hx : x ≠ a := fun hxa => by simp [hxa, hfa] at hfx
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa, by simp [hx, hfx, heq]⟩
    | some y =>
      by_cases hy : y = b
      · subst hy
        exact ⟨x, List.mem_cons_self, hfx, by simp [hfx]⟩
      · rw [List.filterMap_cons_some hfx] at h
        obtain ⟨a, ha, hfa, heq⟩ := ih ((List.mem_cons.mp h).resolve_left fun hb => hy hb.symm)
        have hx : x ≠ a := fun hxa => hy (by simpa [hxa, hfa] using hfx.symm)
        exact ⟨a, List.mem_cons_of_mem _ ha, hfa, by simp [hx, hfx, heq, hy]⟩

theorem filterMap_cons_toList (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [h]

theorem filterMap_concat (f : α → Option β) (l : List α) (a : α) :
    (l ++ [a]).filterMap f = l.filterMap f ++ (f a).toList := by
  cases h : f a <;> simp [h]

theorem filterMap_filter_of_none {f : α → Option β} {p : α → Bool}
    (h : ∀ x, p x = false → f x = none) (l : List α) :
    (l.filter p).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases hp : p x with
    | true => cases hfx : f x <;> simp [hp, hfx, ih]
    | false => simp [hp, ih, h x hp]

theorem countP_erase_add [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {a : α}
    (h : a ∈ l) : (l.erase a).countP p + (p a).toNat = l.countP p := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      cases hp : p b <;> simp [hp]
    · have := ih (by simpa [Ne.symm hb] using h)
      simp only [List.erase_cons, beq_iff_eq, hb, ↓reduceIte, List.countP_cons]
      omega

theorem find?_congr {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

end Lanes
