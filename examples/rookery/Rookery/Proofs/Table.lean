import Rookery.Table

/-!
What a lookup sees of a table after it is changed. These lemmas do not mention the board; they
belong in `Lanes/Proof/List/`, which this package may not edit (friction log).
-/

namespace Rookery

variable {N α : Type} [DecidableEq N]

theorem lookup_modify (m n : N) (f : α → α) (t : List (N × α)) :
    lookup m (modify n f t) = if m = n then (lookup m t).map f else lookup m t := by
  induction t with
  | nil => simp [lookup, modify]
  | cons x t ih =>
    obtain ⟨k, a⟩ := x
    simp only [modify, List.map_cons, lookup] at ih ⊢
    rw [ih]
    by_cases hk : k = m
    · subst hk
      by_cases hn : k = n <;> simp [hn]
    · simp [hk]

theorem lookup_append_of_ne {m n : N} (h : n ≠ m) (a : α) (t : List (N × α)) :
    lookup m (t ++ [(n, a)]) = lookup m t := by
  induction t with
  | nil => simp [lookup, h]
  | cons x t ih =>
    obtain ⟨k, b⟩ := x
    simp only [List.cons_append, lookup, ih]

theorem lookup_append_self {n : N} {t : List (N × α)} (h : lookup n t = none) (a : α) :
    lookup n (t ++ [(n, a)]) = some a := by
  induction t with
  | nil => simp [lookup]
  | cons x t ih =>
    obtain ⟨k, b⟩ := x
    simp only [lookup] at h
    split at h
    · cases h
    · simp only [List.cons_append, lookup, *, ite_false]

theorem mem_of_lookup {n : N} {a : α} {t : List (N × α)} (h : lookup n t = some a) :
    (n, a) ∈ t := by
  induction t with
  | nil => simp [lookup] at h
  | cons x t ih =>
    obtain ⟨k, b⟩ := x
    simp only [lookup] at h
    split at h
    · cases h; subst_vars; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem length_modify (n : N) (f : α → α) (t : List (N × α)) :
    (modify n f t).length = t.length := by
  simp [modify]

/-- Each entry after `modify n f` is an entry before, changed by `f` if it is `n`'s. -/
theorem mem_modify {n : N} {f : α → α} {t : List (N × α)} {x : N × α}
    (h : x ∈ modify n f t) : ∃ y ∈ t, x = (y.1, if y.1 = n then f y.2 else y.2) := by
  simp only [modify, List.mem_map] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

end Rookery
