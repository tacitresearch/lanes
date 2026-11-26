/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Facts about lists that fit none of the other files of `Lanes/Data/List/`.
-/

public section

namespace Lanes

variable {α β : Type}

theorem find?_congr {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem mapM_some {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self,
      mapM_some fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem dropWhile_of_head_any {p : α → Bool} : ∀ {l : List α}, l.head?.any p = false →
    l.dropWhile p = l
  | [], _ => rfl
  | c :: l, h => List.dropWhile_cons_of_neg (by simpa using h)

theorem flatMap_singletons {γ : Type} (f : α → β) (g : β → γ) (l : List α) :
    (l.flatMap fun a => [f a]).flatMap (fun b => [g b]) = l.map fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Replacing one element changes a sum by the difference. -/
theorem sum_map_set (f : α → Int) {l : List α} {i : Nat} {a : α} (v : α) (h : l[i]? = some a) :
    ((l.set i v).map f).sum + f a = (l.map f).sum + f v := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

end Lanes
