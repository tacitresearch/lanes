/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
A log read by a monitor that may reject it, `foldlM` into `Option`; and right folds by `max`.
-/

public section

namespace Lanes

variable {α β : Type}

theorem foldlM_append_some {M : Type} {f : M → α → Option M} {l₁ l₂ : List α} {m t : M}
    (h : (l₁ ++ l₂).foldlM f m = some t) :
    ∃ m', l₁.foldlM f m = some m' ∧ l₂.foldlM f m' = some t := by
  rw [List.foldlM_append] at h
  cases h₁ : l₁.foldlM f m with
  | none => simp [h₁] at h
  | some m' => exact ⟨m', rfl, by simpa [h₁] using h⟩

theorem foldlM_cons_some {M : Type} {f : M → α → Option M} {x : α} {l : List α} {m t : M}
    (h : (x :: l).foldlM f m = some t) : ∃ m', f m x = some m' ∧ l.foldlM f m' = some t := by
  simp only [List.foldlM_cons] at h
  cases h₁ : f m x with
  | none => simp [h₁] at h
  | some m' => exact ⟨m', rfl, by simpa [h₁] using h⟩

/-- What each accepted element keeps, a whole accepted list keeps. -/
theorem foldlM_some_inv {M : Type} {f : M → α → Option M} {l : List α} {m t : M} (P : M → Prop)
    (hstep : ∀ m x m', x ∈ l → P m → f m x = some m' → P m') (hm : P m)
    (h : l.foldlM f m = some t) : P t := by
  induction l generalizing m with
  | nil => simp only [List.foldlM_nil] at h; exact Option.some.inj h ▸ hm
  | cons x l ih =>
    obtain ⟨m', hx, hl⟩ := foldlM_cons_some h
    exact ih (fun m y m'' hy => hstep m y m'' (List.mem_cons_of_mem _ hy))
      (hstep m x m' List.mem_cons_self hm hx) hl

/-- A right fold by `max` is at least where it starts. -/
theorem le_foldr_max (f : α → Nat) (init : Nat) (l : List α) :
    init ≤ l.foldr (fun a m => max (f a) m) init := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih => simp only [List.foldr_cons]; omega

/-- A right fold by `max` is at least each element's value. -/
theorem le_foldr_max_of_mem (f : α → Nat) (init : Nat) {l : List α} {a : α} (h : a ∈ l) :
    f a ≤ l.foldr (fun a m => max (f a) m) init := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

end Lanes
