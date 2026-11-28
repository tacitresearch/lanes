/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.World
public import Lanes.Data.Enum

/-!
# Sums over every value of a finite type

`Enum α` lists every value of `α`, maybe more than once. `Enum.values α` lists each once, and
`Enum.sum g` adds `g a` over them: the sum over all actors that a conservation property states.

## Main definitions

- `Enum.values α`: every value of `α`, each once.
- `Enum.card α`: the number of values of `α`.
- `Enum.sum g`: `g a` added over every value `a`.

## Main statements

- `Enum.sum_update`: how a sum over all actors changes when one actor's state changes.
- `List.sum_map_erase_int`: how a sum over a list changes when one element is removed.
-/

@[expose] public section

namespace Lanes

/-- A list without its repeated elements: each one's last occurrence is kept. -/
def nub {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then nub l else a :: nub l

/-- `nub` keeps every element. -/
@[simp] theorem mem_nub {α : Type} [DecidableEq α] {a : α} {l : List α} : a ∈ nub l ↔ a ∈ l := by
  induction l with
  | nil => simp [nub]
  | cons b l ih =>
    simp only [nub]
    split <;> simp_all

/-- `nub` repeats nothing. -/
theorem nodup_nub {α : Type} [DecidableEq α] (l : List α) : (nub l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons b l ih =>
    simp only [nub]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨by simpa, ih⟩

private theorem sum_update_list {α : Type} {h h' : α → Int} {i : α} :
    ∀ {l : List α}, l.Nodup → i ∈ l → (∀ j, j ≠ i → h j = h' j) →
      (l.map h).sum = (l.map h').sum - h' i + h i
  | [], _, hi, _ => absurd hi List.not_mem_nil
  | a :: l, hnd, hi, hoff => by
    obtain ⟨hal, hnd⟩ := List.nodup_cons.mp hnd
    by_cases hai : a = i
    · subst hai
      have : l.map h = l.map h' :=
        List.map_congr_left fun j hj => hoff j fun e => hal (e ▸ hj)
      simp only [List.map_cons, List.sum_cons, this]
      omega
    · have hi' : i ∈ l := by
        rcases List.mem_cons.mp hi with e | e
        · exact absurd e.symm hai
        · exact e
      simp only [List.map_cons, List.sum_cons, hoff a hai, sum_update_list hnd hi' hoff]
      omega

namespace Enum

variable {α : Type} [Enum α] [DecidableEq α]

/-- Every value of `α`, each once. -/
def values (α : Type) [Enum α] [DecidableEq α] : List α := nub (all (α := α))

/-- The number of values of `α`. -/
def card (α : Type) [Enum α] [DecidableEq α] : Nat := (values α).length

/-- `g a` added over every value `a` of `α`. -/
def sum {M : Type} [Add M] [Zero M] (g : α → M) : M := ((values α).map g).sum

/-- Every value is listed. -/
@[simp] theorem mem_values (a : α) : a ∈ values α := mem_nub.mpr (complete a)

/-- No value is listed twice. -/
theorem nodup_values : (values α).Nodup := nodup_nub _

/-- A constant summed over every value. -/
@[simp] theorem sum_const (n : Int) : sum (fun _ : α => n) = card α * n := by
  simp only [sum, card]
  induction values α with
  | nil => simp
  | cons a l ih => simp [ih, Int.add_mul, Int.add_comm]

/-- Changing one actor's state changes a sum over all actors by the difference at that actor.
`g` reads the summed quantity (a balance, a count) from a state. -/
theorem sum_update {β : α → Type} (g : (i : α) → β i → Int) (f : (i : α) → β i) (i : α)
    (v : β i) :
    sum (fun j => g j (update f i v j)) = sum (fun j => g j (f j)) - g i (f i) + g i v := by
  simp only [sum]
  have := sum_update_list (h := fun j => g j (update f i v j)) (h' := fun j => g j (f j))
    nodup_values (mem_values i) fun j hj => by simp [update, hj]
  simpa using this

/-- Summing a pointwise sum is adding the sums. -/
theorem sum_add {g h : α → Int} : sum (fun a => g a + h a) = sum g + sum h := by
  simp only [sum]
  induction values α with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- Functions equal at every value have equal sums. -/
theorem sum_congr {M : Type} [Add M] [Zero M] {g h : α → M} (hgh : ∀ a, g a = h a) :
    sum g = sum h := by
  simp only [sum, funext hgh]

end Enum

/-- Consuming one message removes its contribution from a sum over the messages in flight. -/
theorem sum_map_erase {α : Type} [DecidableEq α] (g : α → Int) {l : List α} {a : α}
    (h : a ∈ l) : ((l.erase a).map g).sum = (l.map g).sum - g a := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
    by_cases hab : b = a
    · subst hab; simp; omega
    · have h' : a ∈ l := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e.symm hab
        · exact e
      simp [beq_iff_eq, hab, ih h']
      omega

end Lanes
