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

/-- Functions equal at every value have equal sums. -/
theorem sum_congr {M : Type} [Add M] [Zero M] {g h : α → M} (hgh : ∀ a, g a = h a) :
    sum g = sum h := by
  simp only [sum, funext hgh]

section Monoid

/-! Sums in any commutative monoid: integers, bags. -/

variable {M : Type} [Add M] [Zero M] [Std.Associative (α := M) (· + ·)]
  [Std.Commutative (α := M) (· + ·)] [Std.LawfulIdentity (α := M) (· + ·) 0]

omit [Std.Associative (α := M) (· + ·)] [Std.Commutative (α := M) (· + ·)] in
private theorem zero_add' (x : M) : 0 + x = x := Std.LawfulLeftIdentity.left_id x
omit [Std.Associative (α := M) (· + ·)] [Std.Commutative (α := M) (· + ·)] in
private theorem add_zero' (x : M) : x + 0 = x := Std.LawfulRightIdentity.right_id x

omit [Std.Associative (α := M) (· + ·)] [Std.Commutative (α := M) (· + ·)] in
/-- Nothing summed is nothing. -/
@[simp] theorem sum_zero : sum (fun _ : α => (0 : M)) = 0 := by
  simp only [sum]
  induction values α with
  | nil => rfl
  | cons a l ih => simp [ih, zero_add']

/-- Summing a pointwise sum is adding the sums. -/
theorem sum_add {g h : α → M} : sum (fun a => g a + h a) = sum g + sum h := by
  simp only [sum]
  induction values α with
  | nil => simp [zero_add']
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ac_rfl

omit [Enum α] [Std.Associative (α := M) (· + ·)] [Std.Commutative (α := M) (· + ·)] in
private theorem sum_ite_list (i : α) (x : M) :
    ∀ {l : List α}, l.Nodup →
      (l.map fun a => if i = a then x else 0).sum = if i ∈ l then x else 0
  | [], _ => by simp
  | a :: l, hnd => by
    obtain ⟨hal, hnd⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.sum_cons, sum_ite_list i x hnd, List.mem_cons]
    by_cases hia : i = a
    · subst hia; simp [hal, add_zero']
    · simp [hia, zero_add']

omit [Std.Associative (α := M) (· + ·)] [Std.Commutative (α := M) (· + ·)] in
/-- A sum of what is nothing at every value but one. -/
theorem sum_ite_eq (i : α) (x : M) : sum (fun a => if i = a then x else 0) = x := by
  simp only [sum, sum_ite_list i x nodup_values, mem_values, ite_true]

omit [Enum α] in
private theorem sum_split_list (i : α) (g : α → M) :
    ∀ {l : List α}, l.Nodup → i ∈ l →
      (l.map g).sum = g i + (l.map fun a => if a = i then 0 else g a).sum
  | [], _, hi => absurd hi List.not_mem_nil
  | a :: l, hnd, hi => by
    obtain ⟨hal, hnd⟩ := List.nodup_cons.mp hnd
    by_cases hai : a = i
    · subst hai
      have : (l.map fun b => if b = a then 0 else g b) = l.map g :=
        List.map_congr_left fun b hb => by
          have hba : b ≠ a := fun e => hal (e ▸ hb)
          simp [hba]
      simp [this, zero_add']
    · have hi' : i ∈ l := by
        rcases List.mem_cons.mp hi with e | e
        · exact absurd e.symm hai
        · exact e
      simp only [List.map_cons, List.sum_cons, sum_split_list i g hnd hi', hai, ite_false]
      ac_rfl

/-- A sum is its value at `i` and the sum of the others. -/
theorem sum_split (i : α) (g : α → M) : sum g = g i + sum (fun a => if a = i then 0 else g a) :=
  sum_split_list i g nodup_values (mem_values i)

end Monoid

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
