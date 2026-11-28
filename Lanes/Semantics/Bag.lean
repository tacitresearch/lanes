/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Init

/-!
# Bags

A bag (a multiset) is a list up to the order of its elements: a quotient of lists by
`List.Perm`, for which core Lean has the relation and its lemmas. Specs use bags for what waits
in no particular order, such as a service's pending inputs and undelivered outputs.

The operations and the names of the lemmas follow `Multiset` of the Lean community's
mathematics library, so a proof reads the same: `a ::ₘ s`, `s + t`, `s.erase a`, `s.count a`, `s.map f`, membership, and `s ≤ t`, which
holds when `t` is `s` and something more (`le_iff_count` reads it by counts).

## Main definitions

- `Bag α`: lists of `α` up to order; a list `l` is the bag `↑l`.
- `Bag.cons`, `+`, `Bag.erase`, `Bag.count`, `Bag.map`, `∈`, `≤`.

## Main statements

- `Bag.coe_eq_coe`: two lists are the same bag when one is a permutation of the other.
- `Bag.le_iff_count`: `s ≤ t` when no element occurs more often in `s` than in `t`.
-/

@[expose] public section

namespace Lanes

universe u v

/-- Lists of `α` up to the order of their elements. -/
def Bag (α : Type u) : Type u := Quotient (List.isSetoid α)

namespace Bag

variable {α : Type u} {β : Type v}

/-- The bag of a list's elements. -/
@[coe] def ofList (l : List α) : Bag α := Quotient.mk _ l

instance : Coe (List α) (Bag α) := ⟨ofList⟩

/-- Prove a property of every bag from one of every list. -/
@[elab_as_elim]
protected theorem ind {p : Bag α → Prop} (h : ∀ l : List α, p l) (s : Bag α) : p s :=
  Quotient.inductionOn s h

/-- Two lists are the same bag when one is a permutation of the other. -/
@[simp] theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Bag α) = l₂ ↔ l₁.Perm l₂ :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- A function on lists that respects permutations, on bags. -/
@[inline] def lift {γ : Sort v} (f : List α → γ) (h : ∀ l₁ l₂ : List α, l₁.Perm l₂ → f l₁ = f l₂)
    (s : Bag α) : γ :=
  Quotient.liftOn s f h

/-- A function of lists to lists that respects permutations, on bags. -/
@[inline] def lift1 {β : Type v} (f : List α → List β)
    (h : ∀ l₁ l₂ : List α, l₁.Perm l₂ → (f l₁).Perm (f l₂)) (s : Bag α) : Bag β :=
  lift (fun l => ofList (f l)) (fun _ _ hl => Quotient.sound (h _ _ hl)) s

/-- The empty bag. -/
instance : Zero (Bag α) := ⟨([] : List α)⟩

instance : Inhabited (Bag α) := ⟨0⟩

/-- The empty list is the empty bag. -/
@[simp] theorem coe_nil : (([] : List α) : Bag α) = 0 := rfl

/-- `a` added to `s`. -/
def cons (a : α) (s : Bag α) : Bag α :=
  lift1 (a :: ·) (fun _ _ h => h.cons a) s

end Bag

@[inherit_doc] scoped infixr:67 " ::ₘ " => Bag.cons

namespace Bag

variable {α : Type u} {β : Type v}

/-- The bag of one element. -/
instance : Singleton α (Bag α) := ⟨fun a => ([a] : List α)⟩

/-- Both bags' elements. -/
instance : Add (Bag α) :=
  ⟨fun s t => lift (fun l => lift1 (l ++ ·) (fun _ _ h => h.append_left l) t)
    (fun l₁ l₂ h => by
      induction t using Quotient.inductionOn
      exact Quotient.sound (h.append_right _)) s⟩

/-- Whether `a` is in `s`. -/
def Mem (s : Bag α) (a : α) : Prop :=
  lift (a ∈ ·) (fun _ _ h => propext h.mem_iff) s

instance : Membership α (Bag α) := ⟨Mem⟩

/-- `f` applied to each element. -/
def map (f : α → β) (s : Bag α) : Bag β :=
  lift1 (List.map f) (fun _ _ h => h.map f) s

/-- The number of elements. -/
def card (s : Bag α) : Nat :=
  lift List.length (fun _ _ h => h.length_eq) s

/-- `t` is `s` and something more. -/
protected def Le (s t : Bag α) : Prop := ∃ u, t = s + u

instance : LE (Bag α) := ⟨Bag.Le⟩

section Basic

variable {a b : α} {s t u : Bag α} {l l₁ l₂ : List α}

@[simp] theorem cons_coe (a : α) (l : List α) : a ::ₘ (l : Bag α) = (a :: l : List α) := rfl

@[simp] theorem coe_add (l₁ l₂ : List α) : (l₁ : Bag α) + l₂ = (l₁ ++ l₂ : List α) := rfl

theorem coe_singleton (a : α) : (([a] : List α) : Bag α) = {a} := rfl

@[simp] theorem mem_coe : a ∈ (l : Bag α) ↔ a ∈ l := Iff.rfl

@[simp] theorem map_coe (f : α → β) (l : List α) : map f (l : Bag α) = (l.map f : List β) := rfl

@[simp] theorem card_coe (l : List α) : card (l : Bag α) = l.length := rfl

@[simp] theorem zero_add (s : Bag α) : 0 + s = s := by
  induction s using Bag.ind; rfl

@[simp] theorem add_zero (s : Bag α) : s + 0 = s := by
  induction s using Bag.ind; simp [← coe_nil]

theorem add_assoc (s t u : Bag α) : s + t + u = s + (t + u) := by
  induction s using Bag.ind; induction t using Bag.ind; induction u using Bag.ind; simp

theorem add_comm (s t : Bag α) : s + t = t + s := by
  induction s using Bag.ind; induction t using Bag.ind; simpa using List.perm_append_comm

theorem add_left_comm (s t u : Bag α) : s + (t + u) = t + (s + u) := by
  rw [← add_assoc, add_comm s t, add_assoc]

instance : Std.Associative (α := Bag α) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := Bag α) (· + ·) := ⟨add_comm⟩
instance : Std.LawfulIdentity (α := Bag α) (· + ·) 0 where
  left_id := zero_add
  right_id := add_zero

theorem cons_eq_singleton_add (a : α) (s : Bag α) : a ::ₘ s = {a} + s := by
  induction s using Bag.ind; rfl

theorem singleton_add (a : α) (s : Bag α) : {a} + s = a ::ₘ s :=
  (cons_eq_singleton_add a s).symm

@[simp] theorem coe_singleton_add (a : α) (s : Bag α) : (([a] : List α) : Bag α) + s = a ::ₘ s :=
  singleton_add a s

@[simp] theorem cons_add (a : α) (s t : Bag α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [cons_eq_singleton_add, cons_eq_singleton_add, add_assoc]

@[simp] theorem add_cons (a : α) (s t : Bag α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [cons_eq_singleton_add, cons_eq_singleton_add, add_left_comm]

theorem cons_swap (a b : α) (s : Bag α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s := by
  induction s using Bag.ind; exact coe_eq_coe.mpr (.swap b a _)

@[simp] theorem mem_cons : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s := by
  induction s using Bag.ind; simp

theorem mem_cons_self (a : α) (s : Bag α) : a ∈ a ::ₘ s := mem_cons.mpr (.inl rfl)

theorem mem_cons_of_mem (h : a ∈ s) : a ∈ b ::ₘ s := mem_cons.mpr (.inr h)

@[simp] theorem mem_add : a ∈ s + t ↔ a ∈ s ∨ a ∈ t := by
  induction s using Bag.ind; induction t using Bag.ind; simp

@[simp] theorem mem_singleton : a ∈ ({b} : Bag α) ↔ a = b := by
  simp [← coe_singleton]

@[simp] theorem not_mem_zero (a : α) : a ∉ (0 : Bag α) := by
  simp [← coe_nil]

@[simp] theorem map_zero (f : α → β) : map f (0 : Bag α) = 0 := rfl

@[simp] theorem map_cons (f : α → β) (a : α) (s : Bag α) : map f (a ::ₘ s) = f a ::ₘ map f s := by
  induction s using Bag.ind; rfl

@[simp] theorem map_add (f : α → β) (s t : Bag α) : map f (s + t) = map f s + map f t := by
  induction s using Bag.ind; induction t using Bag.ind; simp

@[simp] theorem map_singleton (f : α → β) (a : α) : map f ({a} : Bag α) = {f a} := rfl

@[simp] theorem mem_map {f : α → β} {b : β} : b ∈ map f s ↔ ∃ a ∈ s, f a = b := by
  induction s using Bag.ind; simp

@[simp] theorem card_zero : card (0 : Bag α) = 0 := rfl

@[simp] theorem card_add (s t : Bag α) : card (s + t) = card s + card t := by
  induction s using Bag.ind; induction t using Bag.ind; simp

@[simp] theorem card_cons (a : α) (s : Bag α) : card (a ::ₘ s) = card s + 1 := by
  induction s using Bag.ind; simp

end Basic

/-! ### Order -/

section Order

variable {a b : α} {s t u s' t' : Bag α} {l₁ l₂ : List α}

theorem le_def : s ≤ t ↔ ∃ u, t = s + u := Iff.rfl

@[simp] theorem le_refl (s : Bag α) : s ≤ s := ⟨0, (add_zero s).symm⟩

theorem le_rfl : s ≤ s := le_refl s

theorem le_of_eq (h : s = t) : s ≤ t := h ▸ le_refl s

/-- An inequality between equal bags. -/
theorem le_congr (h : s ≤ t) (hs : s' = s) (ht : t = t') : s' ≤ t' := hs ▸ ht ▸ h

theorem le_trans_eq (h : s ≤ t) (ht : t = u) : s ≤ u := ht ▸ h

theorem le_trans (h₁ : s ≤ t) (h₂ : t ≤ u) : s ≤ u := by
  obtain ⟨v, rfl⟩ := h₁
  obtain ⟨w, rfl⟩ := h₂
  exact ⟨v + w, add_assoc _ _ _⟩

theorem Le.trans (h₁ : s ≤ t) (h₂ : t ≤ u) : s ≤ u := le_trans h₁ h₂

theorem Le.trans_eq (h : s ≤ t) (ht : t = u) : s ≤ u := ht ▸ h

instance : Std.IsPreorder (Bag α) where
  le_refl := le_refl
  le_trans _ _ _ := le_trans

@[simp] theorem zero_le (s : Bag α) : 0 ≤ s := ⟨s, (zero_add s).symm⟩

@[simp] theorem le_add_right (s t : Bag α) : s ≤ s + t := ⟨t, rfl⟩

@[simp] theorem le_add_left (s t : Bag α) : s ≤ t + s := ⟨t, add_comm _ _⟩

theorem add_le_add (h₁ : s ≤ t) (h₂ : s' ≤ t') : s + s' ≤ t + t' := by
  obtain ⟨u, rfl⟩ := h₁
  obtain ⟨u', rfl⟩ := h₂
  exact ⟨u + u', by ac_rfl⟩

theorem add_le_add_left (h : s ≤ t) (u : Bag α) : u + s ≤ u + t :=
  add_le_add (le_refl u) h

theorem add_le_add_right (h : s ≤ t) (u : Bag α) : s + u ≤ t + u :=
  add_le_add h (le_refl u)

theorem mem_of_le (h : s ≤ t) (ha : a ∈ s) : a ∈ t := by
  obtain ⟨u, rfl⟩ := h
  exact mem_add.mpr (.inl ha)

theorem le_cons_self (s : Bag α) (a : α) : s ≤ a ::ₘ s :=
  ⟨{a}, by rw [cons_eq_singleton_add, add_comm]⟩

theorem cons_le_cons (a : α) (h : s ≤ t) : a ::ₘ s ≤ a ::ₘ t := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (cons_add a s u).symm⟩

theorem map_le_map (f : α → β) (h : s ≤ t) : map f s ≤ map f t := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨map f u, map_add f s u⟩

/-- A sublist is a smaller bag. -/
theorem coe_le_coe_of_sublist (h : l₁.Sublist l₂) : (l₁ : Bag α) ≤ l₂ := by
  induction h with
  | slnil => exact le_refl _
  | cons a _ ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨a ::ₘ u, by rw [← cons_coe, hu, add_cons]⟩
  | cons_cons a _ ih => exact cons_le_cons a ih

end Order

/-! ### Erasing and counting -/

section Erase

variable [DecidableEq α] {a b : α} {s t u : Bag α} {l : List α}

/-- `s` with one `a` fewer, if it has one. -/
def erase (s : Bag α) (a : α) : Bag α :=
  lift1 (·.erase a) (fun _ _ h => h.erase a) s

/-- The number of times `a` is in `s`. -/
def count (a : α) (s : Bag α) : Nat :=
  lift (List.count a) (fun _ _ h => h.count_eq a) s

instance (a : α) (s : Bag α) : Decidable (a ∈ s) :=
  Quotient.recOnSubsingleton s fun l => inferInstanceAs (Decidable (a ∈ l))

@[simp] theorem coe_erase (l : List α) (a : α) : (l : Bag α).erase a = (l.erase a : List α) := rfl

@[simp] theorem coe_count (a : α) (l : List α) : count a (l : Bag α) = l.count a := rfl

@[simp] theorem erase_zero (a : α) : (0 : Bag α).erase a = 0 := rfl

@[simp] theorem erase_cons_head (a : α) (s : Bag α) : (a ::ₘ s).erase a = s := by
  induction s using Bag.ind; simp

theorem erase_cons_tail (s : Bag α) (h : b ≠ a) : (b ::ₘ s).erase a = b ::ₘ s.erase a := by
  induction s using Bag.ind; simp [beq_iff_eq, h]

theorem erase_of_not_mem (h : a ∉ s) : s.erase a = s := by
  induction s using Bag.ind; exact congrArg ofList (List.erase_of_not_mem h)

theorem cons_erase (h : a ∈ s) : a ::ₘ s.erase a = s := by
  induction s using Bag.ind with
  | h l => exact coe_eq_coe.mpr (List.perm_cons_erase h).symm

theorem mem_of_mem_erase (h : a ∈ s.erase b) : a ∈ s := by
  induction s using Bag.ind; exact List.mem_of_mem_erase h

theorem erase_add_left_pos (t : Bag α) (h : a ∈ s) : (s + t).erase a = s.erase a + t := by
  induction s using Bag.ind; induction t using Bag.ind; simp [List.erase_append_left _ h]

theorem erase_add_right_pos (s : Bag α) (h : a ∈ t) : (s + t).erase a = s + t.erase a := by
  rw [add_comm, erase_add_left_pos s h, add_comm]

theorem erase_add_right_neg (t : Bag α) (h : a ∉ s) : (s + t).erase a = s + t.erase a := by
  induction s using Bag.ind; induction t using Bag.ind; simp [List.erase_append_right _ h]

theorem erase_le (a : α) (s : Bag α) : s.erase a ≤ s := by
  by_cases h : a ∈ s
  · exact ⟨{a}, by rw [add_comm, singleton_add, cons_erase h]⟩
  · rw [erase_of_not_mem h]; exact le_refl s

theorem erase_le_erase (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a := by
  obtain ⟨u, rfl⟩ := h
  by_cases ha : a ∈ s
  · exact ⟨u, erase_add_left_pos u ha⟩
  · rw [erase_of_not_mem ha, erase_add_right_neg u ha]
    exact le_add_right _ _

theorem map_erase_of_mem [DecidableEq β] (f : α → β) (s : Bag α) (h : a ∈ s) :
    map f (s.erase a) = (map f s).erase (f a) := by
  conv => rhs; rw [← cons_erase h]
  simp

@[simp] theorem count_zero (a : α) : count a (0 : Bag α) = 0 := rfl

@[simp] theorem count_add (a : α) (s t : Bag α) : count a (s + t) = count a s + count a t := by
  induction s using Bag.ind; induction t using Bag.ind; simp

@[simp] theorem count_cons_self (a : α) (s : Bag α) : count a (a ::ₘ s) = count a s + 1 := by
  induction s using Bag.ind; simp

theorem count_cons_of_ne (h : a ≠ b) (s : Bag α) : count a (b ::ₘ s) = count a s := by
  induction s using Bag.ind; simp [Ne.symm h]

theorem count_eq_zero : count a s = 0 ↔ a ∉ s := by
  induction s using Bag.ind; simp [List.count_eq_zero]

theorem count_eq_zero_of_notMem (h : a ∉ s) : count a s = 0 := count_eq_zero.mpr h

theorem count_pos : 0 < count a s ↔ a ∈ s := by
  induction s using Bag.ind; simp [List.count_pos_iff]

@[simp] theorem count_erase_self (a : α) (s : Bag α) : count a (s.erase a) = count a s - 1 := by
  induction s using Bag.ind; simp

@[simp] theorem count_erase_of_ne (h : a ≠ b) (s : Bag α) : count a (s.erase b) = count a s := by
  induction s using Bag.ind; simp [List.count_erase_of_ne h]

theorem count_le_of_le (a : α) (h : s ≤ t) : count a s ≤ count a t := by
  obtain ⟨u, rfl⟩ := h
  simp

/-- Bags are equal when every element occurs as often in each. -/
theorem ext' {s t : Bag α} (h : ∀ a, count a s = count a t) : s = t := by
  induction s using Bag.ind; induction t using Bag.ind
  exact coe_eq_coe.mpr (List.perm_iff_count.mpr h)

/-- What is added on the right can be taken away. -/
theorem add_right_cancel (h : s + u = t + u) : s = t :=
  ext' fun a => by have := congrArg (count a) h; simp at this; omega

/-- What is added on the left can be taken away. -/
theorem add_left_cancel (h : u + s = u + t) : s = t :=
  add_right_cancel (u := u) (by rw [add_comm s u, add_comm t u]; exact h)

/-- Bags are equal when every element occurs as often in each. -/
theorem ext {s t : Bag α} (h : ∀ a, count a s = count a t) : s = t := by
  induction s using Bag.ind; induction t using Bag.ind
  exact coe_eq_coe.mpr (List.perm_iff_count.mpr h)

/-- `s ≤ t` when no element occurs more often in `s` than in `t`. -/
theorem le_iff_count : s ≤ t ↔ ∀ a, count a s ≤ count a t := by
  refine ⟨fun h a => count_le_of_le a h, fun h => ?_⟩
  induction s using Bag.ind generalizing t with
  | h l =>
    induction l generalizing t with
    | nil => exact zero_le t
    | cons a l ih =>
      have ha : a ∈ t := count_pos.mp (by have := h a; simp at this; omega)
      have hle : (l : Bag α) ≤ t.erase a := ih fun b => by
        have := h b
        by_cases hb : b = a
        · subst hb; simp at this ⊢; omega
        · rw [count_erase_of_ne hb]
          rw [← cons_coe, count_cons_of_ne hb] at this
          exact this
      rw [← cons_erase ha, ← cons_coe]
      exact cons_le_cons a hle

end Erase

end Bag

end Lanes
