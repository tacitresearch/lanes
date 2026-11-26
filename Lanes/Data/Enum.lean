/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Finite types with a listed set of values

`Enum α` lists every value of `α`. The simulator and the model checker use it to walk over actor
identities, and the model checker uses it to run actors that are generic over keys, values and
node identities on small instances (2 keys, 3 nodes).

It is defined here, not taken from Mathlib's `Fintype`, because runtime modules import only `Std`.
-/

@[expose] public section

namespace Lanes

class Enum (α : Type) where
  all : List α
  complete : ∀ a : α, a ∈ all

namespace Enum

instance : Enum Empty := ⟨[], fun a => nomatch a⟩

instance : Enum Unit := ⟨[()], fun _ => by simp⟩

instance : Enum Bool := ⟨[false, true], fun b => by cases b <;> simp⟩

instance {n : Nat} : Enum (Fin n) := ⟨List.finRange n, List.mem_finRange⟩

instance {α : Type} [Enum α] : Enum (Option α) where
  all := none :: (all (α := α)).map some
  complete a := by
    cases a with
    | none => simp
    | some a => simp [complete a]

instance {α β : Type} [Enum α] [Enum β] : Enum (α ⊕ β) where
  all := (all (α := α)).map .inl ++ (all (α := β)).map .inr
  complete a := by
    cases a with
    | inl a => simp [complete a]
    | inr b => simp [complete b]

instance {α β : Type} [Enum α] [Enum β] : Enum (α × β) where
  all := (all (α := α)).flatMap fun a => (all (α := β)).map fun b => (a, b)
  complete p := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨p.1, complete p.1, p.2, complete p.2, rfl⟩

instance {α : Type} {p : α → Prop} [Enum α] [DecidablePred p] : Enum {a // p a} where
  all := (all (α := α)).filterMap fun a => if h : p a then some ⟨a, h⟩ else none
  complete a := List.mem_filterMap.mpr ⟨a.val, complete a.val, by simp [a.property]⟩

/-- Low priority, so a more specific instance wins. -/
instance (priority := low) funBEq {α β : Type} [Enum α] [BEq β] : BEq (α → β) where
  beq f g := (all (α := α)).all fun a => f a == g a

instance funLawfulBEq {α β : Type} [Enum α] [BEq β] [LawfulBEq β] : LawfulBEq (α → β) where
  rfl := List.all_eq_true.mpr fun _ _ => BEq.rfl
  eq_of_beq h := funext fun a => eq_of_beq (List.all_eq_true.mp h a (complete a))

instance (priority := low) funHashable {α β : Type} [Enum α] [Hashable β] : Hashable (α → β) where
  hash f := (all (α := α)).foldl (fun h a => mixHash h (hash (f a))) 17

instance (priority := low) funRepr {α β : Type} [Enum α] [Repr α] [Repr β] : Repr (α → β) where
  reprPrec f _ := repr ((all (α := α)).map fun a => (a, f a))

end Enum

end Lanes
