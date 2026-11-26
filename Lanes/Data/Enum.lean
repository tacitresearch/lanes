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

/--
The values of a function on a finite type, as data. A function built by a long run is a chain of
updates as deep as the run is long, and every lookup walks it; `Table.of` computes each value
once, and `Table.get` no longer refers to the function.

`Table.of` returns data, not a function, so that it is evaluated where it is written: a
definition that returns a function is compiled to one that takes the argument too, and would
build the table again on every lookup.
-/
structure Table (ι : Type) (β : ι → Type) where
  cells : List (Sigma β)
  complete : ∀ i, i ∈ cells.map Sigma.fst

namespace Table

variable {ι : Type} {β : ι → Type}

def find [DecidableEq ι] : (cells : List (Sigma β)) → (i : ι) → i ∈ cells.map Sigma.fst → β i
  | [], _, h => nomatch h
  | ⟨j, v⟩ :: cells, i, h =>
    if hij : i = j then hij ▸ v
    else find cells i (by
      cases h with
      | head => exact absurd rfl hij
      | tail _ h => exact h)

theorem find_map [DecidableEq ι] (f : (i : ι) → β i) (l : List ι) (i : ι)
    (h : i ∈ (l.map fun j => (⟨j, f j⟩ : Sigma β)).map Sigma.fst) :
    find (l.map fun j => ⟨j, f j⟩) i h = f i := by
  induction l with
  | nil => nomatch h
  | cons j l ih =>
    simp only [List.map_cons, find]
    split
    · next hij => subst hij; rfl
    · exact ih _

def of [Enum ι] (f : (i : ι) → β i) : Table ι β where
  cells := (all (α := ι)).map fun i => ⟨i, f i⟩
  complete i := by simpa [Function.comp_def] using Enum.complete i

def get [DecidableEq ι] (t : Table ι β) (i : ι) : β i :=
  find t.cells i (t.complete i)

@[simp] theorem get_of [DecidableEq ι] [Enum ι] (f : (i : ι) → β i) : (of f).get = f :=
  funext fun i => find_map f _ i _

end Table

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
