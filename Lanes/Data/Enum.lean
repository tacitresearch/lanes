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

def tabulateOn {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i) :
    (l : List ι) → (i : ι) → i ∈ l → β i
  | [], _, h => nomatch h
  | j :: l, i, h =>
    let v := f j
    let rest := tabulateOn f l
    if hij : i = j then hij ▸ v
    else rest i (by cases h with | head => exact absurd rfl hij | tail _ h => exact h)

/--
Rebuild a function on a finite type as a table of already computed values. The result is equal
to `f` (`tabulate_eq`) but no longer refers to `f`, so chains of function updates do not grow
across a long run.
-/
def tabulate {ι : Type} [DecidableEq ι] [Enum ι] {β : ι → Type} (f : (i : ι) → β i) :
    (i : ι) → β i :=
  let table := tabulateOn f (all (α := ι))
  fun i => table i (complete i)

theorem tabulateOn_eq {ι : Type} [DecidableEq ι] {β : ι → Type} (f : (i : ι) → β i)
    (l : List ι) (i : ι) (h : i ∈ l) : tabulateOn f l i h = f i := by
  induction l with
  | nil => nomatch h
  | cons j l ih =>
    simp only [tabulateOn]
    split
    · next hij => subst hij; rfl
    · exact ih _

@[simp] theorem tabulate_eq {ι : Type} [DecidableEq ι] [Enum ι] {β : ι → Type}
    (f : (i : ι) → β i) : tabulate f = f :=
  funext fun i => tabulateOn_eq f _ i _

/-- Low priority, so a more specific instance wins. -/
instance (priority := low) funBEq {α β : Type} [Enum α] [BEq β] : BEq (α → β) where
  beq f g := (all (α := α)).all fun a => f a == g a

instance (priority := low) funHashable {α β : Type} [Enum α] [Hashable β] : Hashable (α → β) where
  hash f := (all (α := α)).foldl (fun h a => mixHash h (hash (f a))) 17

instance (priority := low) funRepr {α β : Type} [Enum α] [Repr α] [Repr β] : Repr (α → β) where
  reprPrec f _ := repr ((all (α := α)).map fun a => (a, f a))

end Enum

end Lanes
