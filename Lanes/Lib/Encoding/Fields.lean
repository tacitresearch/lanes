/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Fields and constructors, for any format of values

What `lanes_data` derives JSON and CBOR from (`Lanes/Lib/Encoding/Json/Derive.lean`,
`Lanes/Lib/Encoding/Cbor/Derive.lean`). A structure, or a constructor's arguments, is an object of
named fields, and an inductive type its constructors, each a name and the object of its
arguments. The pieces here carry their laws and know nothing of the values `V` they write: a
format adds a field of one type, the object, and the tagging.
-/

@[expose] public section

namespace Lanes

/-- An object's fields: a structure, or a constructor's arguments. `read` takes the value of each
key; the law says it reads back what `write` wrote, when each key gives what was written. -/
structure Fields (V α : Type) where
  keys : List String
  write : α → List (String × V)
  keys_write : ∀ a, (write a).map (·.1) = keys
  read : (String → V) → Except String α
  read_write : ∀ a (look : String → V), (∀ p ∈ write a, look p.1 = p.2) → read look = .ok a

namespace Fields

variable {V α β : Type}

def unit : Fields V Unit where
  keys := []
  write _ := []
  keys_write _ := rfl
  read _ := .ok ()
  read_write _ _ _ := rfl

def pair (a : Fields V α) (b : Fields V β) : Fields V (α × β) where
  keys := a.keys ++ b.keys
  write x := a.write x.1 ++ b.write x.2
  keys_write x := by simp [a.keys_write, b.keys_write]
  read look := do
    let x ← a.read look
    let y ← b.read look
    return (x, y)
  read_write x look h := by
    rw [a.read_write x.1 look fun p hp => h p (List.mem_append_left _ hp),
      b.read_write x.2 look fun p hp => h p (List.mem_append_right _ hp)]
    rfl

/-- A type written as another. -/
def map (c : Fields V β) (to : α → β) (back : β → α) (h : ∀ a, back (to a) = a) : Fields V α where
  keys := c.keys
  write a := c.write (to a)
  keys_write a := c.keys_write (to a)
  read look := back <$> c.read look
  read_write a look hl := by rw [c.read_write (to a) look hl]; simp [Functor.map, Except.map, h]

end Fields

/-- The constructors of an inductive type: each value as its constructor's name and the object of
its arguments. -/
structure Alts (V α : Type) where
  tags : List String
  write : α → String × V
  tag_mem : ∀ a, (write a).1 ∈ tags
  read : String → V → Except String α
  read_write : ∀ a, read (write a).1 (write a).2 = .ok a

namespace Alts

variable {V α β : Type}

/-- The constructors of `α`, then those of `β`, which have other names. -/
def sum (a : Alts V α) (b : Alts V β) (h : (a.tags.all fun t => !b.tags.contains t) = true) :
    Alts V (α ⊕ β) where
  tags := a.tags ++ b.tags
  write
    | .inl x => a.write x
    | .inr y => b.write y
  tag_mem
    | .inl x => List.mem_append_left _ (a.tag_mem x)
    | .inr y => List.mem_append_right _ (b.tag_mem y)
  read t j := if a.tags.contains t then .inl <$> a.read t j else .inr <$> b.read t j
  read_write
    | .inl x => by
      simp only [List.elem_eq_mem, a.tag_mem x, decide_true, ↓reduceIte, a.read_write x]; rfl
    | .inr y => by
      have hb := b.tag_mem y
      have : a.tags.contains (b.write y).1 = false := by
        rw [Bool.eq_false_iff]
        intro ha
        have := List.all_eq_true.mp h _ (List.elem_iff.mp ha)
        simp [hb] at this
      simp only [this, Bool.false_eq_true, ↓reduceIte, b.read_write y]; rfl

def map (c : Alts V β) (to : α → β) (back : β → α) (h : ∀ a, back (to a) = a) : Alts V α where
  tags := c.tags
  write a := c.write (to a)
  tag_mem a := c.tag_mem (to a)
  read t j := back <$> c.read t j
  read_write a := by rw [c.read_write (to a)]; simp [Functor.map, Except.map, h]

end Alts

end Lanes
