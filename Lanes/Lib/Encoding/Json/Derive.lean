/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.Classes
public import Lanes.Lib.Encoding.Json.BasicSound
public import Lanes.Proof.List.Basic

/-!
# What `lanes_data` derives JSON with

`lanes_data … deriving ToJson, FromJson` (`Lanes/Data/Declare.lean`) builds a `Json.Codec` from
the pieces here and makes the instances from it, `LawfulJson` and `NonNullJson` among them. Each
piece carries its law, so the law of the whole holds by construction: no proof is written per
type but the distinctness of its keys and tags, which `decide` checks.

The encoding:

- A structure is an object with a field per Lean field, named as the field is. A field whose
  value is encoded as `null` is left out, and a field that is missing reads as `null`: so a
  field of type `Option α` is left out when it is `none`.
- A constructor is an object with one field, the constructor's name, holding an object of its
  arguments, written as a structure's fields. A constructor whose arguments are all left out, one
  with none among them, is written as its name, a string.

These are the encodings of `Lean`'s own `deriving ToJson, FromJson`, but that Lean leaves out
only a field whose name ends in `?`, and writes `null` for the others, and so writes a
constructor with arguments as an object always. What Lean writes reads back here.
-/

@[expose] public section

namespace Lanes.Json

/-- An encoding with its laws, from which the instances are made. -/
structure Codec (α : Type) where
  toJson : α → Json
  fromJson? : Json → Except String α
  fromJson?_toJson : ∀ a, fromJson? (toJson a) = .ok a
  toJson_ne_null : ∀ a, toJson a ≠ .null

/-- An object's fields: a structure, or a constructor's arguments. `read` takes the value of each
key; the law says it reads back what `write` wrote, when each key gives what was written. -/
structure Fields (α : Type) where
  keys : List String
  write : α → List (String × Json)
  keys_write : ∀ a, (write a).map (·.1) = keys
  read : (String → Json) → Except String α
  read_write : ∀ a (look : String → Json), (∀ p ∈ write a, look p.1 = p.2) → read look = .ok a

namespace Fields

variable {α β : Type}

def field (key : String) {β : Type} [ToJson β] [FromJson β] [LawfulJson β] : Fields β where
  keys := [key]
  write b := [(key, toJson b)]
  keys_write _ := rfl
  read look := (fromJson? (look key)).mapError (s!"{key.quote}: " ++ ·)
  read_write b look h := by rw [h _ (List.mem_singleton_self _), fromJson?_toJson]; rfl

def unit : Fields Unit where
  keys := []
  write _ := []
  keys_write _ := rfl
  read _ := .ok ()
  read_write _ _ _ := rfl

def pair (a : Fields α) (b : Fields β) : Fields (α × β) where
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
def map (c : Fields β) (to : α → β) (back : β → α) (h : ∀ a, back (to a) = a) : Fields α where
  keys := c.keys
  write a := c.write (to a)
  keys_write a := c.keys_write (to a)
  read look := back <$> c.read look
  read_write a look hl := by rw [c.read_write (to a) look hl]; simp [Functor.map, Except.map, h]

/-- The object: the fields that are not `null`. -/
def object (c : Fields α) (a : α) : Json :=
  mkObj ((c.write a).filter (·.2 != .null))

def readObject (c : Fields α) : Json → Except String α
  | j@(.obj _) => c.read j.getObjValD
  | j => .error s!"expected an object, got '{j}'"

theorem getObjValD_object (c : Fields α) (h : c.keys.Nodup) (a : α) :
    ∀ p ∈ c.write a, (c.object a).getObjValD p.1 = p.2 := by
  intro p hp
  have hone : (c.write a).filter (fun q => q.1 == p.1) = [p] :=
    filter_key_eq_singleton (c.keys_write a ▸ h) hp
  have hkept : ((c.write a).filter (·.2 != .null)).filter (·.1 == p.1)
      = [p].filter (·.2 != .null) := by
    rw [List.filter_filter, ← hone, List.filter_filter]
    congr 1
    funext q
    exact Bool.and_comm _ _
  unfold getObjValD object
  by_cases hn : p.2 = .null
  · have : [p].filter (·.2 != .null) = [] := by simp [hn]
    split
    · rename_i v hv
      rw [getObjVal?_mkObj, hkept, this] at hv
      cases hv
    · exact hn.symm
  · have : [p].filter (·.2 != .null) = [p] := by simp [hn]
    rw [(getObjVal?_mkObj (v := p.2)).mpr (by rw [hkept, this]; rfl)]

theorem readObject_object (c : Fields α) (h : c.keys.Nodup) (a : α) :
    c.readObject (c.object a) = .ok a :=
  c.read_write a _ (c.getObjValD_object h a)

theorem object_ne_null (c : Fields α) (a : α) : c.object a ≠ .null := nofun

end Fields

/-- A structure, written as an object of its fields. -/
def Codec.object {α : Type} (c : Fields α) (h : c.keys.Nodup) : Codec α where
  toJson := c.object
  fromJson? := c.readObject
  fromJson?_toJson := c.readObject_object h
  toJson_ne_null := c.object_ne_null

/-- The constructors of an inductive type: each value as its constructor's name and the object of
its arguments. -/
structure Alts (α : Type) where
  tags : List String
  write : α → String × Json
  tag_mem : ∀ a, (write a).1 ∈ tags
  read : String → Json → Except String α
  read_write : ∀ a, read (write a).1 (write a).2 = .ok a

namespace Alts

variable {α β : Type}

def ctor (tag : String) (c : Fields α) (h : c.keys.Nodup) : Alts α where
  tags := [tag]
  write a := (tag, c.object a)
  tag_mem _ := List.mem_singleton_self _
  read _ := c.readObject
  read_write := c.readObject_object h

/-- The constructors of `α`, then those of `β`, which have other names. -/
def sum (a : Alts α) (b : Alts β) (h : (a.tags.all fun t => !b.tags.contains t) = true) :
    Alts (α ⊕ β) where
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

def map (c : Alts β) (to : α → β) (back : β → α) (h : ∀ a, back (to a) = a) : Alts α where
  tags := c.tags
  write a := c.write (to a)
  tag_mem a := c.tag_mem (to a)
  read t j := back <$> c.read t j
  read_write a := by rw [c.read_write (to a)]; simp [Functor.map, Except.map, h]

end Alts

/-- A constructor's name and the object of its arguments: a name alone stands for no argument. -/
def untag : Json → Option (String × Json)
  | .str t => some (t, .obj #[])
  | .obj #[(t, args)] => some (t, args)
  | _ => none

def tag (t : String) (args : Json) : Json :=
  if args = .obj #[] then .str t else .obj #[(t, args)]

theorem untag_tag (t : String) (args : Json) : untag (tag t args) = some (t, args) := by
  unfold tag
  split
  · rename_i h; rw [h]; rfl
  · rfl

/-- An inductive type, written as its constructors. -/
def Codec.ofAlts {α : Type} (c : Alts α) : Codec α where
  toJson a := tag (c.write a).1 (c.write a).2
  fromJson? j :=
    match untag j with
    | some (t, args) =>
      if c.tags.contains t then c.read t args else .error s!"no constructor is named {t.quote}"
    | none => .error s!"expected a constructor's name, or an object of one field, got '{j}'"
  fromJson?_toJson a := by
    simp only [untag_tag, List.elem_eq_mem, c.tag_mem a, decide_true, ↓reduceIte, c.read_write]
  toJson_ne_null a := by unfold tag; split <;> nofun

end Lanes.Json
