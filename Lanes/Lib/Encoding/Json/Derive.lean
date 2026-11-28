/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.Classes
public import Lanes.Lib.Encoding.Fields
public import Lanes.Lib.Encoding.Json.BasicSound
public import Lanes.Proof.List.Basic

/-!
# What `lanes_data` derives JSON with

`lanes_data … deriving ToJson, FromJson` (`Lanes/Data/Declare.lean`) builds a `Json.Codec` from
the pieces here and those of `Lanes/Lib/Encoding/Fields.lean`, and makes the instances from it,
`LawfulJson` and `NonNullJson` among them. Each piece carries its law, so the law of the whole
holds by construction: no proof is written per type but the distinctness of its keys and tags,
which `decide` checks.

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

/-- An object's fields, as JSON. -/
abbrev Fields (α : Type) := Lanes.Fields Json α

namespace Fields

variable {α : Type}

def field (key : String) {β : Type} [ToJson β] [FromJson β] [LawfulJson β] : Fields β where
  keys := [key]
  write b := [(key, toJson b)]
  keys_write _ := rfl
  read look := (fromJson? (look key)).mapError (s!"{key.quote}: " ++ ·)
  read_write b look h := by rw [h _ (List.mem_singleton_self _), fromJson?_toJson]; rfl

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

/-- The constructors of an inductive type, as JSON. -/
abbrev Alts (α : Type) := Lanes.Alts Json α

namespace Alts

variable {α : Type}

def ctor (tag : String) (c : Fields α) (h : c.keys.Nodup) : Alts α where
  tags := [tag]
  write a := (tag, c.object a)
  tag_mem _ := List.mem_singleton_self _
  read _ := c.readObject
  read_write := c.readObject_object h

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
