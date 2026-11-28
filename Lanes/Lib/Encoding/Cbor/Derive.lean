/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Cbor.Classes
public import Lanes.Lib.Encoding.Fields
public import Lanes.Proof.List.Basic

/-!
# What `lanes_data` derives CBOR with

`lanes_data … deriving ToCbor, FromCbor` (`Lanes/Data/Declare.lean`) builds a `Cbor.Codec` from
the pieces of `Lanes/Lib/Encoding/Fields.lean` and those here, as it builds a `Json.Codec`
(`Lanes/Lib/Encoding/Json/Derive.lean`), and makes the instances from it, `LawfulCbor` and
`NonNullCbor` among them. The law of the whole holds by construction.

The shapes are JSON's, so that a type's CBOR and its JSON agree:

- A structure is a map with a text key per Lean field, named as the field is, in the order of
  the fields. A field whose value is `null` is left out, and a field that is missing reads as
  `null`: so a field of type `Option α` is left out when it is `none`.
- A constructor is a map of one entry, the constructor's name as text, holding the map of its
  arguments; a constructor whose arguments are all left out is its name, as text.
-/

@[expose] public section

namespace Lanes.Cbor

/-- An encoding with its laws, from which the instances are made. -/
structure Codec (α : Type) where
  toCbor : α → Cbor
  fromCbor? : Cbor → Except String α
  fromCbor?_toCbor : ∀ a, fromCbor? (toCbor a) = .ok a
  toCbor_ne_null : ∀ a, toCbor a ≠ .null

/-- An object's fields, as a CBOR map. -/
abbrev Fields (α : Type) := Lanes.Fields Cbor α

/-- The value of a text key, the first if there are two, and `null` if there is none. -/
def look (entries : List (Cbor × Cbor)) (key : String) : Cbor := (lookup entries key).getD .null

namespace Fields

variable {α : Type}

def field (key : String) {β : Type} [ToCbor β] [FromCbor β] [LawfulCbor β] : Fields β where
  keys := [key]
  write b := [(key, toCbor b)]
  keys_write _ := rfl
  read look := (fromCbor? (look key)).mapError (s!"{key.quote}: " ++ ·)
  read_write b look h := by rw [h _ (List.mem_singleton_self _), fromCbor?_toCbor]; rfl

/-- The map: the fields that are not `null`, each keyed by its name as text. -/
def object (c : Fields α) (a : α) : Cbor :=
  .map (((c.write a).filter (·.2 != .null)).map fun p => (.text p.1, p.2))

def readObject (c : Fields α) : Cbor → Except String α
  | .map entries => c.read (look entries)
  | v => .error s!"expected a map, got {repr v}"

theorem look_object (c : Fields α) (h : c.keys.Nodup) (a : α) :
    ∀ p ∈ c.write a, look (((c.write a).filter (·.2 != .null)).map fun p => (.text p.1, p.2)) p.1
      = p.2 := by
  intro p hp
  have hone : (c.write a).filter (fun q => q.1 == p.1) = [p] :=
    filter_key_eq_singleton (c.keys_write a ▸ h) hp
  have hkey : ((fun e : Cbor × Cbor => e.1 == .text p.1) ∘
      fun q : String × Cbor => (Cbor.text q.1, q.2)) = fun q => q.1 == p.1 := by
    funext q
    rw [Bool.eq_iff_iff]
    simp only [Function.comp, beq_iff_eq, Cbor.text.injEq]
  have hkept : ((c.write a).filter (·.2 != .null)).filter (·.1 == p.1)
      = [p].filter (·.2 != .null) := by
    rw [List.filter_filter, ← hone, List.filter_filter]
    congr 1
    funext q
    exact Bool.and_comm _ _
  unfold look lookup
  rw [List.find?_map, hkey, ← List.head?_filter, hkept]
  by_cases hn : p.2 = .null
  · simp [hn]
  · simp [hn]

theorem readObject_object (c : Fields α) (h : c.keys.Nodup) (a : α) :
    c.readObject (c.object a) = .ok a :=
  c.read_write a _ (c.look_object h a)

end Fields

/-- A structure, written as a map of its fields. -/
def Codec.object {α : Type} (c : Fields α) (h : c.keys.Nodup) : Codec α where
  toCbor := c.object
  fromCbor? := c.readObject
  fromCbor?_toCbor := c.readObject_object h
  toCbor_ne_null _ := nofun

/-- The constructors of an inductive type, as CBOR. -/
abbrev Alts (α : Type) := Lanes.Alts Cbor α

def Alts.ctor {α : Type} (tag : String) (c : Fields α) (h : c.keys.Nodup) : Alts α where
  tags := [tag]
  write a := (tag, c.object a)
  tag_mem _ := List.mem_singleton_self _
  read _ := c.readObject
  read_write := c.readObject_object h

/-- A constructor's name and the map of its arguments: a name alone stands for no argument. -/
def constructor? : Cbor → Option (String × Cbor)
  | .text t => some (t, .map [])
  | .map [(.text t, args)] => some (t, args)
  | _ => none

def constructor (t : String) (args : Cbor) : Cbor :=
  if args = .map [] then .text t else .map [(.text t, args)]

theorem constructor?_constructor (t : String) (args : Cbor) :
    constructor? (constructor t args) = some (t, args) := by
  unfold constructor
  split
  · rename_i h; rw [h]; rfl
  · rfl

/-- An inductive type, written as its constructors. -/
def Codec.ofAlts {α : Type} (c : Alts α) : Codec α where
  toCbor a := constructor (c.write a).1 (c.write a).2
  fromCbor? v :=
    match constructor? v with
    | some (t, args) =>
      if c.tags.contains t then c.read t args else .error s!"no constructor is named {t.quote}"
    | none => .error s!"expected a constructor's name, or a map of one entry, got {repr v}"
  fromCbor?_toCbor a := by
    simp only [constructor?_constructor, List.elem_eq_mem, c.tag_mem a, decide_true, ↓reduceIte,
      c.read_write]
  toCbor_ne_null a := by unfold constructor; split <;> nofun

end Lanes.Cbor
