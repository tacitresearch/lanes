/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Ported from Lean 4 core (`Lean.Data.Json.FromToJson.Basic`), Copyright (c) 2019 Gabriel Ebner,
Microsoft Corporation and Lean FRO, Apache 2.0.
Authors: Gabriel Ebner, Marc Huisinga
-/
module

public import Lanes.Data.Json.Printer

/-!
# Encoding and decoding typed values

`ToJson α` encodes a value of `α` as JSON and `FromJson α` decodes one, failing with a message when
the JSON has the wrong shape. Adapters use them to turn text into typed messages once, at the edge
(rule 2.2).

There is no `deriving` handler: one needs `Lean` meta code, which runtime modules cannot import.
Instances for structures are written by hand with `Json.mkObj`, `Json.opt` and `Json.getObjValAs?`.

The encodings are those of `Lean.Data.Json`.
-/

@[expose] public section

namespace Lanes

universe u v

class FromJson (α : Type u) where
  fromJson? : Json → Except String α

export FromJson (fromJson?)

class ToJson (α : Type u) where
  toJson : α → Json

export ToJson (toJson)

instance : FromJson Json := ⟨.ok⟩
instance : ToJson Json := ⟨id⟩

instance : FromJson JsonNumber := ⟨Json.getNum?⟩
instance : ToJson JsonNumber := ⟨.num⟩

instance : FromJson Unit where
  fromJson?
    | .obj #[] => .ok ()
    | j => .error s!"expected \{}, got '{j}'"
instance : ToJson Unit := ⟨fun _ => .obj #[]⟩

instance : FromJson Bool := ⟨Json.getBool?⟩
instance : ToJson Bool := ⟨.bool⟩

instance : FromJson Nat := ⟨Json.getNat?⟩
instance : ToJson Nat := ⟨fun n => .num n⟩

instance : FromJson Int := ⟨Json.getInt?⟩
instance : ToJson Int := ⟨fun n => .num n⟩

instance : FromJson String := ⟨Json.getStr?⟩
instance : ToJson String := ⟨.str⟩

instance {n : Nat} : FromJson (Fin n) where
  fromJson? j :=
    match j.getNat? with
    | .ok i => if h : i < n then .ok ⟨i, h⟩ else .error s!"expected a number below {n}, got {i}"
    | .error e => .error e
instance {n : Nat} : ToJson (Fin n) := ⟨fun i => .num i.val⟩

instance {α : Type u} [FromJson α] : FromJson (Array α) where
  fromJson?
    | .arr elems => elems.mapM fromJson?
    | j => .error s!"expected an array, got '{j}'"
instance {α : Type u} [ToJson α] : ToJson (Array α) := ⟨fun a => .arr (a.map toJson)⟩

instance {α : Type u} [FromJson α] : FromJson (List α) where
  fromJson?
    | .arr elems => elems.toList.mapM fromJson?
    | j => .error s!"expected an array, got '{j}'"
instance {α : Type u} [ToJson α] : ToJson (List α) := ⟨fun l => .arr (l.map toJson).toArray⟩

instance {α : Type u} [FromJson α] : FromJson (Option α) where
  fromJson?
    | .null => .ok none
    | j => (fromJson? j).map some
instance {α : Type u} [ToJson α] : ToJson (Option α) where
  toJson
    | none => .null
    | some a => toJson a

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (α × β) where
  fromJson? j :=
    match j.getArr? with
    | .ok elems =>
      if h : elems.size = 2 then
        match fromJson? elems[0], fromJson? elems[1] with
        | .ok a, .ok b => .ok (a, b)
        | .error e, _ => .error e
        | _, .error e => .error e
      else .error s!"expected an array of two elements, got '{j}'"
    | .error _ => .error s!"expected an array of two elements, got '{j}'"
instance {α : Type u} {β : Type v} [ToJson α] [ToJson β] : ToJson (α × β) where
  toJson pair := .arr #[toJson pair.1, toJson pair.2]

/-! ### Encodings that lose nothing -/

/-- `Option α` has no instance, because `some none` and `none` are both encoded as `null`. -/
class LawfulJson (α : Type u) [ToJson α] [FromJson α] : Prop where
  fromJson?_toJson (a : α) : fromJson? (toJson a) = .ok a

export LawfulJson (fromJson?_toJson)

instance : LawfulJson Json := ⟨fun _ => rfl⟩
instance : LawfulJson JsonNumber := ⟨fun _ => rfl⟩
instance : LawfulJson Unit := ⟨fun _ => rfl⟩
instance : LawfulJson Bool := ⟨fun _ => rfl⟩
instance : LawfulJson String := ⟨fun _ => rfl⟩
instance : LawfulJson Nat := ⟨fun n => by simp [toJson, fromJson?, Json.getNat?]⟩
instance : LawfulJson Int := ⟨fun n => by simp [toJson, fromJson?, Json.getInt?]⟩
instance {n : Nat} : LawfulJson (Fin n) := ⟨fun i => by simp [toJson, fromJson?, Json.getNat?]⟩

theorem mapM_fromJson?_toJson {α : Type u} [ToJson α] [FromJson α] [LawfulJson α] (l : List α) :
    l.mapM (fromJson? (α := α) ∘ toJson) = .ok l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fromJson?_toJson, ih]; rfl

instance {α : Type u} [ToJson α] [FromJson α] [LawfulJson α] : LawfulJson (List α) :=
  ⟨fun l => by simp [toJson, fromJson?, mapM_fromJson?_toJson]⟩

instance {α : Type u} [ToJson α] [FromJson α] [LawfulJson α] : LawfulJson (Array α) :=
  ⟨fun a => by
    simp [toJson, fromJson?, Array.mapM_eq_mapM_toList, mapM_fromJson?_toJson]; rfl⟩

instance {α : Type u} {β : Type v} [ToJson α] [FromJson α] [LawfulJson α]
    [ToJson β] [FromJson β] [LawfulJson β] : LawfulJson (α × β) :=
  ⟨fun pair => by simp [toJson, fromJson?, Json.getArr?, fromJson?_toJson]⟩

namespace Json

/-- A missing field decodes as `null` does, so a field of type `Option α` may be left out. -/
def getObjValAs? (j : Json) (α : Type u) [FromJson α] (key : String) : Except String α :=
  fromJson? (j.getObjValD key)

/-- No field if there is no value. For building the argument of `Json.mkObj`. -/
def opt {α : Type u} [ToJson α] (key : String) : (value : Option α) → List (String × Json)
  | none => []
  | some a => [(key, toJson a)]

end Json

end Lanes
