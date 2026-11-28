/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Ported from Lean 4 core (`Lean.Data.Json.FromToJson.Basic`), Copyright (c) 2019 Gabriel Ebner,
Microsoft Corporation and Lean FRO, Apache 2.0.
Authors: Gabriel Ebner, Marc Huisinga
-/
module

public import Lanes.Lib.Encoding.Json.Printer

/-!
# Encoding and decoding typed values

`ToJson α` encodes a value of `α` as JSON and `FromJson α` decodes one, failing with a message when
the JSON has the wrong shape. Adapters use them to turn text into typed messages once, at the edge
(rule 2.2).

Lean's `deriving` handlers need `Lean` meta code, which runtime modules cannot import. A type
declared with `lanes_data` derives its instances instead (`Lanes/Lib/Encoding/Json/Derive.lean`).

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

/-- A number within the range of a signed 64-bit integer. -/
instance : FromJson Int64 where
  fromJson? j :=
    match j.getInt? with
    | .ok i =>
      if h : Int64.minValue.toInt ≤ i ∧ i ≤ Int64.maxValue.toInt then .ok (Int64.ofIntLE i h.1 h.2)
      else .error s!"expected a 64-bit integer, got {i}"
    | .error e => .error e
instance : ToJson Int64 := ⟨fun i => .num i.toInt⟩

/-- Read back only if the property holds. -/
instance {α : Type u} {p : α → Prop} [DecidablePred p] [FromJson α] : FromJson {a // p a} where
  fromJson? j :=
    match (fromJson? j : Except String α) with
    | .ok a => if h : p a then .ok ⟨a, h⟩ else .error s!"a value does not have its property: '{j}'"
    | .error e => .error e
instance {α : Type u} {p : α → Prop} [ToJson α] : ToJson {a // p a} := ⟨fun a => toJson a.val⟩

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

/-- `Option α` has an instance only when `α` is never encoded as `null` (`NonNullJson`), the
encoding of `none`: `some none` and `none` would both be `null`. -/
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

instance : LawfulJson Int64 :=
  ⟨fun i => by
    have : -9223372036854775808 ≤ i.toInt := i.minValue_le_toInt
    simp [toJson, fromJson?, Json.getInt?, i.toInt_le, this]⟩

instance {α : Type u} {p : α → Prop} [DecidablePred p] [ToJson α] [FromJson α] [LawfulJson α] :
    LawfulJson {a // p a} :=
  ⟨fun a => by simp [toJson, fromJson?, fromJson?_toJson a.val, a.property]⟩

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

/-- `toJson` never gives `null`, the encoding of `none`, so `Option α` loses nothing. -/
class NonNullJson (α : Type u) [ToJson α] : Prop where
  toJson_ne_null (a : α) : toJson a ≠ .null

export NonNullJson (toJson_ne_null)

instance : NonNullJson Unit := ⟨fun _ => nofun⟩
instance : NonNullJson Bool := ⟨fun _ => nofun⟩
instance : NonNullJson Nat := ⟨fun _ => nofun⟩
instance : NonNullJson Int := ⟨fun _ => nofun⟩
instance : NonNullJson Int64 := ⟨fun _ => nofun⟩
instance : NonNullJson String := ⟨fun _ => nofun⟩
instance : NonNullJson JsonNumber := ⟨fun _ => nofun⟩
instance {n : Nat} : NonNullJson (Fin n) := ⟨fun _ => nofun⟩
instance {α : Type u} [ToJson α] : NonNullJson (List α) := ⟨fun _ => nofun⟩
instance {α : Type u} [ToJson α] : NonNullJson (Array α) := ⟨fun _ => nofun⟩
instance {α : Type u} {β : Type v} [ToJson α] [ToJson β] : NonNullJson (α × β) := ⟨fun _ => nofun⟩
instance {α : Type u} {p : α → Prop} [ToJson α] [NonNullJson α] : NonNullJson {a // p a} :=
  ⟨fun a => toJson_ne_null a.val⟩

/-! The law for each instance, by name, and what holds of `Option`. -/

theorem fromJson?_toJson_json (j : Json) : fromJson? (toJson j) = .ok j := fromJson?_toJson j
theorem fromJson?_toJson_jsonNumber (n : JsonNumber) : fromJson? (toJson n) = .ok n :=
  fromJson?_toJson n
theorem fromJson?_toJson_unit (u : Unit) : fromJson? (toJson u) = .ok u := fromJson?_toJson u
theorem fromJson?_toJson_bool (b : Bool) : fromJson? (toJson b) = .ok b := fromJson?_toJson b
theorem fromJson?_toJson_nat (n : Nat) : fromJson? (toJson n) = .ok n := fromJson?_toJson n
theorem fromJson?_toJson_int (i : Int) : fromJson? (toJson i) = .ok i := fromJson?_toJson i
theorem fromJson?_toJson_string (s : String) : fromJson? (toJson s) = .ok s := fromJson?_toJson s
theorem fromJson?_toJson_fin {n : Nat} (i : Fin n) : fromJson? (toJson i) = .ok i :=
  fromJson?_toJson i

theorem fromJson?_toJson_array {α : Type u} [ToJson α] [FromJson α] [LawfulJson α]
    (a : Array α) : fromJson? (toJson a) = .ok a := fromJson?_toJson a

theorem fromJson?_toJson_list {α : Type u} [ToJson α] [FromJson α] [LawfulJson α] (l : List α) :
    fromJson? (toJson l) = .ok l := fromJson?_toJson l

theorem fromJson?_toJson_prod {α : Type u} {β : Type v} [ToJson α] [FromJson α] [LawfulJson α]
    [ToJson β] [FromJson β] [LawfulJson β] (pair : α × β) :
    fromJson? (toJson pair) = .ok pair := fromJson?_toJson pair

theorem fromJson?_toJson_none {α : Type u} [ToJson α] [FromJson α] :
    (fromJson? (toJson (none : Option α)) : Except String (Option α)) = .ok none := rfl

/-- `some a` reads back when `a` is not encoded as `null`, the encoding of `none`. -/
theorem fromJson?_toJson_some {α : Type u} [ToJson α] [FromJson α] [LawfulJson α] {a : α}
    (h : toJson a ≠ .null) : fromJson? (toJson (some a)) = .ok (some a) := by
  show (match toJson a with
    | .null => (.ok none : Except String (Option α))
    | j => (fromJson? j : Except String α).map some) = _
  split
  · exact absurd ‹_› h
  · rw [fromJson?_toJson]; rfl

instance {α : Type u} [ToJson α] [FromJson α] [LawfulJson α] [NonNullJson α] :
    LawfulJson (Option α) :=
  ⟨fun | none => rfl | some a => fromJson?_toJson_some (toJson_ne_null a)⟩

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
