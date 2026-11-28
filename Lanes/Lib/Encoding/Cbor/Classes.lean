/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Cbor.Basic
public import Lanes.Lib.Encoding.Digits

/-!
# Typed values to and from CBOR

`ToCbor α` writes a value of `α` as a `Cbor` value and `FromCbor α` reads one back, failing with a
message when the value has the wrong shape; `LawfulCbor` says that what is written reads back,
and `NonNullCbor` that nothing is written as `null`, the encoding of `none`. The shapes are JSON's
(`Lanes/Lib/Encoding/Json/Classes.lean`), so a type's CBOR and its JSON agree: a pair is an array
of two, `Unit` an empty map, `none` is `null`. CBOR adds what JSON lacks: byte strings, and
integers of each sign apart.

A natural number or an integer that does not fit the 64 bits of an argument is a bignum (RFC 8949
§3.4.3): tag 2, or tag 3 for `-1 - n`, holding the big-endian bytes of `n` with no leading zero.
-/

@[expose] public section

namespace Lanes

universe u v

class ToCbor (α : Type u) where
  toCbor : α → Cbor

export ToCbor (toCbor)

class FromCbor (α : Type u) where
  fromCbor? : Cbor → Except String α

export FromCbor (fromCbor?)

class LawfulCbor (α : Type u) [ToCbor α] [FromCbor α] : Prop where
  fromCbor?_toCbor (a : α) : fromCbor? (toCbor a) = .ok a

export LawfulCbor (fromCbor?_toCbor)

/-- `toCbor` never gives `null`, the encoding of `none`, so `Option α` loses nothing. -/
class NonNullCbor (α : Type u) [ToCbor α] : Prop where
  toCbor_ne_null (a : α) : toCbor a ≠ .null

export NonNullCbor (toCbor_ne_null)

namespace Cbor

/-- The big-endian bytes of `n`, with no leading zero. -/
def bigBytes (n : Nat) : ByteArray := ((Digits.digits 256 n).map Nat.toUInt8).toByteArray

/-- The number big-endian bytes spell. -/
def bigNat (b : ByteArray) : Nat := Digits.join 256 (b.data.toList.map UInt8.toNat)

theorem bigNat_bigBytes (n : Nat) : bigNat (bigBytes n) = n := by
  unfold bigNat bigBytes
  rw [List.toList_data_toByteArray, List.map_map]
  conv => rhs; rw [← Digits.join_digits (b := 256) n]
  congr 1
  conv => rhs; rw [← List.map_id (Digits.digits 256 n)]
  refine List.map_congr_left fun d hd => ?_
  have := Digits.lt_of_mem_digits (by decide) hd
  simp [Nat.mod_eq_of_lt this]

/-- A natural number: an unsigned integer, or a bignum. -/
def ofNat (n : Nat) : Cbor := if n < 2 ^ 64 then .uint n.toUInt64 else .tag 2 (.bytes (bigBytes n))

def nat? : Cbor → Except String Nat
  | .uint n => .ok n.toNat
  | .tag 2 (.bytes b) => .ok (bigNat b)
  | v => .error s!"expected an unsigned integer, got {repr v}"

theorem nat?_ofNat (n : Nat) : nat? (ofNat n) = .ok n := by
  unfold ofNat
  split
  · simp [nat?, Nat.mod_eq_of_lt ‹_›]
  · simp [nat?, bigNat_bigBytes]

/-- An integer: `ofNat`, or `-1 - n` as a negative integer or a bignum. -/
def ofInt (i : Int) : Cbor :=
  if 0 ≤ i then ofNat i.toNat
  else
    let n := (-1 - i).toNat
    if n < 2 ^ 64 then .nint n.toUInt64 else .tag 3 (.bytes (bigBytes n))

def int? : Cbor → Except String Int
  | .uint n => .ok n.toNat
  | .nint n => .ok (-1 - (n.toNat : Int))
  | .tag 2 (.bytes b) => .ok (bigNat b)
  | .tag 3 (.bytes b) => .ok (-1 - (bigNat b : Int))
  | v => .error s!"expected an integer, got {repr v}"

theorem int?_ofInt (i : Int) : int? (ofInt i) = .ok i := by
  unfold ofInt ofNat
  split
  · split
    · simp [int?, Nat.mod_eq_of_lt ‹_›]; omega
    · simp [int?, bigNat_bigBytes]; omega
  · dsimp only
    split
    · simp [int?, Nat.mod_eq_of_lt ‹_›]; omega
    · simp [int?, bigNat_bigBytes]; omega

theorem ofNat_ne_null (n : Nat) : ofNat n ≠ .null := by unfold ofNat; split <;> nofun

theorem ofInt_ne_null (i : Int) : ofInt i ≠ .null := by
  unfold ofInt; split
  · exact ofNat_ne_null _
  · dsimp only; split <;> nofun

end Cbor

instance : ToCbor Cbor := ⟨id⟩
instance : FromCbor Cbor := ⟨.ok⟩
instance : LawfulCbor Cbor := ⟨fun _ => rfl⟩

instance : ToCbor Unit := ⟨fun _ => .map []⟩
instance : FromCbor Unit where
  fromCbor?
    | .map [] => .ok ()
    | v => .error s!"expected an empty map, got {repr v}"
instance : LawfulCbor Unit := ⟨fun _ => rfl⟩
instance : NonNullCbor Unit := ⟨fun _ => nofun⟩

instance : ToCbor Bool := ⟨.bool⟩
instance : FromCbor Bool where
  fromCbor?
    | .bool b => .ok b
    | v => .error s!"expected a boolean, got {repr v}"
instance : LawfulCbor Bool := ⟨fun _ => rfl⟩
instance : NonNullCbor Bool := ⟨fun _ => nofun⟩

instance : ToCbor Nat := ⟨Cbor.ofNat⟩
instance : FromCbor Nat := ⟨Cbor.nat?⟩
instance : LawfulCbor Nat := ⟨Cbor.nat?_ofNat⟩
instance : NonNullCbor Nat := ⟨Cbor.ofNat_ne_null⟩

instance : ToCbor Int := ⟨Cbor.ofInt⟩
instance : FromCbor Int := ⟨Cbor.int?⟩
instance : LawfulCbor Int := ⟨Cbor.int?_ofInt⟩
instance : NonNullCbor Int := ⟨Cbor.ofInt_ne_null⟩

instance {n : Nat} : ToCbor (Fin n) := ⟨fun i => Cbor.ofNat i.val⟩
instance {n : Nat} : FromCbor (Fin n) where
  fromCbor? v :=
    match Cbor.nat? v with
    | .ok i => if h : i < n then .ok ⟨i, h⟩ else .error s!"expected a number below {n}, got {i}"
    | .error e => .error e
instance {n : Nat} : LawfulCbor (Fin n) :=
  ⟨fun i => by simp [toCbor, fromCbor?, Cbor.nat?_ofNat]⟩
instance {n : Nat} : NonNullCbor (Fin n) := ⟨fun i => Cbor.ofNat_ne_null i.val⟩

instance : ToCbor Int64 := ⟨fun i => Cbor.ofInt i.toInt⟩
instance : FromCbor Int64 where
  fromCbor? v :=
    match Cbor.int? v with
    | .ok i =>
      if h : Int64.minValue.toInt ≤ i ∧ i ≤ Int64.maxValue.toInt then .ok (Int64.ofIntLE i h.1 h.2)
      else .error s!"expected a 64-bit integer, got {i}"
    | .error e => .error e
instance : LawfulCbor Int64 :=
  ⟨fun i => by
    have : -9223372036854775808 ≤ i.toInt := i.minValue_le_toInt
    simp [toCbor, fromCbor?, Cbor.int?_ofInt, i.toInt_le, this]⟩
instance : NonNullCbor Int64 := ⟨fun i => Cbor.ofInt_ne_null i.toInt⟩

instance : ToCbor UInt8 := ⟨fun u => .uint u.toUInt64⟩
instance : FromCbor UInt8 where
  fromCbor?
    | .uint n => if n.toNat < 2 ^ 8 then .ok n.toUInt8 else .error s!"expected a byte, got {n}"
    | v => .error s!"expected an unsigned integer, got {repr v}"
instance : LawfulCbor UInt8 := ⟨fun u => by simp [toCbor, fromCbor?, u.toNat_lt]⟩
instance : NonNullCbor UInt8 := ⟨fun _ => nofun⟩

instance : ToCbor UInt16 := ⟨fun u => .uint u.toUInt64⟩
instance : FromCbor UInt16 where
  fromCbor?
    | .uint n =>
      if n.toNat < 2 ^ 16 then .ok n.toUInt16 else .error s!"expected a 16-bit number, got {n}"
    | v => .error s!"expected an unsigned integer, got {repr v}"
instance : LawfulCbor UInt16 := ⟨fun u => by simp [toCbor, fromCbor?, u.toNat_lt]⟩
instance : NonNullCbor UInt16 := ⟨fun _ => nofun⟩

instance : ToCbor UInt32 := ⟨fun u => .uint u.toUInt64⟩
instance : FromCbor UInt32 where
  fromCbor?
    | .uint n =>
      if n.toNat < 2 ^ 32 then .ok n.toUInt32 else .error s!"expected a 32-bit number, got {n}"
    | v => .error s!"expected an unsigned integer, got {repr v}"
instance : LawfulCbor UInt32 := ⟨fun u => by simp [toCbor, fromCbor?, u.toNat_lt]⟩
instance : NonNullCbor UInt32 := ⟨fun _ => nofun⟩

instance : ToCbor UInt64 := ⟨.uint⟩
instance : FromCbor UInt64 where
  fromCbor?
    | .uint n => .ok n
    | v => .error s!"expected an unsigned integer, got {repr v}"
instance : LawfulCbor UInt64 := ⟨fun _ => rfl⟩
instance : NonNullCbor UInt64 := ⟨fun _ => nofun⟩

instance : ToCbor String := ⟨.text⟩
instance : FromCbor String where
  fromCbor?
    | .text s => .ok s
    | v => .error s!"expected text, got {repr v}"
instance : LawfulCbor String := ⟨fun _ => rfl⟩
instance : NonNullCbor String := ⟨fun _ => nofun⟩

instance : ToCbor ByteArray := ⟨.bytes⟩
instance : FromCbor ByteArray where
  fromCbor?
    | .bytes b => .ok b
    | v => .error s!"expected bytes, got {repr v}"
instance : LawfulCbor ByteArray := ⟨fun _ => rfl⟩
instance : NonNullCbor ByteArray := ⟨fun _ => nofun⟩

instance {α : Type u} [ToCbor α] : ToCbor (Option α) where
  toCbor
    | none => .null
    | some a => toCbor a
instance {α : Type u} [FromCbor α] : FromCbor (Option α) where
  fromCbor?
    | .null => .ok none
    | v => (fromCbor? v).map some

/-- `Option α` has an instance only when `α` is never `null`: `some none` and `none` would both
be `null`. -/
instance {α : Type u} [ToCbor α] [FromCbor α] [LawfulCbor α] [NonNullCbor α] :
    LawfulCbor (Option α) :=
  ⟨fun
    | none => rfl
    | some a => by
      show (match toCbor a with
        | .null => (.ok none : Except String (Option α))
        | v => (fromCbor? v : Except String α).map some) = _
      split
      · exact absurd ‹_› (toCbor_ne_null a)
      · rw [fromCbor?_toCbor]; rfl⟩

instance {α : Type u} [ToCbor α] : ToCbor (List α) := ⟨fun l => .array (l.map toCbor)⟩
instance {α : Type u} [FromCbor α] : FromCbor (List α) where
  fromCbor?
    | .array items => items.mapM fromCbor?
    | v => .error s!"expected an array, got {repr v}"

theorem Cbor.mapM_fromCbor?_toCbor {α : Type u} [ToCbor α] [FromCbor α] [LawfulCbor α]
    (l : List α) : (l.map toCbor).mapM (fromCbor? (α := α)) = .ok l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fromCbor?_toCbor, ih]; rfl

instance {α : Type u} [ToCbor α] [FromCbor α] [LawfulCbor α] : LawfulCbor (List α) :=
  ⟨fun l => Cbor.mapM_fromCbor?_toCbor l⟩
instance {α : Type u} [ToCbor α] : NonNullCbor (List α) := ⟨fun _ => nofun⟩

instance {α : Type u} [ToCbor α] : ToCbor (Array α) := ⟨fun a => .array (a.toList.map toCbor)⟩
instance {α : Type u} [FromCbor α] : FromCbor (Array α) where
  fromCbor?
    | .array items => List.toArray <$> items.mapM fromCbor?
    | v => .error s!"expected an array, got {repr v}"
instance {α : Type u} [ToCbor α] [FromCbor α] [LawfulCbor α] : LawfulCbor (Array α) :=
  ⟨fun a => by
    show List.toArray <$> (a.toList.map toCbor).mapM fromCbor? = _
    rw [Cbor.mapM_fromCbor?_toCbor]; rfl⟩
instance {α : Type u} [ToCbor α] : NonNullCbor (Array α) := ⟨fun _ => nofun⟩

instance {α : Type u} {β : Type v} [ToCbor α] [ToCbor β] : ToCbor (α × β) where
  toCbor pair := .array [toCbor pair.1, toCbor pair.2]
instance {α : Type u} {β : Type v} [FromCbor α] [FromCbor β] : FromCbor (α × β) where
  fromCbor?
    | .array [a, b] =>
      match fromCbor? a, fromCbor? b with
      | .ok a, .ok b => .ok (a, b)
      | .error e, _ => .error e
      | _, .error e => .error e
    | v => .error s!"expected an array of two elements, got {repr v}"
instance {α : Type u} {β : Type v} [ToCbor α] [FromCbor α] [LawfulCbor α]
    [ToCbor β] [FromCbor β] [LawfulCbor β] : LawfulCbor (α × β) :=
  ⟨fun pair => by simp [toCbor, fromCbor?, fromCbor?_toCbor]⟩
instance {α : Type u} {β : Type v} [ToCbor α] [ToCbor β] : NonNullCbor (α × β) := ⟨fun _ => nofun⟩

/-- Read back only if the property holds. -/
instance {α : Type u} {p : α → Prop} [ToCbor α] : ToCbor {a // p a} := ⟨fun a => toCbor a.val⟩
instance {α : Type u} {p : α → Prop} [DecidablePred p] [FromCbor α] : FromCbor {a // p a} where
  fromCbor? v :=
    match (fromCbor? v : Except String α) with
    | .ok a => if h : p a then .ok ⟨a, h⟩ else .error s!"a value does not have its property: {repr v}"
    | .error e => .error e
instance {α : Type u} {p : α → Prop} [DecidablePred p] [ToCbor α] [FromCbor α] [LawfulCbor α] :
    LawfulCbor {a // p a} :=
  ⟨fun a => by simp [toCbor, fromCbor?, fromCbor?_toCbor a.val, a.property]⟩
instance {α : Type u} {p : α → Prop} [ToCbor α] [NonNullCbor α] : NonNullCbor {a // p a} :=
  ⟨fun a => toCbor_ne_null a.val⟩

end Lanes
