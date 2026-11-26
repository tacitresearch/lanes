/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Ported from Lean 4 core (`Lean.Data.Json.Basic`), Copyright (c) 2019 Gabriel Ebner, Microsoft
Corporation and Lean FRO, Apache 2.0.
Authors: Gabriel Ebner, Marc Huisinga
-/
module

/-!
# JSON values

`Json` is the type of JSON documents (RFC 8259), and `JsonNumber` the exact decimal numbers they
hold. It is defined here, not taken from `Lean.Data.Json`, because runtime modules import only
`Std`: any `import Lean` takes a compiled binary from about 5 MB to about 137 MB.

Values are kept canonical, so that `=` is the equality of JSON documents, and it is decidable:

- a `JsonNumber` carries a proof that it has no trailing zero after the decimal point, so `1.50`
  and `1.5` are the same value;
- the fields of an object built by `Json.mkObj` or by the parser are sorted by key and have
  distinct keys, so two objects with the same fields are equal whatever order they were given in.

Objects are sorted arrays, not the `Std.TreeMap.Raw` of the original: two trees with the same
entries can differ in shape, so a tree map gives neither `DecidableEq` nor a hash that agrees with
equality without a proof about its internals.

## Main definitions

- `JsonNumber`: a decimal number `mantissa * 10 ^ -exponent` in lowest terms.
- `Json`: a JSON value.
- `Json.mkObj`: build an object from a list of fields.
- `Json.getObjVal?`, `Json.getArr?`, `Json.getStr?`, `Json.getNat?` and the other accessors, which
  return `Except String`.
-/

@[expose] public section

namespace Lanes

/--
A decimal number `mantissa * 10 ^ -exponent` in lowest terms. Integers have exponent 0, so they
are stored in full; a fraction has no trailing zero.
-/
structure JsonNumber where
  /-- The digits of the number as an integer, with its sign. -/
  mantissa : Int
  /-- The number of those digits that come after the decimal point. -/
  exponent : Nat
  /-- The last digit after the decimal point is not zero, so each number has one representation. -/
  normal : exponent = 0 ∨ mantissa % 10 ≠ 0
  deriving DecidableEq

namespace JsonNumber

/-- The number `mantissa * 10 ^ -exponent`, with trailing zeros after the decimal point removed. -/
def ofDecimal : (mantissa : Int) → (exponent : Nat) → JsonNumber
  | m, 0 => ⟨m, 0, .inl rfl⟩
  | m, e + 1 => if h : m % 10 = 0 then ofDecimal (m / 10) e else ⟨m, e + 1, .inr h⟩

/-- An integer as a JSON number. -/
protected def fromInt (n : Int) : JsonNumber := ⟨n, 0, .inl rfl⟩

/-- A natural number as a JSON number. -/
protected def fromNat (n : Nat) : JsonNumber := .fromInt n

/-- The number `mantissa * 10 ^ exponent`, for an exponent of either sign. -/
def ofScientific (mantissa : Int) (exponent : Int) : JsonNumber :=
  if exponent < 0 then ofDecimal mantissa exponent.natAbs
  else .fromInt (mantissa * 10 ^ exponent.toNat)

instance : Coe Nat JsonNumber := ⟨JsonNumber.fromNat⟩
instance : Coe Int JsonNumber := ⟨JsonNumber.fromInt⟩
instance {n : Nat} : OfNat JsonNumber n := ⟨JsonNumber.fromNat n⟩
instance : Inhabited JsonNumber := ⟨0⟩

instance : OfScientific JsonNumber where
  ofScientific mantissa exponentSign decimalExponent :=
    ofScientific mantissa (if exponentSign then -(decimalExponent : Int) else decimalExponent)

instance : Neg JsonNumber where
  neg n := ⟨-n.mantissa, n.exponent, n.normal.imp id (by omega)⟩

instance : Hashable JsonNumber where
  hash n := mixHash (hash n.mantissa) (hash n.exponent)

/-- The value as an integer, if it has no fractional part. -/
def toInt? (n : JsonNumber) : Option Int :=
  if n.exponent = 0 then some n.mantissa else none

/-- The value as a natural number, if it is a non-negative integer. -/
def toNat? (n : JsonNumber) : Option Nat :=
  if n.exponent = 0 ∧ 0 ≤ n.mantissa then some n.mantissa.toNat else none

/--
The most zeros `toString` writes between the decimal point and the first significant digit. A
smaller number is written in scientific notation, so the length of the text stays proportional to
the number of significant digits.
-/
def maxLeadingZeros : Nat := 9

/--
The JSON text of a number. Integers are written in full. A fraction is written with a decimal
point, or in scientific notation (`1.5e-20`) when it starts with more than `maxLeadingZeros`
zeros.
-/
protected def toString (n : JsonNumber) : String :=
  if n.exponent = 0 then toString n.mantissa
  else
    let sign := if n.mantissa < 0 then "-" else ""
    let digits := Nat.toDigits 10 n.mantissa.natAbs
    if n.exponent < digits.length then
      let whole := digits.length - n.exponent
      sign ++ String.ofList (digits.take whole ++ '.' :: digits.drop whole)
    else if n.exponent - digits.length ≤ maxLeadingZeros then
      let zeros := List.replicate (n.exponent - digits.length) '0'
      sign ++ String.ofList ('0' :: '.' :: zeros ++ digits)
    else
      let fraction := if digits.length = 1 then [] else '.' :: digits.drop 1
      let power : Int := (digits.length : Int) - 1 - n.exponent
      sign ++ String.ofList (digits.take 1 ++ fraction) ++ "e" ++ toString power

instance : ToString JsonNumber := ⟨JsonNumber.toString⟩

instance : Repr JsonNumber where
  reprPrec n prec := Repr.addAppParen ("Lanes.JsonNumber.ofDecimal " ++
    reprArg n.mantissa ++ " " ++ reprArg n.exponent) prec

@[simp] theorem toInt?_fromInt (n : Int) : (JsonNumber.fromInt n).toInt? = some n := rfl

@[simp] theorem toNat?_fromNat (n : Nat) : (JsonNumber.fromNat n).toNat? = some n := by
  simp [toNat?, JsonNumber.fromNat, JsonNumber.fromInt]

end JsonNumber

/--
A JSON value.

The fields of an object are kept sorted by key, with no key twice: `Json.mkObj` and the parser
build them that way, and equality of objects relies on it. A hand-built `Json.obj` whose fields
are in another order still prints and is still looked up correctly, but is not equal to the
sorted object with the same fields.
-/
inductive Json where
  /-- The value `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- A number. -/
  | num (n : JsonNumber)
  /-- A string. -/
  | str (s : String)
  /-- An array. -/
  | arr (elems : Array Json)
  /-- An object: its fields, sorted by key. Build one with `Json.mkObj`. -/
  | obj (fields : Array (String × Json))
  deriving Inhabited

namespace Json

/-!
### Equality, hashing and display

The deriving handlers do not cover a type that is nested through `Array` (`DecidableEq`) or
generate opaque `partial` definitions for it (`BEq`, `Hashable`, `Repr`), so the instances are
written out as total functions.
-/

mutual

/-- Decide whether two JSON values are equal. -/
protected def decEq : (a b : Json) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Json.bool.inj e)
  | .num a, .num b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Json.num.inj e)
  | .str a, .str b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Json.str.inj e)
  | .arr a, .arr b =>
    match Json.decEqArray a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Json.arr.inj e)
  | .obj a, .obj b =>
    match Json.decEqFields a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Json.obj.inj e)
  | .null, .bool _ | .null, .num _ | .null, .str _ | .null, .arr _ | .null, .obj _
  | .bool _, .null | .bool _, .num _ | .bool _, .str _ | .bool _, .arr _ | .bool _, .obj _
  | .num _, .null | .num _, .bool _ | .num _, .str _ | .num _, .arr _ | .num _, .obj _
  | .str _, .null | .str _, .bool _ | .str _, .num _ | .str _, .arr _ | .str _, .obj _
  | .arr _, .null | .arr _, .bool _ | .arr _, .num _ | .arr _, .str _ | .arr _, .obj _
  | .obj _, .null | .obj _, .bool _ | .obj _, .num _ | .obj _, .str _ | .obj _, .arr _ =>
    isFalse nofun
termination_by structural a => a

/-- Decide whether two arrays of JSON values are equal. -/
protected def decEqArray : (a b : Array Json) → Decidable (a = b)
  | ⟨a⟩, ⟨b⟩ =>
    match Json.decEqList a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Array.mk.inj e)
termination_by structural a => a

/-- Decide whether two lists of JSON values are equal. -/
protected def decEqList : (a b : List Json) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Json.decEq a b, Json.decEqList as bs with
    | isTrue h, isTrue hs => isTrue (h ▸ hs ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
    | _, isFalse h => isFalse fun e => h (List.cons.inj e).2
  | [], _ :: _ | _ :: _, [] => isFalse nofun
termination_by structural a => a

/-- Decide whether two arrays of object fields are equal. -/
protected def decEqFields : (a b : Array (String × Json)) → Decidable (a = b)
  | ⟨a⟩, ⟨b⟩ =>
    match Json.decEqFieldList a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Array.mk.inj e)
termination_by structural a => a

/-- Decide whether two lists of object fields are equal. -/
protected def decEqFieldList : (a b : List (String × Json)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Json.decEqField a b, Json.decEqFieldList as bs with
    | isTrue h, isTrue hs => isTrue (h ▸ hs ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
    | _, isFalse h => isFalse fun e => h (List.cons.inj e).2
  | [], _ :: _ | _ :: _, [] => isFalse nofun
termination_by structural a => a

/-- Decide whether two object fields are equal. -/
protected def decEqField : (a b : String × Json) → Decidable (a = b)
  | (ka, va), (kb, vb) =>
    if hk : ka = kb then
      match Json.decEq va vb with
      | isTrue h => isTrue (hk ▸ h ▸ rfl)
      | isFalse h => isFalse fun e => h (Prod.mk.inj e).2
    else isFalse fun e => hk (Prod.mk.inj e).1
termination_by structural a => a

end

instance : DecidableEq Json := Json.decEq

/-- The value of a field is smaller than the object that holds it. -/
theorem sizeOf_field_lt {fields : Array (String × Json)} {field : String × Json}
    (h : field ∈ fields) : sizeOf field.2 < sizeOf fields := by
  have := Array.sizeOf_lt_of_mem h
  obtain ⟨key, value⟩ := field
  simp only [Prod.mk.sizeOf_spec] at this
  show sizeOf value < _
  omega

/-- A hash of a JSON value. -/
protected def hash : Json → UInt64
  | .null => 11
  | .bool b => mixHash 13 (hash b)
  | .num n => mixHash 17 (hash n)
  | .str s => mixHash 19 (hash s)
  | .arr elems => mixHash 23 (elems.foldl (fun r elem => mixHash r elem.hash) 7)
  | .obj fields =>
    mixHash 29 (fields.foldl (fun r field => mixHash r (mixHash (hash field.1) field.2.hash)) 7)
decreasing_by
  · decreasing_tactic
  · have := sizeOf_field_lt ‹_›
    simp only [obj.sizeOf_spec]
    omega

instance : Hashable Json := ⟨Json.hash⟩

/-- A JSON value as the Lean term that builds it. -/
protected def reprPrec : Json → Nat → Std.Format
  | .null, _ => "Lanes.Json.null"
  | .bool b, prec => Repr.addAppParen ("Lanes.Json.bool " ++ reprArg b) prec
  | .num n, prec => Repr.addAppParen ("Lanes.Json.num " ++ reprArg n) prec
  | .str s, prec => Repr.addAppParen ("Lanes.Json.str " ++ reprArg s) prec
  | .arr elems, prec =>
    let items := elems.toList.map fun elem => elem.reprPrec 0
    Repr.addAppParen
      ("Lanes.Json.arr " ++ Std.Format.bracket "#[" (Std.Format.joinSep items ("," ++ .line)) "]")
      prec
  | .obj fields, prec =>
    let items := fields.toList.map fun field =>
      Std.Format.paren (repr field.1 ++ "," ++ .line ++ field.2.reprPrec 0)
    Repr.addAppParen
      ("Lanes.Json.obj " ++ Std.Format.bracket "#[" (Std.Format.joinSep items ("," ++ .line)) "]")
      prec
termination_by j => j
decreasing_by
  · have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹_›)
    simp only [arr.sizeOf_spec]
    omega
  · have := sizeOf_field_lt (Array.mem_toList_iff.mp ‹_›)
    simp only [obj.sizeOf_spec]
    omega

instance : Repr Json := ⟨Json.reprPrec⟩

/-! ### Building values -/

instance : Coe Nat Json := ⟨fun n => .num n⟩
instance : Coe Int Json := ⟨fun n => .num n⟩
instance : Coe String Json := ⟨.str⟩
instance : Coe Bool Json := ⟨.bool⟩
instance {n : Nat} : OfNat Json n := ⟨.num (.fromNat n)⟩

/-- Sort fields by key. Fields with the same key keep their relative order. -/
def sortFields (fields : List (String × Json)) : List (String × Json) :=
  fields.mergeSort fun a b => a.1 ≤ b.1

/-- Of each run of neighbouring fields with the same key, keep the last. -/
def dedupFields : List (String × Json) → List (String × Json)
  | a :: b :: rest => if a.1 = b.1 then dedupFields (b :: rest) else a :: dedupFields (b :: rest)
  | fields => fields

/-- The first key that two neighbouring fields share. -/
def duplicateKey? : List (String × Json) → Option String
  | a :: b :: rest => if a.1 = b.1 then some a.1 else duplicateKey? (b :: rest)
  | _ => none

/-- An object with the given fields. If a key is given twice, its last value wins. -/
def mkObj (fields : List (String × Json)) : Json :=
  .obj (dedupFields (sortFields fields)).toArray

/-- An object with the given fields, or the error naming a key that is given twice. -/
def mkObj? (fields : List (String × Json)) : Except String Json :=
  let sorted := sortFields fields
  match duplicateKey? sorted with
  | some key => .error s!"duplicate object key {key.quote}"
  | none => .ok (.obj sorted.toArray)

/-! ### Reading values -/

/-- Whether the value is `null`. -/
def isNull : Json → Bool
  | .null => true
  | _ => false

/-- The fields of an object. -/
def getObj? : Json → Except String (Array (String × Json))
  | .obj fields => .ok fields
  | _ => .error "object expected"

/-- The elements of an array. -/
def getArr? : Json → Except String (Array Json)
  | .arr elems => .ok elems
  | _ => .error "array expected"

/-- The contents of a string. -/
def getStr? : Json → Except String String
  | .str s => .ok s
  | _ => .error "string expected"

/-- The value of a number. -/
def getNum? : Json → Except String JsonNumber
  | .num n => .ok n
  | _ => .error "number expected"

/-- The value of a number that is a natural number. -/
def getNat? : Json → Except String Nat
  | .num n =>
    match n.toNat? with
    | some n => .ok n
    | none => .error "natural number expected"
  | _ => .error "natural number expected"

/-- The value of a number that is an integer. -/
def getInt? : Json → Except String Int
  | .num n =>
    match n.toInt? with
    | some n => .ok n
    | none => .error "integer expected"
  | _ => .error "integer expected"

/-- The value of a Boolean. -/
def getBool? : Json → Except String Bool
  | .bool b => .ok b
  | _ => .error "Boolean expected"

/-- The value of the field `key` of an object. -/
def getObjVal? : Json → String → Except String Json
  | .obj fields, key =>
    match fields.find? (·.1 == key) with
    | some field => .ok field.2
    | none => .error s!"property not found: {key}"
  | _, _ => .error "object expected"

/-- The element at index `i` of an array. -/
def getArrVal? : Json → Nat → Except String Json
  | .arr elems, i =>
    match elems[i]? with
    | some elem => .ok elem
    | none => .error s!"index out of bounds: {i}"
  | _, _ => .error "array expected"

/-- The value of the field `key` of an object, or `null` if there is no such field. -/
def getObjValD (j : Json) (key : String) : Json :=
  match j.getObjVal? key with
  | .ok value => value
  | .error _ => .null

end Json

end Lanes
