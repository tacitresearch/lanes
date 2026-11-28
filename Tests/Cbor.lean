/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Lib.Encoding.Cbor
import Tests.Oracle.Basic

/-! CBOR (`Lanes/Lib/Encoding/Cbor.lean`): RFC 8949's examples of Appendix A written and read, its
inputs that are not well-formed of Appendix F refused, the strict modes and the limits, random
values read back, a float's width against the machine's own conversions, and what `lanes_data`
derives: the shapes, and that a type's CBOR has the shape of its JSON. -/

namespace Tests.Cbor

open Lanes Lanes.Cbor

def hexOf (s : String) : ByteArray := (Bytes.unhex? s).getD .empty

def uint (n : Nat) : Cbor := .uint n.toUInt64
def text (s : String) : Cbor := .text s
def float (bits : UInt64) : Cbor := .float bits

/-- Appendix A: each value and its preferred serialization, which is also its deterministic
encoding. -/
def appendixA : List (Cbor × String) :=
  [ (uint 0, "00"), (uint 1, "01"), (uint 10, "0a"), (uint 23, "17"), (uint 24, "1818"),
    (uint 25, "1819"), (uint 100, "1864"), (uint 1000, "1903e8"), (uint 1000000, "1a000f4240"),
    (uint 1000000000000, "1b000000e8d4a51000"), (uint 18446744073709551615, "1bffffffffffffffff"),
    (.tag 2 (.bytes (hexOf "010000000000000000")), "c249010000000000000000"),
    (.nint 18446744073709551615, "3bffffffffffffffff"),
    (.tag 3 (.bytes (hexOf "010000000000000000")), "c349010000000000000000"),
    (.nint 0, "20"), (.nint 9, "29"), (.nint 99, "3863"), (.nint 999, "3903e7"),
    (float 0x0, "f90000"), (float 0x8000000000000000, "f98000"),
    (float 0x3ff0000000000000, "f93c00"), (float 0x3ff199999999999a, "fb3ff199999999999a"),
    (float 0x3ff8000000000000, "f93e00"), (float 0x40effc0000000000, "f97bff"),
    (float 0x40f86a0000000000, "fa47c35000"), (float 0x47efffffe0000000, "fa7f7fffff"),
    (float 0x7e37e43c8800759c, "fb7e37e43c8800759c"), (float 0x3e70000000000000, "f90001"),
    (float 0x3f10000000000000, "f90400"), (float 0xc010000000000000, "f9c400"),
    (float 0xc010666666666666, "fbc010666666666666"), (float 0x7ff0000000000000, "f97c00"),
    (float 0x7ff8000000000000, "f97e00"), (float 0xfff0000000000000, "f9fc00"),
    (.bool false, "f4"), (.bool true, "f5"), (.null, "f6"), (.undefined, "f7"),
    (.simple ⟨16, by decide⟩, "f0"), (.simple ⟨255, by decide⟩, "f8ff"),
    (.tag 0 (text "2013-03-21T20:04:00Z"), "c074323031332d30332d32315432303a30343a30305a"),
    (.tag 1 (uint 1363896240), "c11a514b67b0"),
    (.tag 1 (float 0x41d452d9ec200000), "c1fb41d452d9ec200000"),
    (.tag 23 (.bytes (hexOf "01020304")), "d74401020304"),
    (.tag 24 (.bytes (hexOf "6449455446")), "d818456449455446"),
    (.tag 32 (text "http://www.example.com"),
      "d82076687474703a2f2f7777772e6578616d706c652e636f6d"),
    (.bytes .empty, "40"), (.bytes (hexOf "01020304"), "4401020304"), (text "", "60"),
    (text "a", "6161"), (text "IETF", "6449455446"), (text "\"\\", "62225c"),
    (text "ü", "62c3bc"), (text "水", "63e6b0b4"), (text "𐅑", "64f0908591"),
    (.array [], "80"), (.array [uint 1, uint 2, uint 3], "83010203"),
    (.array [uint 1, .array [uint 2, uint 3], .array [uint 4, uint 5]], "8301820203820405"),
    (.array ((List.range 25).map (uint ·.succ)),
      "98190102030405060708090a0b0c0d0e0f101112131415161718181819"),
    (.map [], "a0"), (.map [(uint 1, uint 2), (uint 3, uint 4)], "a201020304"),
    (.map [(text "a", uint 1), (text "b", .array [uint 2, uint 3])], "a26161016162820203"),
    (.array [text "a", .map [(text "b", text "c")]], "826161a161626163"),
    (.map [(text "a", text "A"), (text "b", text "B"), (text "c", text "C"), (text "d", text "D"),
      (text "e", text "E")], "a56161614161626142616361436164614461656145") ]

/-- Appendix A's encodings that are well-formed but not preferred: floats wider than they need,
and indefinite lengths. -/
def appendixALoose : List (String × Cbor) :=
  [ ("fa7f800000", float 0x7ff0000000000000), ("fa7fc00000", float 0x7ff8000000000000),
    ("faff800000", float 0xfff0000000000000), ("fb7ff0000000000000", float 0x7ff0000000000000),
    ("fb7ff8000000000000", float 0x7ff8000000000000),
    ("fbfff0000000000000", float 0xfff0000000000000),
    ("5f42010243030405ff", .bytes (hexOf "0102030405")),
    ("7f657374726561646d696e67ff", text "streaming"), ("9fff", .array []),
    ("9f018202039f0405ffff", .array [uint 1, .array [uint 2, uint 3], .array [uint 4, uint 5]]),
    ("9f01820203820405ff", .array [uint 1, .array [uint 2, uint 3], .array [uint 4, uint 5]]),
    ("83018202039f0405ff", .array [uint 1, .array [uint 2, uint 3], .array [uint 4, uint 5]]),
    ("83019f0203ff820405", .array [uint 1, .array [uint 2, uint 3], .array [uint 4, uint 5]]),
    ("9f0102030405060708090a0b0c0d0e0f101112131415161718181819ff",
      .array ((List.range 25).map (uint ·.succ))),
    ("bf61610161629f0203ffff", .map [(text "a", uint 1), (text "b", .array [uint 2, uint 3])]),
    ("826161bf61626163ff", .array [text "a", .map [(text "b", text "c")]]),
    ("bf6346756ef563416d7421ff", .map [(text "Fun", .bool true), (text "Amt", .nint 1)]) ]

/-- Appendix F: inputs that are not well-formed. -/
def appendixF : List String :=
  [ "18", "19", "1a", "1b", "1901", "1a0102", "1b01020304050607", "38", "58", "78", "98",
    "9a01ff00", "b8", "d8", "f8", "f900", "fa0000", "fb000000",
    "41", "61", "5affffffff00", "5bffffffffffffffff010203", "7affffffff00",
    "7b7fffffffffffffff010203",
    "81", "818181818181818181", "8200", "a1", "a20102", "a100", "a2000000", "c0",
    "5f4100", "7f6100", "9f", "9f0102", "bf", "bf01020102", "819f", "9f8000",
    "9f9f9f9f9fffffffff", "9f819f819f9fffffff",
    "1c", "1d", "1e", "3c", "3d", "3e", "5c", "5d", "5e", "7c", "7d", "7e", "9c", "9d", "9e",
    "bc", "bd", "be", "dc", "dd", "de", "fc", "fd", "fe",
    "f800", "f801", "f818", "f81f",
    "5f00ff", "5f21ff", "5f6100ff", "5f80ff", "5fa0ff", "5fc000ff", "5fe0ff", "7f4100ff",
    "5f5f4100ffff", "7f7f6100ffff",
    "ff", "81ff", "8200ff", "a1ff", "a1ff00", "a100ff", "a20000ff", "9f81ff", "9f829f819f9fffffffff",
    "bf00ff", "bf000000ff",
    "1f", "3f", "df" ]

instance : BEq (Except Error Cbor) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

def decodes (cfg : Config) (hex : String) : Except Error Cbor := decode cfg (hexOf hex)

def strictPreferred : Config := { accept := .preferred }
def strictDeterministic : Config := { accept := .deterministic }

def appendixTests : List (String × Bool) :=
  [ ("cbor: RFC 8949 Appendix A, each value written as the RFC writes it",
      appendixA.all fun (v, hex) => Bytes.hex (encode v) == hex && Bytes.hex (encodeDeterministic v) == hex),
    ("cbor: RFC 8949 Appendix A, each encoding read back, by every mode of the decoder",
      appendixA.all fun (v, hex) =>
        [{}, strictPreferred, strictDeterministic].all fun cfg => decodes cfg hex == .ok v),
    ("cbor: Appendix A's wider floats and indefinite lengths read, and refused by the strict modes",
      appendixALoose.all fun (hex, v) =>
        decodes {} hex == .ok v && decodes strictPreferred hex == .error .notPreferred
          && decodes strictDeterministic hex == .error .notDeterministic),
    ("cbor: RFC 8949 Appendix F, every input that is not well-formed refused",
      appendixF.all fun hex => (decodes {} hex).toOption.isNone),
    ("cbor: what is refused is refused for its reason",
      decodes {} "1c" == .error .reserved && decodes {} "19" == .error .truncated
        && decodes {} "1f" == .error .indefinite && decodes {} "ff" == .error .unexpectedBreak
        && decodes {} "f818" == .error .badSimple && decodes {} "5f00ff" == .error .badChunk
        && decodes {} "62c328" == .error .invalidUtf8 && decodes {} "0000" == .error .trailing
        && decodes {} "7f61ff61ffff" == .error .invalidUtf8) ]

def strictTests : List (String × Bool) :=
  [ ("cbor: an argument longer than it needs is read, and refused by the strict modes",
      decodes {} "1800" == .ok (uint 0) && decodes {} "1b0000000000000001" == .ok (uint 1)
        && decodes strictPreferred "1800" == .error .notPreferred
        && decodes strictDeterministic "1b0000000000000001" == .error .notDeterministic),
    ("cbor: a map out of order is preferred but not deterministic; sorted, it is both",
      decodes strictPreferred "a2616201616102"
          == .ok (.map [(text "b", uint 1), (text "a", uint 2)])
        && decodes strictDeterministic "a2616201616102" == .error .notDeterministic
        && decodes strictDeterministic "a2616102616201"
          == .ok (.map [(text "a", uint 2), (text "b", uint 1)])),
    ("cbor: the deterministic order is bytewise, not shortest first",
      Bytes.hex (encodeDeterministic
          (.map [(text "", uint 3), (uint 100, uint 2), (.bytes (hexOf "000000"), uint 1)]))
        == "a318640243000000016003") ]

def nested : Nat → Cbor
  | 0 => uint 0
  | n + 1 => .array [nested n]

def limitTests : List (String × Bool) :=
  [ ("cbor: the depth: as deep as the limit is read, one level more is refused",
      decode { maxDepth := 4 } (encode (nested 3)) == .ok (nested 3)
        && decode { maxDepth := 4 } (encode (nested 4)) == .error .tooDeep
        && decode {} (encode (nested 64)) == .error .tooDeep
        && decode { maxDepth := 3 } (hexOf "c1c1c100") == .error .tooDeep),
    ("cbor: the length of a string, an array and a map, definite or not",
      decode { maxLength := 3 } (encode (text "abc")) == .ok (text "abc")
        && decode { maxLength := 3 } (encode (text "abcd")) == .error .tooLong
        && decode { maxLength := 2 } (hexOf "83010203") == .error .tooLong
        && decode { maxLength := 2 } (hexOf "9f010203ff") == .error .tooLong
        && decode { maxLength := 1 } (hexOf "a201020304") == .error .tooLong
        && decode { maxLength := 3 } (hexOf "5f42010243030405ff") == .error .tooLong
        && decode { maxLength := 2 } (hexOf "5affffffff00") == .error .tooLong),
    ("cbor: the size of the input",
      decode { maxSize := 2 } (hexOf "1903e8") == .error .tooLarge
        && decode { maxSize := 3 } (hexOf "1903e8") == .ok (uint 1000)) ]

/-! ### Random values -/


def genUInt : Oracle.Gen UInt64 := do
  match ← Oracle.Gen.below 4 with
  | 0 => return (← Oracle.Gen.pick [0, 1, 23, 24, 255, 256, 65535, 65536, 4294967295, 4294967296,
      18446744073709551615]).toUInt64
  | 1 => return (← Oracle.Gen.below 300).toUInt64
  | 2 => return (← Oracle.Gen.below 70000).toUInt64
  | _ => return (← Oracle.Gen.below (2 ^ 64)).toUInt64

def genFloat : Oracle.Gen UInt64 := do
  match ← Oracle.Gen.below 4 with
  | 0 => return ofHalf (← Oracle.Gen.below 65536).toUInt16
  | 1 => return ofSingle (← Oracle.Gen.below (2 ^ 32)).toUInt32
  | 2 => return (← Oracle.Gen.pick [0, 0x8000000000000000, 0x7ff0000000000000, 0x7ff8000000000000,
      0x7ff0000000000001, 0x3e70000000000000, 0x36a0000000000000]).toUInt64
  | _ => return (← Oracle.Gen.below (2 ^ 64)).toUInt64

def genSimple : Oracle.Gen Cbor := do
  let v ← Oracle.Gen.pick ((List.range 20) ++ [32, 100, 255])
  if h : v.toUInt8 < 20 ∨ 32 ≤ v.toUInt8 then return .simple ⟨v.toUInt8, h⟩ else return .null

def genScalar : Oracle.Gen Cbor := do
  match ← Oracle.Gen.below 8 with
  | 0 => return .uint (← genUInt)
  | 1 => return .nint (← genUInt)
  | 2 => return .float (← genFloat)
  | 3 => return .bool (← Oracle.Gen.chance 50)
  | 4 => return (← Oracle.Gen.pick [.null, .undefined])
  | 5 => genSimple
  | 6 => return .bytes (← Oracle.Gen.bytes 30)
  | _ => return .text (← Oracle.Gen.text ['a', 'Z', '0', ' ', '"', 'é', '水', '😀', '\x00'] 30)

def genCbor : Nat → Oracle.Gen Cbor
  | 0 => genScalar
  | d + 1 => do
    match ← Oracle.Gen.below 8 with
    | 0 => return .array (← Oracle.Gen.list (← Oracle.Gen.below 5) (genCbor d))
    | 1 => do
      let n ← Oracle.Gen.below 4
      return .map (← Oracle.Gen.list n do return (← genCbor d, ← genCbor d))
    | 2 => return .tag (← genUInt) (← genCbor d)
    | 3 => return .array (← Oracle.Gen.list (← Oracle.Gen.below 30) genScalar)
    | _ => genScalar

/-- Another encoding of the same value: some arguments wider than they need, some lengths
indefinite, some strings in chunks; `fuel` levels deep, below them the preferred one. -/
def loose : (fuel : Nat) → Cbor → Oracle.Gen ByteArray
  | 0, v => return encode v
  | fuel + 1, v => do
  let head (major n : Nat) : Oracle.Gen ByteArray := do
    let widths := [(24, 1), (25, 2), (26, 4), (27, 8)].filter fun (_, w) => n < 256 ^ w
    if (← Oracle.Gen.chance 50) || widths.isEmpty then return (head major n).toByteArray
    else
      let (info, _) ← Oracle.Gen.pick widths
      return (longHead major info n).toByteArray
  let items (major : Nat) (count : Nat) (body : ByteArray) : Oracle.Gen ByteArray := do
    if ← Oracle.Gen.chance 30 then return [(major * 32 + 31).toUInt8].toByteArray ++ body ++ [0xff].toByteArray
    else return (← head major count) ++ body
  match v with
  | .uint n => head 0 n.toNat
  | .nint n => head 1 n.toNat
  | .bytes b =>
    if ← Oracle.Gen.chance 30 then
      let cut ← Oracle.Gen.below (b.size + 1)
      let a := b.extract 0 cut
      let c := b.extract cut b.size
      return [0x5f].toByteArray ++ (← head 2 a.size) ++ a ++ (← head 2 c.size) ++ c ++ [0xff].toByteArray
    else return (← head 2 b.size) ++ b
  | .text s => return (← head 3 s.utf8ByteSize) ++ s.toUTF8
  | .array xs => do
    let body ← xs.foldlM (fun acc x => return acc ++ (← loose fuel x)) .empty
    items 4 xs.length body
  | .map es => do
    let body ← es.foldlM (fun acc e => return acc ++ (← loose fuel e.1) ++ (← loose fuel e.2))
      .empty
    items 5 es.length body
  | .tag t x => return (← head 6 t.toNat) ++ (← loose fuel x)
  | .float bits =>
    match ← Oracle.Gen.below 3 with
    | 0 => return (longHead 7 27 bits.toNat).toByteArray
    | _ => return encode v
  | _ => return encode v

/-- `v` with each map's entries reversed, `fuel` levels deep: equal in the data model. -/
def reorder : (fuel : Nat) → Cbor → Cbor
  | fuel + 1, .array xs => .array (xs.map (reorder fuel))
  | fuel + 1, .map es => .map (es.reverse.map fun e => (reorder fuel e.1, reorder fuel e.2))
  | fuel + 1, .tag t x => .tag t (reorder fuel x)
  | _, v => v

def randomValues (count seed : Nat) : List Cbor := Oracle.Gen.run seed (Oracle.Gen.list count (genCbor 4))

def randomTests : List (String × Bool) :=
  let values := randomValues 3000 2026
  let looseBytes := Oracle.Gen.run 7 (values.mapM (loose 10))
  [ ("cbor: random values read back from their preferred serialization, by every mode",
      values.all fun v => decode {} (encode v) == .ok v && decode strictPreferred (encode v) == .ok v),
    ("cbor: random values read back from their deterministic encoding, in deterministic order",
      values.all fun v =>
        decode strictDeterministic (encodeDeterministic v) == .ok (canonical v)
          && decode {} (encodeDeterministic v) == .ok (canonical v)),
    ("cbor: a value with its maps reordered has the same deterministic encoding",
      values.all fun v => encodeDeterministic (reorder 10 v) == encodeDeterministic v),
    ("cbor: other encodings of random values read, and are refused when not preferred",
      (values.zip looseBytes).all fun (v, b) =>
        decode {} b == .ok v
          && (decode strictPreferred b == .ok v) == (b == encode v)),
    ("cbor: cut short anywhere, an encoding is refused",
      (values.take 300).all fun v =>
        let b := encode v
        (List.range b.size).all fun n => (decode {} (b.extract 0 n)).toOption.isNone) ]

/-! ### Floats -/

/-- The binary64 a binary16 holds, by arithmetic on `Float`, which is exact for these. -/
def halfReference (h : Nat) : Float :=
  let sign : Float := if h / 2 ^ 15 = 1 then -1 else 1
  let exponent : Nat := h / 2 ^ 10 % 32
  let fraction := (h % 1024).toFloat
  if exponent = 0 then sign * Float.scaleB fraction (-24)
  else if exponent = 31 then (if h % 1024 = 0 then sign / 0 else 0 / 0)
  else sign * Float.scaleB (1024 + fraction) (Int.ofNat exponent - 25)

def isNan (bits : UInt64) : Bool :=
  bits.toNat / 2 ^ 52 % 2048 = 2047 && bits.toNat % 2 ^ 52 ≠ 0

def floatTests : List (String × Bool) :=
  let singles := Oracle.Gen.run 11 (Oracle.Gen.list 20000 (Oracle.Gen.below (2 ^ 32)))
  [ ("cbor: every binary16 widens as the arithmetic says, and is written in two bytes",
      (List.range 65536).all fun h =>
        let bits := ofHalf h.toUInt16
        (isNan bits || bits == (halfReference h).toBits)
          && toHalf? bits == some h.toUInt16 && (encode (.float bits)).size == 3),
    ("cbor: random binary32 widen as the machine widens them, in the fewest bytes",
      singles.all fun s =>
        let bits := ofSingle s.toUInt32
        (isNan bits || bits == (Float32.ofBits s.toUInt32).toFloat.toBits)
          && toSingle? bits == some s.toUInt32
          && (encode (.float bits)).size == (if (toHalf? bits).isSome then 3 else 5)) ]

/-! ### Typed values, and what `lanes_data` derives -/

lanes_data structure Point where
  x : Int
  y : Int
  label : Option String
  deriving DecidableEq, ToJson, FromJson, ToCbor, FromCbor

lanes_data inductive Shape where
  | dot
  | circle (centre : Point) (radius : Nat)
  | path (points : List Point) (closed : Bool)
  deriving DecidableEq, ToJson, FromJson, ToCbor, FromCbor

lanes_data inductive Slot (A : Type) where
  | empty
  | held (owner : A) (count : Fin 2)
  deriving DecidableEq, ToCbor, FromCbor

lanes_data structure Maybe (A : Type) where
  value : Option A
  deriving DecidableEq, ToCbor, FromCbor

lanes_data structure Blob where
  name : String
  body : ByteArray
  size : UInt32
  offset : Int64
  deriving DecidableEq, ToCbor, FromCbor

/--
error: lanes_data: `ToCbor` and `FromCbor` are derived together, with the law that one reads back
what the other writes
-/
#guard_msgs (whitespace := lax) in
lanes_data structure Half where
  n : Nat
  deriving FromCbor

example (s : Shape) : fromCbor? (toCbor s) = .ok s := fromCbor?_toCbor s
example (m : Maybe (Slot Nat)) : fromCbor? (toCbor m) = .ok m := fromCbor?_toCbor m

def roundTrips {α : Type} [ToCbor α] [FromCbor α] [DecidableEq α] (a : α) : Bool :=
  match (decode {} (encode (toCbor a))).toOption.map fromCbor? with
  | some (.ok b) => decide (b = a)
  | _ => false

/-- JSON as CBOR, structurally: a number an integer, an object a map. -/
def ofJson : (fuel : Nat) → Json → Cbor
  | 0, _ => .undefined
  | _ + 1, .null => .null
  | _ + 1, .bool b => .bool b
  | _ + 1, .num n => if n.exponent = 0 then (if 0 ≤ n.mantissa then uint n.mantissa.toNat
      else .nint (-1 - n.mantissa).toNat.toUInt64) else .null
  | _ + 1, .str s => .text s
  | fuel + 1, .arr xs => .array (xs.toList.map (ofJson fuel))
  | fuel + 1, .obj fs => .map (fs.toList.map fun (k, v) => (.text k, ofJson fuel v))

/-- The CBOR of a value and its JSON agree, but for the order of a map's entries. -/
def agrees {α : Type} [ToCbor α] [ToJson α] (a : α) : Bool :=
  encodeDeterministic (toCbor a) == encodeDeterministic (ofJson 10 (toJson a))

def shapes : List Shape :=
  [ .dot, .circle ⟨-3, 4, some "a/b é"⟩ 7, .path [] true,
    .path [⟨0, 0, none⟩, ⟨1, -1, some ""⟩, ⟨-2000000, 5, some "x"⟩] false ]

def typedTests : List (String × Bool) :=
  [ ("cbor: a structure is a map of its fields in their order, a null field left out",
      Bytes.hex (encode (toCbor (Point.mk 1 (-2) none))) == "a2617801617921"
        && toCbor (Point.mk 1 2 (some "a"))
          == .map [(text "x", uint 1), (text "y", uint 2), (text "label", text "a")]),
    ("cbor: a constructor is its name, or a map of its name holding its arguments",
      toCbor Shape.dot == text "dot"
        && toCbor (Shape.path [] true)
          == .map [(text "path", .map [(text "points", .array []), (text "closed", .bool true)])]),
    ("cbor: a type's CBOR has the shape of its JSON",
      shapes.all agrees && agrees (Point.mk 5 6 none)),
    ("cbor: derived types read back through bytes, parameters included",
      shapes.all roundTrips && roundTrips (Slot.held "ab" 1) && roundTrips (Slot.empty : Slot Nat)
        && roundTrips (Maybe.mk (some (Slot.empty : Slot Nat)))
        && roundTrips (Blob.mk "f" (hexOf "00ff") 7 (-9223372036854775808))),
    ("cbor: a natural number or an integer past 64 bits is a bignum, as Appendix A writes it",
      Bytes.hex (encode (toCbor (2 ^ 64 : Nat))) == "c249010000000000000000"
        && Bytes.hex (encode (toCbor (-(2 ^ 64) - 1 : Int))) == "c349010000000000000000"
        && Bytes.hex (encode (toCbor (-(2 ^ 64) : Int))) == "3bffffffffffffffff"
        && [0, 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 200 + 5].all (fun n : Nat => roundTrips n)
        && [0, -1, -(2 ^ 64), -(2 ^ 64) - 1, 2 ^ 70, -(2 ^ 99)].all (fun i : Int => roundTrips i)),
    ("cbor: fixed-width numbers, bytes, options, lists, arrays and pairs read back",
      roundTrips (255 : UInt8) && roundTrips (65535 : UInt16) && roundTrips (7 : UInt32)
        && roundTrips (18446744073709551615 : UInt64) && roundTrips (-1 : Int64)
        && roundTrips (hexOf "deadbeef") && roundTrips (some (3 : Nat)) && roundTrips (none : Option Nat)
        && roundTrips [(1 : Nat), 2] && roundTrips #["a", "b"] && roundTrips ((1 : Nat), "x")
        && roundTrips () && roundTrips (⟨1, by decide⟩ : Fin 3)),
    ("cbor: a value out of its type's range, or of another shape, is refused",
      (fromCbor? (uint 256) : Except String UInt8).toOption.isNone
        && (fromCbor? (uint 9223372036854775808) : Except String Int64).toOption.isNone
        && (fromCbor? (uint 3) : Except String (Fin 3)).toOption.isNone
        && (fromCbor? (.nint 0) : Except String Nat).toOption.isNone
        && (fromCbor? (text "square") : Except String Shape).toOption.isNone
        && (fromCbor? (.map [(text "x", uint 1)]) : Except String Point).toOption.isNone) ]

def tests : List (String × Bool) :=
  appendixTests ++ strictTests ++ limitTests ++ randomTests ++ floatTests ++ typedTests

end Tests.Cbor
