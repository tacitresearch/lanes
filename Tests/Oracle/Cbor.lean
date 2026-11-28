/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Tests.Cbor

/-!
`Lanes.Cbor.decode` and `Lanes.Cbor.encodeDeterministic` against Python's cbor2
(`oracles/cbor2/main.py`). The inputs are RFC 8949's examples of Appendix A and F, the encodings
of random values, preferred or not, those with a byte changed, put in or taken out, and random
bytes. Two ops: `decode`, the value read, as a description both sides write; and `canonical`,
the value read and written in cbor2's canonical form, against our deterministic encoding.
-/

namespace Tests.Oracle.Cbor

open Lanes Lanes.Cbor

/-- Limits no generated input reaches, so that both decoders refuse only what is malformed. -/
def cfg : Config := { maxDepth := 10000, maxLength := 2 ^ 24, maxSize := 2 ^ 24 }

def hex64 (bits : UInt64) : String :=
  Bytes.hex ⟨(List.range 8).reverse.toArray.map fun i => (bits >>> (8 * i).toUInt64).toUInt8⟩

/-- The description `oracles/cbor2/main.py` writes; `fuel` bounds the nesting. -/
def describe : (fuel : Nat) → Cbor → Json
  | 0, _ => .null
  | _ + 1, .uint n => .arr #["u", .str (toString n)]
  | _ + 1, .nint n => .arr #["n", .str (toString n)]
  | _ + 1, .float bits => .arr #["f", .str (hex64 bits)]
  | _ + 1, .text s => .arr #["t", .str s]
  | _ + 1, .bytes b => .arr #["h", .str (Bytes.hex b)]
  | fuel + 1, .array xs => .arr #["a", .arr (xs.map (describe fuel)).toArray]
  | fuel + 1, .map es =>
    .arr #["m", .arr (es.map fun e => Json.arr #[describe fuel e.1, describe fuel e.2]).toArray]
  | fuel + 1, .tag t x => .arr #["tag", .str (toString t), describe fuel x]
  | _ + 1, .simple v => .arr #["s", (v.val.toNat : Json)]
  | _ + 1, .bool b => .arr #["b", .bool b]
  | _ + 1, .null => .arr #["null"]
  | _ + 1, .undefined => .arr #["undefined"]

def answer (c : Case) : Answer :=
  match decode cfg c.input with
  | .error _ => none
  | .ok v =>
    if c.op == "decode" then some (describe 10000 v)
    else some (.str (Bytes.hex (encodeDeterministic v)))

def isNan (bits : UInt64) : Bool := Tests.Cbor.isNan bits

/-- `v` with every NaN the one cbor2 writes. -/
def quietNans : (fuel : Nat) → Cbor → Cbor
  | fuel + 1, .array xs => .array (xs.map (quietNans fuel))
  | fuel + 1, .map es => .map (es.map fun e => (quietNans fuel e.1, quietNans fuel e.2))
  | fuel + 1, .tag t x => .tag t (quietNans fuel x)
  | _, .float bits => .float (if isNan bits then 0x7ff8000000000000 else bits)
  | _, v => v

def hasNan (v : Cbor) : Bool := quietNans 10000 v != v

/-- A key as Python compares it: `false`, `true`, a simple value and a float that is a whole number
equal to the integer, inside arrays, maps and tags too. -/
def pythonKey : (fuel : Nat) → Cbor → Cbor
  | _, .bool false => .uint 0
  | _, .bool true => .uint 1
  | _, .simple v => .uint v.val.toUInt64
  | _, .float bits =>
    let f := Float.ofBits bits
    if f.isFinite && f == f.floor && f.abs < 18446744073709551616.0 then
      if 0 ≤ f then .uint f.toUInt64 else .nint (-1 - f).toUInt64
    else .float bits
  | fuel + 1, .array xs => .array (xs.map (pythonKey fuel))
  | fuel + 1, .map es => .map (es.map fun e => (pythonKey fuel e.1, pythonKey fuel e.2))
  | fuel + 1, .tag t x => .tag t (pythonKey fuel x)
  | _, v => v

/-- Some map holds two keys Python counts equal. -/
def twiceKeyed : (fuel : Nat) → Cbor → Bool
  | fuel + 1, .array xs => xs.any (twiceKeyed fuel)
  | fuel + 1, .map es =>
    let keys := es.map (pythonKey 10000 ·.1)
    keys.eraseDups.length != keys.length || es.any fun e => twiceKeyed fuel e.1 || twiceKeyed fuel e.2
  | fuel + 1, .tag _ x => twiceKeyed fuel x
  | _, _ => false

/-- A description with each NaN's bits forgotten. -/
def forgetNans : (fuel : Nat) → Json → Json
  | _ + 1, .arr #[.str "f", .str h] =>
    match Bytes.unhex? h with
    | some b =>
      if isNan (b.foldl (fun acc x => acc * 256 + x.toUInt64) 0) then .arr #["f", "nan"]
      else .arr #["f", .str h]
    | none => .arr #["f", .str h]
  | fuel + 1, .arr xs => .arr (xs.map (forgetNans fuel))
  | _, j => j

def known (c : Case) (go : Answer) : Option String :=
  match decode cfg c.input, go with
  | .ok v, none =>
    if twiceKeyed 10000 v then
      some "cbor2 refuses a map with two keys Python counts equal (`true`, `1`, `1.0` and \
        `simple(1)`, or one key twice); Lanes reads every entry, and a derived reader takes a field's first"
    else none
  | .ok v, some theirs =>
    if c.op == "decode" then
      if hasNan v && forgetNans 10000 (describe 10000 v) == forgetNans 10000 theirs then
        some "cbor2 reads a NaN as Python's float, which keeps a NaN's payload only in part"
      else none
    else
      match theirs with
      | .str h =>
        match (Bytes.unhex? h).map (decode cfg) with
        | some (.ok w) =>
          if encodeDeterministic (quietNans 10000 w) == encodeDeterministic (quietNans 10000 v) then
            if hasNan v then some "cbor2 writes every NaN as f97e00, Lanes keeps its payload"
            else some "cbor2's canonical order puts shorter keys first (RFC 7049 §3.9); RFC 8949 \
              §4.2.1, which Lanes follows, sorts keys bytewise"
          else none
        | _ => none
      | _ => none
  | _, _ => none

/-- One byte changed, put in or taken out. -/
def mutate (b : ByteArray) : Oracle.Gen ByteArray := do
  let bytes := b.data.toList
  let at_ ← Oracle.Gen.below (bytes.length + 1)
  let x := (← Oracle.Gen.below 256).toUInt8
  match ← Oracle.Gen.below 3 with
  | 0 => return (bytes.eraseIdx at_).toByteArray
  | 1 => return (bytes.insertIdx at_ x).toByteArray
  | _ => return (bytes.set at_ x).toByteArray

def case : Oracle.Gen Case := do
  let op ← Oracle.Gen.pick ["decode", "canonical"]
  let v ← Tests.Cbor.genCbor 3
  let input ← match ← Oracle.Gen.below 10 with
    | 0 | 1 | 2 | 3 => pure (encode v)
    | 4 | 5 | 6 => Tests.Cbor.loose 10 v
    | 7 | 8 => mutate (encode v)
    | _ => Oracle.Gen.bytes 12
  return ⟨op, input⟩

def edges : List Case :=
  let ops := ["decode", "canonical"]
  (Tests.Cbor.appendixA.flatMap fun (_, h) => ops.map fun op => ⟨op, Tests.Cbor.hexOf h⟩)
    ++ (Tests.Cbor.appendixALoose.flatMap fun (h, _) => ops.map fun op => ⟨op, Tests.Cbor.hexOf h⟩)
    ++ (Tests.Cbor.appendixF.map fun h => ⟨"decode", Tests.Cbor.hexOf h⟩)

def package : Package where
  name := "cbor"
  reference := .python "cbor2"
  edges := edges
  case := case
  answer := answer
  known := known
  recorded := 1000

end Tests.Oracle.Cbor
