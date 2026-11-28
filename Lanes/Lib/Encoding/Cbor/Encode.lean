/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Cbor.Basic
public import Lanes.Lib.Encoding.Digits

/-!
# Writing CBOR

`Cbor.encode` writes the preferred serialization (RFC 8949 §4.1): every argument in the fewest
bytes that hold it, every length definite, every float in the shortest width that holds it
exactly. A map's entries are written in their order.

`Cbor.encodeDeterministic` writes the deterministic encoding of §4.2.1: the preferred
serialization of `canonical v`, which is `v` with every map's entries sorted by their encodings,
bytewise. An entry is sorted by its key's bytes and then its value's, written one after the other:
an item's encoding never starts another's, so this is the order of the keys, and entries with
equal keys, which a valid map does not have, still have one order.
-/

@[expose] public section

namespace Lanes.Cbor

/-- The last `width` bytes of `n`, most significant first. -/
def argument (width n : Nat) : List UInt8 := (Digits.split 256 width n).map Nat.toUInt8

/-- A head whose argument follows it in `2 ^ (info - 24)` bytes: additional information 24 to
27. -/
def longHead (major info n : Nat) : List UInt8 :=
  (major * 32 + info).toUInt8 :: argument (2 ^ (info - 24)) n

/-- The head of an item of major type `major` whose argument is `n`, in the fewest bytes. -/
def head (major n : Nat) : List UInt8 :=
  if n < 24 then [(major * 32 + n).toUInt8]
  else if n < 2 ^ 8 then longHead major 24 n
  else if n < 2 ^ 16 then longHead major 25 n
  else if n < 2 ^ 32 then longHead major 26 n
  else longHead major 27 n

/-- A float in the shortest of the three widths that holds it exactly. -/
def floatHead (bits : UInt64) : List UInt8 :=
  match toHalf? bits with
  | some h => longHead 7 25 h.toNat
  | none =>
    match toSingle? bits with
    | some s => longHead 7 26 s.toNat
    | none => longHead 7 27 bits.toNat

/-- `bytes` after `out`. -/
def push (out : ByteArray) (bytes : List UInt8) : ByteArray := bytes.foldl ByteArray.push out

mutual
/-- The preferred serialization of an item, after `out`. -/
def encodeTo (out : ByteArray) : Cbor → ByteArray
  | .uint n => push out (head 0 n.toNat)
  | .nint n => push out (head 1 n.toNat)
  | .bytes b => push out (head 2 b.size) ++ b
  | .text s => push out (head 3 s.utf8ByteSize) ++ s.toUTF8
  | .array items => encodeAll (push out (head 4 items.length)) items
  | .map entries => encodeEntries (push out (head 5 entries.length)) entries
  | .tag t item => encodeTo (push out (head 6 t.toNat)) item
  | .bool false => push out (head 7 20)
  | .bool true => push out (head 7 21)
  | .null => push out (head 7 22)
  | .undefined => push out (head 7 23)
  | .simple v => push out (head 7 v.val.toNat)
  | .float bits => push out (floatHead bits)

def encodeAll (out : ByteArray) : List Cbor → ByteArray
  | [] => out
  | x :: xs => encodeAll (encodeTo out x) xs

def encodeEntries (out : ByteArray) : List (Cbor × Cbor) → ByteArray
  | [] => out
  | e :: es => encodeEntries (encodeTo (encodeTo out e.1) e.2) es
end

/-- The preferred serialization (§4.1). -/
def encode (v : Cbor) : ByteArray := encodeTo .empty v

/-- A map's entry as written: its key's bytes, then its value's. -/
def entryBytes (e : Cbor × Cbor) : ByteArray := encodeTo (encode e.1) e.2

/-- Entries in the order of their bytes. -/
def sortEntries (entries : List (Cbor × Cbor)) : List (Cbor × Cbor) :=
  ((entries.map fun e => (entryBytes e, e)).mergeSort fun a b => a.1 ≤ b.1).map (·.2)

mutual
/-- `v` with every map's entries in the order of their deterministic encodings. -/
def canonical : Cbor → Cbor
  | .array items => .array (canonicalAll items)
  | .map entries => .map (sortEntries (canonicalEntries entries))
  | .tag t item => .tag t (canonical item)
  | v => v

def canonicalAll : List Cbor → List Cbor
  | [] => []
  | x :: xs => canonical x :: canonicalAll xs

def canonicalEntries : List (Cbor × Cbor) → List (Cbor × Cbor)
  | [] => []
  | e :: es => (canonical e.1, canonical e.2) :: canonicalEntries es
end

/-- The deterministic encoding (§4.2.1). -/
def encodeDeterministic (v : Cbor) : ByteArray := encode (canonical v)

end Lanes.Cbor
