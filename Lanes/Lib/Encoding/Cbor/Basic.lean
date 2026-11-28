/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# CBOR values

`Cbor` is the data model of CBOR (RFC 8949 §2): each value has one representation, so `=` is the
equality of the data model but for the order of a map's entries, which is kept.

- An integer is `uint n` or `nint n`, the number `-1 - n`: the two major types, each with a
  64-bit argument (§3.1).
- A simple value is `bool`, `null`, `undefined`, or `simple v` for the others: a byte that is not
  20 to 31, since 20 to 23 are the named four and 24 to 31 are not well-formed (§3.3).
- A float is the bits of an IEEE 754 binary64 number. The data model does not tell a half from a
  double of the same value (§2), so the encoder chooses the width: the shortest that holds the
  value exactly (§4.1), and a half or a single read is widened to the double it holds.
  `ofHalf` and `ofSingle` widen; `toHalf?` and `toSingle?` narrow, and a narrowing is kept only
  when widening it gives the value back, so it loses nothing by construction.

`fits depth length` says that a value is within a decoder's limits: at most `depth` levels of
nesting, counting a tag as a level, and at most `length` bytes in a string and entries in an
array or a map.
-/

@[expose] public section

namespace Lanes

/-- A simple value other than `false`, `true`, `null` and `undefined`: 0 to 19, or 32 to 255. -/
abbrev Cbor.Simple := {v : UInt8 // v < 20 ∨ 32 ≤ v}

inductive Cbor where
  | uint (n : UInt64)
  /-- The negative integer `-1 - n`. -/
  | nint (n : UInt64)
  | bytes (b : ByteArray)
  | text (s : String)
  | array (items : List Cbor)
  | map (entries : List (Cbor × Cbor))
  | tag (number : UInt64) (item : Cbor)
  | bool (b : Bool)
  | null
  | undefined
  | simple (v : Cbor.Simple)
  /-- The bits of an IEEE 754 binary64 number. -/
  | float (bits : UInt64)
  deriving Inhabited

namespace Cbor

mutual
def beq : Cbor → Cbor → Bool
  | .uint n, .uint m | .nint n, .nint m | .float n, .float m => n == m
  | .bytes a, .bytes b => a == b
  | .text a, .text b => a == b
  | .array xs, .array ys => beqList xs ys
  | .map xs, .map ys => beqEntries xs ys
  | .tag t v, .tag u w => t == u && beq v w
  | .bool a, .bool b => a == b
  | .null, .null | .undefined, .undefined => true
  | .simple a, .simple b => a == b
  | _, _ => false

def beqList : List Cbor → List Cbor → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false

def beqEntries : List (Cbor × Cbor) → List (Cbor × Cbor) → Bool
  | [], [] => true
  | e :: xs, f :: ys => beq e.1 f.1 && beq e.2 f.2 && beqEntries xs ys
  | _, _ => false
end

mutual
theorem eq_of_beq : (a b : Cbor) → beq a b = true → a = b
  | .array xs, b, h => by
    cases b <;> (try simp [beq] at h)
    rw [eq_of_beqList xs _ h]
  | .map xs, b, h => by
    cases b <;> (try simp [beq] at h)
    rw [eq_of_beqEntries xs _ h]
  | .tag t v, b, h => by
    cases b <;> (try simp [beq] at h)
    rw [h.1, eq_of_beq v _ h.2]
  | .simple v, b, h => by
    cases b <;> (try simp [beq] at h)
    rw [Subtype.ext h]
  | .uint _, b, h | .nint _, b, h | .float _, b, h | .bytes _, b, h | .text _, b, h
  | .bool _, b, h | .null, b, h | .undefined, b, h => by
    cases b <;> simp_all [beq]

theorem eq_of_beqList : (xs ys : List Cbor) → beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [beqList, Bool.and_eq_true] at h
    rw [eq_of_beq x y h.1, eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [beqList] at h

theorem eq_of_beqEntries : (xs ys : List (Cbor × Cbor)) → beqEntries xs ys = true → xs = ys
  | [], [], _ => rfl
  | e :: xs, f :: ys, h => by
    simp only [beqEntries, Bool.and_eq_true] at h
    rw [Prod.ext (eq_of_beq e.1 f.1 h.1.1) (eq_of_beq e.2 f.2 h.1.2), eq_of_beqEntries xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [beqEntries] at h
end

mutual
theorem beq_self : (a : Cbor) → beq a a = true
  | .uint _ | .nint _ | .float _ | .bytes _ | .text _ | .bool _ | .simple _ | .null | .undefined => by
    simp [beq]
  | .array xs => by simp only [beq]; exact beqList_self xs
  | .map xs => by simp only [beq]; exact beqEntries_self xs
  | .tag _ v => by simp only [beq, beq_self_eq_true, Bool.true_and]; exact beq_self v

theorem beqList_self : (xs : List Cbor) → beqList xs xs = true
  | [] => rfl
  | x :: xs => by simp only [beqList, Bool.and_eq_true]; exact ⟨beq_self x, beqList_self xs⟩

theorem beqEntries_self : (xs : List (Cbor × Cbor)) → beqEntries xs xs = true
  | [] => rfl
  | e :: xs => by
    simp only [beqEntries, Bool.and_eq_true]
    exact ⟨⟨beq_self e.1, beq_self e.2⟩, beqEntries_self xs⟩
end

instance : DecidableEq Cbor := fun a b =>
  decidable_of_iff (beq a b = true) ⟨eq_of_beq a b, fun h => h ▸ beq_self a⟩

/-- The two hexadecimal digits of each byte. -/
def hexBytes (b : ByteArray) : String :=
  b.foldl (init := "") fun acc x =>
    let digit (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
    (acc.push (digit (x.toNat / 16))).push (digit (x.toNat % 16))

mutual
/-- The diagnostic notation of RFC 8949 §8, for messages and tests; a float as its bits. -/
def diagnostic : Cbor → String
  | .uint n => toString n
  | .nint n => "-" ++ toString (n.toNat + 1)
  | .bytes b => "h'" ++ hexBytes b ++ "'"
  | .text s => s.quote
  | .array items => "[" ++ diagnosticAll items ++ "]"
  | .map entries => "{" ++ diagnosticEntries entries ++ "}"
  | .tag t item => toString t ++ "(" ++ diagnostic item ++ ")"
  | .bool b => toString b
  | .null => "null"
  | .undefined => "undefined"
  | .simple v => "simple(" ++ toString v.val ++ ")"
  | .float bits => "float(" ++ toString bits.toNat ++ ")"

def diagnosticAll : List Cbor → String
  | [] => ""
  | [x] => diagnostic x
  | x :: xs => diagnostic x ++ ", " ++ diagnosticAll xs

def diagnosticEntries : List (Cbor × Cbor) → String
  | [] => ""
  | [e] => diagnostic e.1 ++ ": " ++ diagnostic e.2
  | e :: es => diagnostic e.1 ++ ": " ++ diagnostic e.2 ++ ", " ++ diagnosticEntries es
end

instance : Repr Cbor := ⟨fun v _ => v.diagnostic⟩
instance : ToString Cbor := ⟨diagnostic⟩

/-- The value of a text key in a map, the first if there are two. -/
def lookup (entries : List (Cbor × Cbor)) (key : String) : Option Cbor :=
  (entries.find? (·.1 == .text key)).map (·.2)

/-- Within `depth` levels of nesting and `length` bytes or entries in each string, array and
map. -/
def fits : (depth : Nat) → (length : Nat) → Cbor → Bool
  | 0, _, _ => false
  | _ + 1, length, .bytes b => b.size ≤ length
  | _ + 1, length, .text s => s.utf8ByteSize ≤ length
  | d + 1, length, .array items => items.length ≤ length && items.all (fits d length)
  | d + 1, length, .map entries =>
    entries.length ≤ length && entries.all fun e => fits d length e.1 && fits d length e.2
  | d + 1, length, .tag _ item => fits d length item
  | _ + 1, _, _ => true

/-! ### Floats by their bits -/

/-- A normal number: its exponent field and its fraction, as binary64 bits. -/
def double (sign exponent fraction : Nat) : UInt64 :=
  (sign * 2 ^ 63 + exponent * 2 ^ 52 + fraction).toUInt64

/-- A subnormal of a narrower format, `fraction · 2 ^ -scale` with `0 < fraction`, as a normal
binary64. -/
def subnormal (sign fraction scale : Nat) : UInt64 :=
  let k := fraction.log2
  double sign (k + 1023 - scale) ((fraction - 2 ^ k) * 2 ^ (52 - k))

/-- The binary64 number a binary16 holds (IEEE 754 §3.6). -/
def ofHalf (h : UInt16) : UInt64 :=
  let h := h.toNat
  let sign := h / 2 ^ 15
  let exponent := h / 2 ^ 10 % 2 ^ 5
  let fraction := h % 2 ^ 10
  if exponent = 0 then
    if fraction = 0 then double sign 0 0 else subnormal sign fraction 24
  else if exponent = 31 then double sign 2047 (fraction * 2 ^ 42)
  else double sign (exponent + 1008) (fraction * 2 ^ 42)

/-- The binary64 number a binary32 holds. -/
def ofSingle (s : UInt32) : UInt64 :=
  let s := s.toNat
  let sign := s / 2 ^ 31
  let exponent := s / 2 ^ 23 % 2 ^ 8
  let fraction := s % 2 ^ 23
  if exponent = 0 then
    if fraction = 0 then double sign 0 0 else subnormal sign fraction 149
  else if exponent = 255 then double sign 2047 (fraction * 2 ^ 29)
  else double sign (exponent + 896) (fraction * 2 ^ 29)

/-- The binary16 to try for a binary64: the right one if any holds it. -/
def halfCandidate (b : UInt64) : UInt16 :=
  let b := b.toNat
  let sign := b / 2 ^ 63 * 2 ^ 15
  let exponent := b / 2 ^ 52 % 2 ^ 11
  let fraction := b % 2 ^ 52
  (if exponent = 2047 then sign + 0x7c00 + fraction / 2 ^ 42
  else if 1009 ≤ exponent ∧ exponent ≤ 1038 then
    sign + (exponent - 1008) * 2 ^ 10 + fraction / 2 ^ 42
  else if 999 ≤ exponent ∧ exponent ≤ 1008 then
    sign + (2 ^ 52 + fraction) / 2 ^ (1051 - exponent)
  else sign).toUInt16

def singleCandidate (b : UInt64) : UInt32 :=
  let b := b.toNat
  let sign := b / 2 ^ 63 * 2 ^ 31
  let exponent := b / 2 ^ 52 % 2 ^ 11
  let fraction := b % 2 ^ 52
  (if exponent = 2047 then sign + 0x7f800000 + fraction / 2 ^ 29
  else if 897 ≤ exponent ∧ exponent ≤ 1150 then
    sign + (exponent - 896) * 2 ^ 23 + fraction / 2 ^ 29
  else if 874 ≤ exponent ∧ exponent ≤ 896 then
    sign + (2 ^ 52 + fraction) / 2 ^ (926 - exponent)
  else sign).toUInt32

/-- The binary16 that holds this binary64 exactly, if one does. -/
def toHalf? (b : UInt64) : Option UInt16 :=
  let h := halfCandidate b
  if ofHalf h = b then some h else none

def toSingle? (b : UInt64) : Option UInt32 :=
  let s := singleCandidate b
  if ofSingle s = b then some s else none

theorem ofHalf_of_toHalf? {b : UInt64} {h : UInt16} (e : toHalf? b = some h) : ofHalf h = b := by
  unfold toHalf? at e
  dsimp only at e
  split at e
  · cases e; assumption
  · cases e

theorem ofSingle_of_toSingle? {b : UInt64} {s : UInt32} (e : toSingle? b = some s) :
    ofSingle s = b := by
  unfold toSingle? at e
  dsimp only at e
  split at e
  · cases e; assumption
  · cases e

end Cbor

end Lanes
