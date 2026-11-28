/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
Percent-encoding (RFC 3986, section 2.1): a byte as `%HH`, and the bytes RFC 3986 lets a URL
carry unescaped (`unreserved`) as themselves. Decoding reads back what was encoded
(`percentDecode_percentEncode`). URLs (`Lanes/Lib/Net/Url.lean`) and HTTP's forms and cookies
(`Lanes/Web/Http/Basic.lean`) both use it.
-/

@[expose] public section

namespace Lanes.Http

def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def percentDecodeBytes (plusIsSpace : Bool) : List Char → Option (List UInt8)
  | [] => some []
  | '%' :: hi :: lo :: rest => do
    let h ← hexValue? hi
    let l ← hexValue? lo
    let rest ← percentDecodeBytes plusIsSpace rest
    return UInt8.ofNat (h * 16 + l) :: rest
  | '%' :: _ => none
  | c :: rest => do
    let rest ← percentDecodeBytes plusIsSpace rest
    return (if c == '+' && plusIsSpace then " " else c.toString).toUTF8.data.toList ++ rest

/-- `none` if an escape is malformed or the result is not UTF-8. -/
def percentDecode (s : String) (plusIsSpace : Bool := false) : Option String := do
  let bytes ← percentDecodeBytes plusIsSpace s.toList
  String.fromUTF8? (ByteArray.mk bytes.toArray)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- Letters, digits and `-._~`: the bytes RFC 3986 lets a URL carry unescaped everywhere. -/
def unreserved (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)
    || b == 45 || b == 46 || b == 95 || b == 126

def percentEncodeByte (b : UInt8) : List Char :=
  if unreserved b then [Char.ofNat b.toNat]
  else ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def percentEncode (s : String) : String :=
  String.ofList (s.toUTF8.data.toList.flatMap percentEncodeByte)

private theorem hexValue?_hexDigit : ∀ n, n < 16 → hexValue? (hexDigit n) = some n := by decide

private theorem unreserved_plain : ∀ b : UInt8, unreserved b →
    Char.ofNat b.toNat ≠ '%' ∧ Char.ofNat b.toNat ≠ '+' ∧ (Char.ofNat b.toNat).utf8Size = 1
      ∧ (Char.ofNat b.toNat).val.toUInt8 = b := by decide

private theorem ofNat_nibbles :
    ∀ b : UInt8, UInt8.ofNat (b.toNat / 16) * 16 + UInt8.ofNat (b.toNat % 16) = b := by decide

private theorem percentDecodeBytes_encodeByte (plusIsSpace : Bool) (b : UInt8) (cs : List Char) :
    percentDecodeBytes plusIsSpace (percentEncodeByte b ++ cs)
      = (percentDecodeBytes plusIsSpace cs).map (b :: ·) := by
  unfold percentEncodeByte
  split
  · rename_i h
    obtain ⟨h1, h2, h3, h4⟩ := unreserved_plain b h
    rw [List.singleton_append, percentDecodeBytes]
    · simp [h2, Char.toString, String.toByteArray_singleton, List.utf8Encode_singleton,
        String.utf8EncodeChar_eq_singleton h3, h4]
      cases percentDecodeBytes plusIsSpace cs <;> simp
    · intro hi lo rest h _; exact h1 h
    · intro h; exact h1 h
  · have h16 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
    simp [percentDecodeBytes, hexValue?_hexDigit _ h16,
      hexValue?_hexDigit _ (Nat.mod_lt _ (by decide : 16 > 0)), ofNat_nibbles]
    cases percentDecodeBytes plusIsSpace cs <;> simp

private theorem percentDecodeBytes_encode (plusIsSpace : Bool) (bs : List UInt8) :
    percentDecodeBytes plusIsSpace (bs.flatMap percentEncodeByte) = some bs := by
  induction bs with
  | nil => simp [percentDecodeBytes]
  | cons b bs ih => simp [List.flatMap_cons, percentDecodeBytes_encodeByte, ih]

/-- Decoding reads back what was encoded, with `+` read as a space or not: an encoding has no `+`. -/
theorem percentDecode_percentEncode (s : String) (plusIsSpace : Bool := false) :
    percentDecode (percentEncode s) plusIsSpace = some s := by
  simp [percentDecode, percentEncode, percentDecodeBytes_encode, String.fromUTF8?, s.isValidUTF8,
    String.fromUTF8]

private theorem percentEncodeByte_plain :
    ∀ b : UInt8, ∀ c ∈ percentEncodeByte b, c ≠ '&' ∧ c ≠ '=' ∧ c ≠ ';' := by decide

/-- An encoding has no `&`, `=` or `;`, so it cannot end a field of a form or a cookie. -/
theorem percentEncode_plain (s : String) :
    ∀ c ∈ (percentEncode s).toList, c ≠ '&' ∧ c ≠ '=' ∧ c ≠ ';' := by
  intro c hc
  simp only [percentEncode, String.toList_ofList, List.mem_flatMap] at hc
  obtain ⟨b, -, hb⟩ := hc
  exact percentEncodeByte_plain b c hb

end Lanes.Http
