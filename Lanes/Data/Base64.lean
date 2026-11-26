/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Base64 (RFC 4648 §4 and §5): the standard and URL-safe alphabets, each with and without
padding, as Go names them (`StdEncoding`, `RawStdEncoding`, `URLEncoding`, `RawURLEncoding`).

`decode e s = some b ↔ encode e b = s` (`decode_eq_some_iff`): every byte string has exactly one
spelling, and `decode` accepts nothing else. Go's strict decoders also skip `\r` and `\n`; this
one does not (`docs/decisions/new-differential-tests-against-go.md`).
-/

@[expose] public section

namespace Lanes.Base64

inductive Alphabet where
  | std
  | url
  deriving DecidableEq, Repr, Inhabited

def Alphabet.last : Alphabet → Char × Char
  | .std => ('+', '/')
  | .url => ('-', '_')

def Alphabet.code (a : Alphabet) (v : Nat) : Nat :=
  if v < 26 then 65 + v
  else if v < 52 then 71 + v
  else if v < 62 then v - 4
  else if v = 62 then a.last.1.toNat
  else a.last.2.toNat

def Alphabet.char (a : Alphabet) (v : Fin 64) : Char := Char.ofNat (a.code v.val)

def Alphabet.valueOf (a : Alphabet) (c : Char) : Nat :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat - 65
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then c.toNat - 71
  else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat + 4
  else if c = a.last.1 then 62
  else if c = a.last.2 then 63
  else 64

def Alphabet.value? (a : Alphabet) (c : Char) : Option (Fin 64) :=
  if h : a.valueOf c < 64 then some ⟨a.valueOf c, h⟩ else none

theorem Alphabet.value?_char (a : Alphabet) (v : Fin 64) : a.value? (a.char v) = some v := by
  cases a <;> revert v <;> decide

private theorem Alphabet.code_valueOf (a : Alphabet) (c : Char) (h : a.valueOf c < 64) :
    a.code (a.valueOf c) = c.toNat := by
  have hl : a.last.1.toNat < 48 ∧ a.last.2.toNat < 48 ∨ a.last.2.toNat = 95 ∧ a.last.1.toNat < 48 := by
    cases a <;> decide
  unfold valueOf at h ⊢
  split
  · simp only [code]; split <;> omega
  · split
    · simp only [code]; repeat' split
      all_goals omega
    · split
      · simp only [code]; repeat' split
        all_goals omega
      · split
        · rename_i hc; subst hc; simp [code]
        · split
          · rename_i hc; subst hc; simp [code]
          · simp_all

theorem Alphabet.char_of_value? {a : Alphabet} {c : Char} {v : Fin 64}
    (h : a.value? c = some v) : a.char v = c := by
  unfold value? at h
  split at h
  · rename_i hv
    simp only [Option.some.injEq] at h
    subst h
    rw [char, code_valueOf a c hv, Char.ofNat_toNat]
  · cases h

theorem Alphabet.char_ne_pad (a : Alphabet) (v : Fin 64) : a.char v ≠ '=' := by
  cases a <;> revert v <;> decide

structure Encoding where
  alphabet : Alphabet
  padded : Bool
  deriving DecidableEq, Repr, Inhabited

def Encoding.std : Encoding := ⟨.std, true⟩
def Encoding.rawStd : Encoding := ⟨.std, false⟩
def Encoding.url : Encoding := ⟨.url, true⟩
def Encoding.rawUrl : Encoding := ⟨.url, false⟩

def sextet (n : Nat) : Fin 64 := ⟨n % 64, Nat.mod_lt _ (by decide)⟩

def byte (n : Nat) : UInt8 := UInt8.ofNat n

section

variable (e : Encoding)

def pad (n : Nat) : List Char := if e.padded then List.replicate n '=' else []

def encodeList : List UInt8 → List Char
  | [] => []
  | [b0] =>
    let c := e.alphabet.char
    [c (sextet (b0.toNat / 4)), c (sextet (b0.toNat % 4 * 16))] ++ pad e 2
  | [b0, b1] =>
    let c := e.alphabet.char
    [c (sextet (b0.toNat / 4)), c (sextet (b0.toNat % 4 * 16 + b1.toNat / 16)),
      c (sextet (b1.toNat % 16 * 4))] ++ pad e 1
  | b0 :: b1 :: b2 :: rest =>
    let c := e.alphabet.char
    c (sextet (b0.toNat / 4)) :: c (sextet (b0.toNat % 4 * 16 + b1.toNat / 16))
      :: c (sextet (b1.toNat % 16 * 4 + b2.toNat / 64)) :: c (sextet (b2.toNat % 64))
      :: encodeList rest

def full (c0 c1 c2 c3 : Char) : Option (List UInt8) := do
  let v0 ← e.alphabet.value? c0
  let v1 ← e.alphabet.value? c1
  let v2 ← e.alphabet.value? c2
  let v3 ← e.alphabet.value? c3
  return [byte (v0.val * 4 + v1.val / 16), byte (v1.val % 16 * 16 + v2.val / 4),
    byte (v2.val % 4 * 64 + v3.val)]

def tail1 (c0 c1 : Char) : Option (List UInt8) := do
  let v0 ← e.alphabet.value? c0
  let v1 ← e.alphabet.value? c1
  if v1.val % 16 = 0 then return [byte (v0.val * 4 + v1.val / 16)] else none

def tail2 (c0 c1 c2 : Char) : Option (List UInt8) := do
  let v0 ← e.alphabet.value? c0
  let v1 ← e.alphabet.value? c1
  let v2 ← e.alphabet.value? c2
  if v2.val % 4 = 0 then return [byte (v0.val * 4 + v1.val / 16), byte (v1.val % 16 * 16 + v2.val / 4)]
  else none

def decodeList : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | [c0, c1] => if e.padded then none else tail1 e c0 c1
  | [c0, c1, c2] => if e.padded then none else tail2 e c0 c1 c2
  | [c0, c1, c2, c3] =>
    if e.padded ∧ c2 = '=' ∧ c3 = '=' then tail1 e c0 c1
    else if e.padded ∧ c3 = '=' then tail2 e c0 c1 c2
    else full e c0 c1 c2 c3
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest => do
    let bytes ← full e c0 c1 c2 c3
    return bytes ++ (← decodeList (c4 :: rest))

def encode (bytes : ByteArray) : String := String.ofList (encodeList e bytes.data.toList)

def decode (s : String) : Option ByteArray :=
  (decodeList e s.toList).map fun bytes => ⟨bytes.toArray⟩

end

private theorem byte_toNat {n : Nat} (h : n < 256) : (byte n).toNat = n := by
  simp [byte, UInt8.toNat_ofNat']; omega

private theorem byte_eq {n : Nat} {b : UInt8} (h : n = b.toNat) : byte n = b := by
  rw [← UInt8.toNat_inj, byte_toNat (by have := b.toNat_lt; omega), h]

private theorem full_encode (e : Encoding) (b0 b1 b2 : UInt8) :
    full e (e.alphabet.char (sextet (b0.toNat / 4)))
      (e.alphabet.char (sextet (b0.toNat % 4 * 16 + b1.toNat / 16)))
      (e.alphabet.char (sextet (b1.toNat % 16 * 4 + b2.toNat / 64)))
      (e.alphabet.char (sextet (b2.toNat % 64))) = some [b0, b1, b2] := by
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
  simp only [full, Alphabet.value?_char, sextet, Option.bind_eq_bind, Option.bind_some]
  simp only [pure, Option.some.injEq, List.cons.injEq, and_true]
  refine ⟨byte_eq ?_, byte_eq ?_, byte_eq ?_⟩ <;> omega

private theorem encodeList_ne_nil (e : Encoding) {bytes : List UInt8} (h : bytes ≠ []) :
    encodeList e bytes ≠ [] := by
  match bytes, h with
  | [_], _ | [_, _], _ | _ :: _ :: _ :: _, _ => simp [encodeList]

theorem decodeList_encodeList (e : Encoding) (bytes : List UInt8) :
    decodeList e (encodeList e bytes) = some bytes := by
  match bytes with
  | [] => rfl
  | [b0] =>
    have := b0.toNat_lt
    cases hp : e.padded <;>
      simp [encodeList, decodeList, pad, hp, tail1, Alphabet.value?_char, sextet] <;>
      exact byte_eq (by omega)
  | [b0, b1] =>
    have := b0.toNat_lt; have := b1.toNat_lt
    cases hp : e.padded <;>
      simp [encodeList, decodeList, pad, hp, tail2, Alphabet.value?_char, Alphabet.char_ne_pad, sextet] <;>
      exact ⟨byte_eq (by omega), byte_eq (by omega)⟩
  | [b0, b1, b2] =>
    simp only [encodeList, decodeList, Alphabet.char_ne_pad, and_false, ite_false]
    exact full_encode e b0 b1 b2
  | b0 :: b1 :: b2 :: b3 :: rest =>
    have ih := decodeList_encodeList e (b3 :: rest)
    cases hr : encodeList e (b3 :: rest) with
    | nil => exact absurd hr (encodeList_ne_nil e (List.cons_ne_nil _ _))
    | cons c4 more =>
      rw [hr] at ih
      simp only [encodeList, hr, decodeList, full_encode, ih, Option.bind_eq_bind, Option.bind_some]
      rfl

private theorem value?_some {a : Alphabet} {c : Char} {v : Fin 64} (h : a.value? c = some v) :
    c = a.char v := (Alphabet.char_of_value? h).symm

private theorem sextet_eq (v : Fin 64) {n : Nat} (h : n = v.val) : sextet n = v := by
  ext; simp [sextet, h]

private theorem encodeList_full {e : Encoding} {c0 c1 c2 c3 : Char} {bytes : List UInt8}
    (h : full e c0 c1 c2 c3 = some bytes) (rest : List UInt8) :
    encodeList e (bytes ++ rest) = c0 :: c1 :: c2 :: c3 :: encodeList e rest := by
  simp only [full, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨v0, h0, v1, h1, v2, h2, v3, h3, rfl⟩ := h
  have := v0.isLt; have := v1.isLt; have := v2.isLt; have := v3.isLt
  simp only [List.cons_append, List.nil_append, encodeList, value?_some h0, value?_some h1,
    value?_some h2, value?_some h3, byte_toNat (show v0.val * 4 + v1.val / 16 < 256 by omega),
    byte_toNat (show v1.val % 16 * 16 + v2.val / 4 < 256 by omega),
    byte_toNat (show v2.val % 4 * 64 + v3.val < 256 by omega)]
  rw [sextet_eq v0 (by omega), sextet_eq v1 (by omega), sextet_eq v2 (by omega),
    sextet_eq v3 (by omega)]

private theorem encodeList_tail1 {e : Encoding} {c0 c1 : Char} {bytes : List UInt8}
    (h : tail1 e c0 c1 = some bytes) : encodeList e bytes = [c0, c1] ++ pad e 2 := by
  simp only [tail1, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v0, h0, v1, h1, h⟩ := h
  split at h
  · simp only [pure, Option.some.injEq] at h
    subst h
    have := v0.isLt; have := v1.isLt
    simp only [encodeList, value?_some h0, value?_some h1,
      byte_toNat (show v0.val * 4 + v1.val / 16 < 256 by omega)]
    rw [sextet_eq v0 (by omega), sextet_eq v1 (by omega)]
  · cases h

private theorem encodeList_tail2 {e : Encoding} {c0 c1 c2 : Char} {bytes : List UInt8}
    (h : tail2 e c0 c1 c2 = some bytes) : encodeList e bytes = [c0, c1, c2] ++ pad e 1 := by
  simp only [tail2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v0, h0, v1, h1, v2, h2, h⟩ := h
  split at h
  · simp only [pure, Option.some.injEq] at h
    subst h
    have := v0.isLt; have := v1.isLt; have := v2.isLt
    simp only [encodeList, value?_some h0, value?_some h1, value?_some h2,
      byte_toNat (show v0.val * 4 + v1.val / 16 < 256 by omega),
      byte_toNat (show v1.val % 16 * 16 + v2.val / 4 < 256 by omega)]
    rw [sextet_eq v0 (by omega), sextet_eq v1 (by omega), sextet_eq v2 (by omega)]
  · cases h

theorem encodeList_of_decodeList {e : Encoding} {chars : List Char} {bytes : List UInt8}
    (h : decodeList e chars = some bytes) : encodeList e bytes = chars := by
  match chars, h with
  | [], h => cases h; rfl
  | [_], h => cases h
  | [c0, c1], h =>
    simp only [decodeList] at h
    split at h
    · cases h
    · rename_i hp; simp [encodeList_tail1 h, pad, hp]
  | [c0, c1, c2], h =>
    simp only [decodeList] at h
    split at h
    · cases h
    · rename_i hp; simp [encodeList_tail2 h, pad, hp]
  | [c0, c1, c2, c3], h =>
    simp only [decodeList] at h
    split at h
    · rename_i hp
      obtain ⟨hp, rfl, rfl⟩ := hp
      simp [encodeList_tail1 h, pad, hp]
    · split at h
      · rename_i hp
        obtain ⟨hp, rfl⟩ := hp
        simp [encodeList_tail2 h, pad, hp]
      · have := encodeList_full h []
        simpa [encodeList] using this
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest, h =>
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨first, hf, more, hm, rfl⟩ := h
    rw [encodeList_full hf, encodeList_of_decodeList hm]

theorem decode_eq_some_iff (e : Encoding) (s : String) (bytes : ByteArray) :
    decode e s = some bytes ↔ encode e bytes = s := by
  constructor
  · intro h
    simp only [decode, Option.map_eq_some_iff] at h
    obtain ⟨list, hd, rfl⟩ := h
    simp [encode, encodeList_of_decodeList hd]
  · rintro rfl
    simp [decode, encode, decodeList_encodeList]

theorem decode_encode (e : Encoding) (bytes : ByteArray) : decode e (encode e bytes) = some bytes :=
  (decode_eq_some_iff e _ bytes).mpr rfl

/-- What `encode` writes: a character of the alphabet, or `=` when the encoding pads. -/
def Encoding.Allowed (e : Encoding) (c : Char) : Prop :=
  (∃ v, e.alphabet.char v = c) ∨ (e.padded = true ∧ c = '=')

theorem allowed_of_mem_encodeList (e : Encoding) {bytes : List UInt8} {c : Char}
    (h : c ∈ encodeList e bytes) : e.Allowed c := by
  have pad_allowed : ∀ {n}, c ∈ pad e n → e.Allowed c := fun h => by
    unfold pad at h
    split at h
    · exact .inr ⟨by assumption, (List.mem_replicate.mp h).2⟩
    · cases h
  match bytes with
  | [] => cases h
  | [_] | [_, _] =>
    simp only [encodeList, List.cons_append, List.mem_cons, List.nil_append] at h
    repeat (first | (rcases h with rfl | h; exact .inl ⟨_, rfl⟩) | exact pad_allowed h)
  | _ :: _ :: _ :: rest =>
    simp only [encodeList, List.mem_cons] at h
    repeat (first | (rcases h with rfl | h; exact .inl ⟨_, rfl⟩) |
      exact allowed_of_mem_encodeList e h)

theorem allowed_of_mem_encode (e : Encoding) (bytes : ByteArray) {c : Char}
    (h : c ∈ (encode e bytes).toList) : e.Allowed c := by
  rw [encode, String.toList_ofList] at h
  exact allowed_of_mem_encodeList e h

def encodedLength (e : Encoding) (n : Nat) : Nat :=
  if e.padded then 4 * ((n + 2) / 3) else (4 * n + 2) / 3

theorem length_encodeList (e : Encoding) (bytes : List UInt8) :
    (encodeList e bytes).length = encodedLength e bytes.length := by
  match bytes with
  | [] => cases hp : e.padded <;> simp [encodeList, encodedLength, hp]
  | [_] | [_, _] => cases hp : e.padded <;> simp [encodeList, encodedLength, pad, hp]
  | _ :: _ :: _ :: rest =>
    simp only [encodeList, List.length_cons, length_encodeList e rest, encodedLength]
    split <;> omega

theorem length_encode (e : Encoding) (bytes : ByteArray) :
    (encode e bytes).length = encodedLength e bytes.size := by
  rw [encode, String.length_ofList, length_encodeList, Array.length_toList]; rfl

theorem decode_eq_none_of_not_allowed (e : Encoding) {s : String} {c : Char} (hc : c ∈ s.toList)
    (h : ¬ e.Allowed c) : decode e s = none := by
  cases hd : decode e s with
  | none => rfl
  | some bytes =>
    rw [decode_eq_some_iff] at hd
    subst hd
    exact absurd (allowed_of_mem_encode e bytes hc) h

theorem decode_eq_none_of_length (e : Encoding) {s : String}
    (h : ∀ n, encodedLength e n ≠ s.length) : decode e s = none := by
  cases hd : decode e s with
  | none => rfl
  | some bytes =>
    rw [decode_eq_some_iff] at hd
    exact absurd (hd ▸ length_encode e bytes).symm (h _)

end Lanes.Base64
