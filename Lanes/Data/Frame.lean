/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
The framing of a journal file. A frame is one record: its length in four bytes, big-endian, the
FNV-1a checksum of its payload in four bytes, then the payload. A file is frames end to end.
`decode` gives back the payloads of every whole, intact frame from the start, so a file whose
last write was torn loses only the records that were not fully written, and bytes after good
frames never change them. `unfinished` tells a torn write from damage. A checksum makes it unlikely, not impossible, that a damaged frame is
taken for a good one.
-/

@[expose] public section

namespace Lanes.Frame

/-- The length field has four bytes, so only these payloads come back from `decode`. -/
def fits (payload : ByteArray) : Bool :=
  payload.size < 2 ^ 32

theorem fits_iff {payload : ByteArray} : fits payload ↔ payload.size < 2 ^ 32 := by
  simp [fits]

theorem all_fits_iff {payloads : List ByteArray} :
    payloads.all fits ↔ ∀ p ∈ payloads, p.size < 2 ^ 32 := by
  simp [fits]

/-- FNV-1a, 32 bits. -/
def checksum (payload : ByteArray) : UInt32 :=
  payload.foldl (fun hash byte => (hash ^^^ byte.toUInt32) * 16777619) 2166136261

private def u32 (n : Nat) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

private def u32At (bytes : ByteArray) (pos : Nat) (h : pos + 4 ≤ bytes.size) : Nat :=
  bytes[pos].toNat <<< 24 + bytes[pos + 1].toNat <<< 16 + bytes[pos + 2].toNat <<< 8
    + bytes[pos + 3].toNat

/-- A frame that claims `sum` as the checksum of `payload`. -/
@[no_expose] def stamped (sum : UInt32) (payload : ByteArray) : ByteArray :=
  u32 payload.size ++ u32 sum.toNat ++ payload

def one (payload : ByteArray) : ByteArray :=
  stamped (checksum payload) payload

def encode (payloads : List ByteArray) : ByteArray :=
  payloads.foldl (· ++ one ·) .empty

@[simp] private theorem size_u32 (n : Nat) : (u32 n).size = 4 := rfl

private theorem u32At_u32 {n : Nat} (rest : ByteArray) (h : n < 2 ^ 32) :
    u32At (u32 n ++ rest) 0 (by simp) = n := by
  simp only [u32At, Nat.zero_add]
  simp [u32, ByteArray.getElem_eq_getElem_data, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

private theorem u32At_append_right {a b : ByteArray} {pos : Nat}
    (h : a.size + pos + 4 ≤ (a ++ b).size) :
    u32At (a ++ b) (a.size + pos) h = u32At b pos (by simp at h; omega) := by
  simp [u32At, ByteArray.getElem_append_right, Nat.add_assoc]

private theorem u32At_extract {bytes : ByteArray} {n pos : Nat}
    (h : pos + 4 ≤ (bytes.extract 0 n).size) :
    u32At (bytes.extract 0 n) pos h = u32At bytes pos (by simp at h; omega) := by
  simp [u32At, ByteArray.getElem_extract]

@[simp] theorem size_stamped (sum : UInt32) (payload : ByteArray) :
    (stamped sum payload).size = 8 + payload.size := by
  simp [stamped]

@[simp] theorem size_one (payload : ByteArray) : (one payload).size = 8 + payload.size :=
  size_stamped ..

private theorem foldl_one (acc : ByteArray) (payloads : List ByteArray) :
    payloads.foldl (· ++ one ·) acc = acc ++ encode payloads := by
  unfold encode
  induction payloads generalizing acc with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (.empty ++ one p), ByteArray.empty_append,
      ByteArray.append_assoc]

@[simp] theorem encode_nil : encode [] = .empty := rfl

@[simp] theorem encode_cons (p : ByteArray) (ps : List ByteArray) :
    encode (p :: ps) = one p ++ encode ps := by
  rw [encode, List.foldl_cons, foldl_one, ByteArray.empty_append]

theorem encode_append (a b : List ByteArray) : encode (a ++ b) = encode a ++ encode b := by
  rw [encode, List.foldl_append, foldl_one]
  rfl

/-- The payload of the frame that starts at `pos`, if it is whole and intact. -/
private def frameAt (bytes : ByteArray) (pos : Nat) : Option ByteArray :=
  if h : pos + 8 ≤ bytes.size then
    let stop := pos + 8 + u32At bytes pos (by omega)
    if stop ≤ bytes.size then
      let payload := bytes.extract (pos + 8) stop
      if u32At bytes (pos + 4) (by omega) = (checksum payload).toNat then some payload else none
    else none
  else none

private theorem frameAt_eq_some_iff {bytes : ByteArray} {pos : Nat} {payload : ByteArray} :
    frameAt bytes pos = some payload ↔
      ∃ h : pos + 8 + payload.size ≤ bytes.size,
        u32At bytes pos (by omega) = payload.size
          ∧ u32At bytes (pos + 4) (by omega) = (checksum payload).toNat
          ∧ bytes.extract (pos + 8) (pos + 8 + payload.size) = payload := by
  unfold frameAt
  constructor
  · intro h
    split at h
    · simp only at h
      split at h
      · split at h
        · cases h
          rename_i h8 hstop hsum
          have hsize : (bytes.extract (pos + 8) (pos + 8 + u32At bytes pos (by omega))).size
              = u32At bytes pos (by omega) := by
            rw [ByteArray.size_extract]
            omega
          exact ⟨by omega, hsize.symm, hsum, by rw [hsize]⟩
        · cases h
      · cases h
    · cases h
  · rintro ⟨h, hsize, hsum, hpayload⟩
    have h8 : pos + 8 ≤ bytes.size := by omega
    simp only [h8, ↓reduceDIte, hsize, h, ↓reduceIte, hpayload, hsum]

private theorem frameAt_size {bytes : ByteArray} {pos : Nat} {payload : ByteArray}
    (h : frameAt bytes pos = some payload) : pos + 8 + payload.size ≤ bytes.size :=
  (frameAt_eq_some_iff.mp h).1

private theorem frameAt_append_right (a b : ByteArray) (pos : Nat) :
    frameAt (a ++ b) (a.size + pos) = frameAt b pos := by
  ext payload
  simp only [frameAt_eq_some_iff, ByteArray.size_append, Nat.add_assoc, u32At_append_right,
    ByteArray.extract_append_size_add, Nat.add_le_add_iff_left]

private theorem frameAt_header {size sum : Nat} {tail payload : ByteArray} (hsize : size < 2 ^ 32)
    (hsum : sum < 2 ^ 32) :
    frameAt (u32 size ++ (u32 sum ++ tail)) 0 = some payload
      ↔ size = payload.size ∧ sum = (checksum payload).toNat
        ∧ tail.extract 0 payload.size = payload := by
  have h0 : ∀ h, u32At (u32 size ++ (u32 sum ++ tail)) 0 h = size := fun _ => u32At_u32 _ hsize
  have h4 : ∀ h, u32At (u32 size ++ (u32 sum ++ tail)) 4 h = sum := fun h =>
    (u32At_append_right (a := u32 size) (pos := 0) h).trans (u32At_u32 _ hsum)
  have h8 : ∀ k, (u32 size ++ (u32 sum ++ tail)).extract 8 (8 + k) = tail.extract 0 k := by
    intro k
    rw [← ByteArray.append_assoc]
    exact ByteArray.extract_append_size_add' (i := 0) rfl
  simp only [frameAt_eq_some_iff, Nat.zero_add, h0, h4, h8]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2, h3⟩
    have := congrArg ByteArray.size h3
    rw [ByteArray.size_extract] at this
    exact ⟨by simp; omega, h1, h2, h3⟩

private theorem frameAt_stamped {payload : ByteArray} (sum : UInt32) (rest : ByteArray)
    (h : payload.size < 2 ^ 32) :
    frameAt (stamped sum payload ++ rest) 0
      = if sum = checksum payload then some payload else none := by
  have shape : stamped sum payload ++ rest
      = u32 payload.size ++ (u32 sum.toNat ++ (payload ++ rest)) := by
    simp [stamped, ByteArray.append_assoc]
  rw [shape]
  ext q
  rw [frameAt_header h sum.toNat_lt]
  constructor
  · rintro ⟨hsize, hsum, hq⟩
    have : q = payload := by
      rw [← hq, ← hsize]
      exact ByteArray.extract_append_eq_left rfl
    subst this
    simp [UInt32.toNat_inj.mp hsum]
  · intro hq
    split at hq
    · cases hq
      rename_i hs
      exact ⟨rfl, by rw [hs], ByteArray.extract_append_eq_left rfl⟩
    · cases hq

private theorem frameAt_extract {bytes : ByteArray} {n pos : Nat} {payload : ByteArray} :
    frameAt (bytes.extract 0 n) pos = some payload
      ↔ frameAt bytes pos = some payload ∧ pos + 8 + payload.size ≤ n := by
  simp only [frameAt_eq_some_iff, u32At_extract, ByteArray.extract_extract,
    ByteArray.size_extract, Nat.zero_add, Nat.sub_zero]
  constructor
  · rintro ⟨h, hsize, hsum, hpayload⟩
    have hn : pos + 8 + payload.size ≤ n := by omega
    rw [Nat.min_eq_left hn] at hpayload
    exact ⟨⟨by omega, hsize, hsum, hpayload⟩, hn⟩
  · rintro ⟨⟨h, hsize, hsum, hpayload⟩, hn⟩
    exact ⟨by omega, hsize, hsum, by rw [Nat.min_eq_left hn]; exact hpayload⟩

private theorem frameAt_extract_eq_none {bytes : ByteArray} {n pos : Nat}
    (h : frameAt bytes pos = none
      ∨ ∀ payload, frameAt bytes pos = some payload → n < pos + 8 + payload.size) :
    frameAt (bytes.extract 0 n) pos = none := by
  refine Option.eq_none_iff_forall_ne_some.mpr fun q hq => ?_
  have ⟨hq, hn⟩ := frameAt_extract.mp hq
  cases h with
  | inl h => simp [h] at hq
  | inr h => exact absurd hn (Nat.not_le.mpr (h q hq))

theorem extract_of_size_le {bytes : ByteArray} {n : Nat} (h : bytes.size ≤ n) :
    bytes.extract 0 n = bytes := by
  rw [← Nat.max_eq_left h, ByteArray.extract_zero_max_size]

private def decodeFrom (bytes : ByteArray) (pos : Nat) (acc : Array ByteArray) : Array ByteArray :=
  match h : frameAt bytes pos with
  | none => acc
  | some payload => decodeFrom bytes (pos + 8 + payload.size) (acc.push payload)
termination_by bytes.size - pos
decreasing_by have := frameAt_size h; omega

@[no_expose] def decode (bytes : ByteArray) : List ByteArray :=
  (decodeFrom bytes 0 #[]).toList

private theorem decodeFrom_none {bytes : ByteArray} {pos : Nat} (acc : Array ByteArray)
    (h : frameAt bytes pos = none) : decodeFrom bytes pos acc = acc := by
  rw [decodeFrom]
  split <;> simp_all

private theorem decodeFrom_some {bytes : ByteArray} {pos : Nat} {payload : ByteArray}
    (acc : Array ByteArray) (h : frameAt bytes pos = some payload) :
    decodeFrom bytes pos acc = decodeFrom bytes (pos + 8 + payload.size) (acc.push payload) := by
  rw [decodeFrom]
  split <;> simp_all

private theorem decodeFrom_acc (bytes : ByteArray) (pos : Nat) (acc : Array ByteArray) :
    decodeFrom bytes pos acc = acc ++ decodeFrom bytes pos #[] := by
  suffices ∀ acc', decodeFrom bytes pos acc' = acc' ++ decodeFrom bytes pos #[] from this acc
  fun_induction decodeFrom bytes pos acc with
  | case1 pos acc h => simp [decodeFrom_none _ h]
  | case2 pos acc payload h ih =>
    intro acc'
    rw [decodeFrom_some _ h, decodeFrom_some _ h, ih, ih (#[].push payload)]
    simp

private theorem decodeFrom_append_right (a b : ByteArray) (pos : Nat) (acc : Array ByteArray) :
    decodeFrom (a ++ b) (a.size + pos) acc = decodeFrom b pos acc := by
  fun_induction decodeFrom b pos acc with
  | case1 pos acc h => rw [decodeFrom_none _ ((frameAt_append_right ..).trans h)]
  | case2 pos acc payload h ih =>
    rw [decodeFrom_some _ ((frameAt_append_right ..).trans h), ← ih]
    simp only [Nat.add_assoc]

private theorem decode_of_none {bytes : ByteArray} (h : frameAt bytes 0 = none) :
    decode bytes = [] := by
  simp [decode, decodeFrom_none _ h]

private theorem decode_of_some {bytes payload : ByteArray} (h : frameAt bytes 0 = some payload) :
    decode bytes = payload :: (decodeFrom bytes (8 + payload.size) #[]).toList := by
  rw [decode, decodeFrom_some _ h, decodeFrom_acc]
  simp

@[simp] theorem decode_empty : decode .empty = [] :=
  decode_of_none (by simp [frameAt])

theorem decode_stamped_append {payload : ByteArray} (sum : UInt32) (rest : ByteArray)
    (h : payload.size < 2 ^ 32) :
    decode (stamped sum payload ++ rest)
      = if sum = checksum payload then payload :: decode rest else [] := by
  split
  · rename_i hs
    rw [decode_of_some (payload := payload) (by simp [frameAt_stamped _ _ h, hs])]
    have := decodeFrom_append_right (stamped sum payload) rest 0 #[]
    simp only [size_stamped, Nat.add_zero] at this
    rw [this, decode]
  · rename_i hs
    exact decode_of_none (by simp [frameAt_stamped _ _ h, hs])

theorem decode_one_append {payload : ByteArray} (rest : ByteArray) (h : payload.size < 2 ^ 32) :
    decode (one payload ++ rest) = payload :: decode rest := by
  simp [one, decode_stamped_append _ _ h]

theorem decode_encode_append {payloads : List ByteArray} (rest : ByteArray)
    (h : ∀ p ∈ payloads, p.size < 2 ^ 32) :
    decode (encode payloads ++ rest) = payloads ++ decode rest := by
  induction payloads with
  | nil => simp
  | cons p ps ih =>
    rw [encode_cons, ByteArray.append_assoc, decode_one_append _ (h p (by simp)),
      ih fun q hq => h q (by simp [hq])]
    rfl

theorem decode_encode {payloads : List ByteArray} (h : ∀ p ∈ payloads, p.size < 2 ^ 32) :
    decode (encode payloads) = payloads := by
  simpa using decode_encode_append .empty h

theorem decode_one {payload : ByteArray} (h : fits payload) : decode (one payload) = [payload] := by
  simpa using decode_one_append .empty (fits_iff.mp h)

theorem prefix_decode_encode_append {payloads : List ByteArray} (junk : ByteArray)
    (h : ∀ p ∈ payloads, p.size < 2 ^ 32) : payloads <+: decode (encode payloads ++ junk) := by
  simp [decode_encode_append junk h]

theorem decode_checksum_ne {payloads : List ByteArray} {payload : ByteArray} {sum : UInt32}
    (rest : ByteArray) (h : ∀ p ∈ payloads, p.size < 2 ^ 32) (hfits : payload.size < 2 ^ 32)
    (hsum : sum ≠ checksum payload) :
    decode (encode payloads ++ stamped sum payload ++ rest) = payloads := by
  simp [ByteArray.append_assoc, decode_encode_append _ h, decode_stamped_append _ _ hfits, hsum]

theorem decode_extract_prefix (bytes : ByteArray) (n : Nat) :
    decode (bytes.extract 0 n) <+: decode bytes := by
  suffices ∀ pos acc, (decodeFrom (bytes.extract 0 n) pos acc).toList
      <+: (decodeFrom bytes pos acc).toList from this 0 #[]
  intro pos acc
  fun_induction decodeFrom bytes pos acc with
  | case1 pos acc h => simp [decodeFrom_none acc (frameAt_extract_eq_none (.inl h))]
  | case2 pos acc payload h ih =>
    by_cases hn : pos + 8 + payload.size ≤ n
    · rw [decodeFrom_some acc (frameAt_extract.mpr ⟨h, hn⟩)]
      exact ih
    · rw [decodeFrom_none acc (frameAt_extract_eq_none (.inr fun q hq => by simp_all)),
        decodeFrom_acc]
      simp

/-- How many of the frames of `payloads`, counted from the first, end within `n` bytes. -/
def whole : List ByteArray → Nat → Nat
  | [], _ => 0
  | p :: ps, n => if 8 + p.size ≤ n then whole ps (n - (8 + p.size)) + 1 else 0

theorem le_whole_iff {payloads : List ByteArray} {k : Nat} (n : Nat) (hk : k ≤ payloads.length) :
    k ≤ whole payloads n ↔ (encode (payloads.take k)).size ≤ n := by
  induction payloads generalizing k n with
  | nil => simp_all [whole]
  | cons p ps ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.take_succ_cons, encode_cons, ByteArray.size_append, size_one, whole]
      split
      · rw [Nat.add_le_add_iff_right, ih _ (by simpa using hk)]
        omega
      · omega

theorem decode_take_eq {payloads : List ByteArray} (h : ∀ p ∈ payloads, p.size < 2 ^ 32)
    (n : Nat) : decode ((encode payloads).extract 0 n) = payloads.take (whole payloads n) := by
  induction payloads generalizing n with
  | nil => simp [whole, extract_of_size_le]
  | cons p ps ih =>
    have hp := h p (by simp)
    rw [encode_cons, whole]
    split
    · rename_i hn
      rw [ByteArray.extract_append, extract_of_size_le (by simpa using hn), size_one,
        Nat.zero_sub, decode_one_append _ hp, ih fun q hq => h q (by simp [hq]),
        List.take_succ_cons]
    · rename_i hn
      refine decode_of_none (frameAt_extract_eq_none (.inr fun q hq => ?_))
      simp only [one, frameAt_stamped _ _ hp, ↓reduceIte, Option.some.injEq] at hq
      subst hq
      omega

theorem decode_take {payloads : List ByteArray} (h : ∀ p ∈ payloads, p.size < 2 ^ 32) (n : Nat) :
    decode ((encode payloads).extract 0 n) <+: payloads :=
  decode_take_eq h n ▸ List.take_prefix ..

/-- The bytes that `payloads` take up as frames. -/
def span (payloads : List ByteArray) : Nat :=
  (payloads.map (8 + ·.size)).sum

theorem size_encode (payloads : List ByteArray) : (encode payloads).size = span payloads := by
  induction payloads with
  | nil => rfl
  | cons p ps ih =>
    rw [encode_cons, ByteArray.size_append, size_one, ih]
    simp [span]

theorem whole_append (a b : List ByteArray) (n : Nat) :
    whole (a ++ b) (span a + n) = a.length + whole b n := by
  induction a with
  | nil => simp [span]
  | cons p ps ih =>
    have hspan : span (p :: ps) + n = 8 + p.size + (span ps + n) := by
      simp [span]
      omega
    have hle : 8 + p.size ≤ 8 + p.size + (span ps + n) := Nat.le_add_right ..
    simp only [List.cons_append, whole, hspan, hle, ↓reduceIte, Nat.add_sub_cancel_left, ih,
      List.length_cons]
    omega

theorem span_take_whole_le (payloads : List ByteArray) (n : Nat) :
    span (payloads.take (whole payloads n)) ≤ n := by
  induction payloads generalizing n with
  | nil => simp [span]
  | cons p ps ih =>
    rw [whole]
    split
    · have := ih (n - (8 + p.size))
      simp only [List.take_succ_cons, span, List.map_cons, List.sum_cons] at this ⊢
      omega
    · simp [span]

/-- The frames that end within `n` bytes are what a file cut there is cut back to. -/
theorem extract_take_whole (payloads : List ByteArray) (n : Nat) :
    ((encode payloads).extract 0 n).extract 0 (span (payloads.take (whole payloads n)))
      = encode (payloads.take (whole payloads n)) := by
  have hle := span_take_whole_le payloads n
  generalize whole payloads n = k at hle ⊢
  have hsplit : encode payloads = encode (payloads.take k) ++ encode (payloads.drop k) := by
    rw [← encode_append, List.take_append_drop]
  rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add, Nat.min_eq_left hle, hsplit]
  exact ByteArray.extract_append_eq_left (size_encode _).symm

/-- Whether what stands at `pos` is nothing, or the start of a frame that was not written to its
end. A file that was only appended to and then cut ends so (`unfinished_take`); a frame that is
all there and does not check is damage, and is not this. -/
@[no_expose] def unfinished (bytes : ByteArray) (pos : Nat) : Bool :=
  if h : pos + 8 ≤ bytes.size then bytes.size < pos + 8 + u32At bytes pos (by omega) else true

theorem unfinished_of_size_le {bytes : ByteArray} {pos : Nat} (h : bytes.size ≤ pos) :
    unfinished bytes pos = true := by
  unfold unfinished
  split
  · omega
  · rfl

private theorem unfinished_append_right (a b : ByteArray) (pos : Nat) :
    unfinished (a ++ b) (a.size + pos) = unfinished b pos := by
  unfold unfinished
  have hiff : a.size + pos + 8 ≤ (a ++ b).size ↔ pos + 8 ≤ b.size := by
    rw [ByteArray.size_append]
    omega
  have hs : (a ++ b).size = a.size + b.size := ByteArray.size_append
  by_cases h : pos + 8 ≤ b.size
  · have h' := hiff.mpr h
    simp only [h, h', ↓reduceDIte, u32At_append_right, decide_eq_decide]
    omega
  · have h' := mt hiff.mp h
    simp only [h, h', ↓reduceDIte]

theorem unfinished_take {payloads : List ByteArray} (h : ∀ p ∈ payloads, p.size < 2 ^ 32)
    (n : Nat) :
    unfinished ((encode payloads).extract 0 n) (span (payloads.take (whole payloads n)))
      = true := by
  induction payloads generalizing n with
  | nil => simp [whole, span, unfinished]
  | cons p ps ih =>
    have hp := h p (by simp)
    rw [encode_cons, whole]
    split
    · rename_i hn
      rw [ByteArray.extract_append, extract_of_size_le (by simpa using hn), size_one,
        Nat.zero_sub, List.take_succ_cons]
      have hspan : span (p :: ps.take (whole ps (n - (8 + p.size))))
          = (one p).size + span (ps.take (whole ps (n - (8 + p.size)))) := by
        simp [span]
      rw [hspan, unfinished_append_right]
      exact ih (fun q hq => h q (by simp [hq])) _
    · rename_i hn
      unfold unfinished
      split
      · rename_i h8
        have hsize : ∀ h', u32At (one p ++ encode ps) 0 h' = p.size := fun _ => by
          have shape : one p ++ encode ps
              = u32 p.size ++ (u32 (checksum p).toNat ++ (p ++ encode ps)) := by
            simp [one, stamped, ByteArray.append_assoc]
          simp only [shape]
          exact u32At_u32 _ hp
        simp only [List.take_zero, span, List.map_nil, List.sum_nil, Nat.zero_add, u32At_extract,
          hsize, ByteArray.size_extract, decide_eq_true_eq]
        omega
      · rfl

end Lanes.Frame
