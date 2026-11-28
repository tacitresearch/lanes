/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.WebSocket
public import Lanes.Proof.ByteArray

/-!
What `Lanes.WebSocket`'s frames are proved to do: `decode` reads back every frame `encode`
writes, masked or not, whatever follows it, and says how many bytes it took
(`WebSocket.decode_encode`); masking undoes itself (`WebSocket.applyMask_applyMask`).
-/

@[expose] public section

namespace Lanes.WebSocket

/-- A frame `decode` reads back: its payload within the limits and below 2⁶³, and a control
frame whole and at most 125 bytes. -/
def Frame.Valid (l : Limits) (f : Frame) : Prop :=
  f.payload.size ≤ min l.maxPayload l.maxMessage ∧ f.payload.size < 2 ^ 63
    ∧ (f.opcode.control = true → f.fin = true ∧ f.payload.size ≤ 125)

theorem xor_xor (x k : UInt8) : x ^^^ k ^^^ k = x :=
  UInt8.toBitVec_inj.1 (by simp [BitVec.xor_assoc])

theorem applyMask_applyMask (key : Vector UInt8 4) (b : ByteArray) :
    applyMask key (applyMask key b) = b := by
  cases b with
  | mk data =>
    simp only [applyMask, Array.mapIdx_mapIdx, ByteArray.mk.injEq]
    apply Array.ext
    · simp only [Array.size_mapIdx]
    · intro i h1 h2
      simp only [Array.getElem_mapIdx, Function.comp, xor_xor]

theorem size_applyMask (key : Vector UInt8 4) (b : ByteArray) : (applyMask key b).size = b.size := by
  simp only [applyMask, ByteArray.size, Array.size_mapIdx]

theorem ofCode?_code (o : Opcode) : Opcode.ofCode? o.code = some o := by cases o <;> rfl

theorem toNat_byte0 (fin : Bool) (o : Opcode) :
    ((if fin then 128 else 0) + o.code).toUInt8.toNat = (if fin then 128 else 0) + o.code := by
  cases fin <;> cases o <;> decide

theorem code_lt (o : Opcode) : o.code < 16 := by cases o <;> decide

theorem toNat_byte1 (masked : Bool) {len7 : Nat} (h : len7 < 128) :
    ((if masked then 128 else 0) + len7).toUInt8.toNat = (if masked then 128 else 0) + len7 := by
  have : (if masked then 128 else 0) + len7 < 256 := by split <;> omega
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

theorem map_toNat_split {w n : Nat} :
    ((Digits.split 256 w n).map (·.toUInt8)).map (·.toNat) = Digits.split 256 w n := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id (Digits.split 256 w n)]
  apply List.map_congr_left
  intro d hd
  have := Digits.lt_of_mem_split (by decide) hd
  simp only [Function.comp, Nat.toUInt8, UInt8.toNat_ofNat', id]
  omega

/-- What `readLength` reads from the length `lengthBytes` writes, whatever follows. -/
theorem readLength_lengthBytes {n : Nat} (hn : n < 2 ^ 63) (more : List UInt8) :
    readLength (lengthBytes n).1 ((lengthBytes n).2 ++ more) = some (n, (lengthBytes n).2.length) := by
  unfold lengthBytes
  split
  · simp [readLength, *]
  · split
    · have hl : ((Digits.split 256 2 n).map (·.toUInt8)).length = 2 := by simp [Digits.length_split]
      simp only [readLength, show ¬ (126 ≤ 125) by decide, ite_false, ite_true, hl, List.length_append]
      rw [ite_eq_right (by omega), List.take_left' hl, map_toNat_split, Digits.join_split]
      simp only [show n % 256 ^ 2 = n by omega]
    · have hl : ((Digits.split 256 8 n).map (·.toUInt8)).length = 8 := by simp [Digits.length_split]
      simp only [readLength, show ¬ (127 ≤ 125) by decide, ite_false, hl, List.length_append,
        show ¬ ((127 : Nat) = 126) by decide]
      rw [ite_eq_right (by omega), List.take_left' hl, map_toNat_split, Digits.join_split]
      simp only [show n % 256 ^ 8 = n by omega]

theorem len7_lt (n : Nat) : (lengthBytes n).1 < 128 := by
  unfold lengthBytes; split
  · simp; omega
  · split <;> simp

theorem len7_le_125 {n : Nat} : (lengthBytes n).1 ≤ 125 ↔ n ≤ 125 := by
  unfold lengthBytes; split
  · simp_all
  · split <;> simp <;> omega

theorem length_ext_le (n : Nat) : (lengthBytes n).2.length ≤ 8 := by
  unfold lengthBytes; split
  · simp
  · split <;> simp [Digits.length_split]

def maskList (f : Frame) : List UInt8 := (f.mask.map (·.toList)).getD []

def headerSize (f : Frame) : Nat := 2 + (lengthBytes f.payload.size).2.length + (maskList f).length

theorem length_header (f : Frame) : (header f).length = headerSize f := by
  simp [header, headerSize, maskList]
  omega

theorem headerSize_le (f : Frame) : headerSize f ≤ 14 := by
  have := length_ext_le f.payload.size
  unfold headerSize maskList
  cases f.mask <;> simp <;> omega

theorem byte0_mod (fin : Bool) {c : Nat} (hc : c < 16) : ((if fin then 128 else 0) + c) % 16 = c := by
  cases fin <;> simp <;> omega

theorem byte0_div (fin : Bool) {c : Nat} (hc : c < 16) : ((if fin then 128 else 0) + c) / 16 % 8 = 0 := by
  cases fin <;> simp <;> omega

theorem byte0_fin (fin : Bool) {c : Nat} (hc : c < 16) :
    decide ((if fin then 128 else 0) + c ≥ 128) = fin := by
  cases fin <;> simp <;> omega

theorem byte1_mod (m : Bool) {len7 : Nat} (h : len7 < 128) : ((if m then 128 else 0) + len7) % 128 = len7 := by
  cases m <;> simp <;> omega

theorem byte1_masked (m : Bool) {len7 : Nat} (h : len7 < 128) :
    ((if m then 128 else 0) + len7 ≥ 128) ↔ m = true := by
  cases m <;> simp <;> omega

theorem readHeader_header {l : Limits} {f : Frame} (hv : f.Valid l) {masked : Option Bool}
    (hm : masked = none ∨ masked = some f.mask.isSome) (more : List UInt8) :
    readHeader l masked 0 (header f ++ more)
      = some (.ok ⟨f.fin, 0, f.opcode, f.mask, f.payload.size, headerSize f⟩) := by
  obtain ⟨hmax, h63, _⟩ := hv
  have h7 := len7_lt f.payload.size
  have hc := code_lt f.opcode
  have hmask : masked.any (· != decide ((if f.mask.isSome = true then 128 else 0)
      + (lengthBytes f.payload.size).1 ≥ 128)) = false := by
    rcases hm with rfl | rfl
    · rfl
    · cases f.mask.isSome <;> simp <;> omega
  have hrsv : ((if f.fin = true then 128 else 0) + f.opcode.code) / 16 % 8 = 0 := byte0_div _ hc
  have hlim : ¬ f.payload.size > (if f.opcode.control then l.maxPayload else min l.maxPayload (l.maxMessage - 0)) := by
    split <;> simp at hmax ⊢ <;> omega
  simp only [header, List.cons_append, readHeader, toNat_byte0, toNat_byte1 _ h7, byte0_mod _ hc,
    ofCode?_code, ite_false, byte1_mod _ h7, List.append_assoc,
    readLength_lengthBytes h63, hlim, byte1_masked _ h7, List.drop_left,
    byte0_fin _ hc, hrsv]
  have h7' : ¬ (lengthBytes f.payload.size).1 ≥ 128 := by omega
  have h7'' : (128 + (lengthBytes f.payload.size).1 ≥ 128) := by omega
  unfold headerSize maskList
  cases hm : f.mask with
  | none => simp; simpa [hm, h7'] using hmask
  | some key =>
    obtain ⟨⟨l⟩, hl⟩ := key
    match l, hl with
    | [k0, k1, k2, k3], _ => simp; simpa [hm, h7''] using hmask

/-- The payload as it is sent: masked if the frame has a key. -/
def body (f : Frame) : ByteArray := match f.mask with | some k => applyMask k f.payload | none => f.payload

theorem size_body (f : Frame) : (body f).size = f.payload.size := by
  unfold body; split <;> simp [size_applyMask]

theorem encode_eq (f : Frame) : encode f = ⟨(header f).toArray⟩ ++ body f := rfl

theorem size_encode (f : Frame) : (encode f).size = headerSize f + f.payload.size := by
  rw [encode_eq, ByteArray.size_append, size_body, ← length_header]
  rfl

/-- `decode` reads back every frame `encode` writes, whatever follows it, whether or not it is
told the frame must be masked as it is. -/
theorem decode_encode {l : Limits} {f : Frame} (hv : f.Valid l) {masked : Option Bool}
    (hm : masked = none ∨ masked = some f.mask.isSome) (rest : ByteArray) :
    decode l (encode f ++ rest) masked = .frame f (encode f).size := by
  have hs := headerSize_le f
  have hh : ((encode f ++ rest).extract 0 14).data.toList
      = header f ++ (body f ++ rest).data.toList.take (14 - headerSize f) := by
    rw [toList_extract_zero, encode_eq, ByteArray.append_assoc, ByteArray.data_append,
      Array.toList_append, List.take_append, List.take_of_length_le (by rw [length_header]; omega),
      length_header]
  unfold decode
  rw [hh, readHeader_header hv hm]
  simp only
  rw [ite_eq_right (by rw [ByteArray.size_append, size_encode]; omega)]
  have hctl : (decide ((0 : Nat) ≠ 0) || (f.opcode.control && (!f.fin || decide (f.payload.size > 125))))
      = false := by
    cases e : f.opcode.control
    · simp
    · obtain ⟨h1, h2⟩ := hv.2.2 e
      simp [h1]; omega
  rw [ite_eq_right (by simpa using hctl)]
  have hb : (encode f ++ rest).extract (headerSize f) (headerSize f + f.payload.size) = body f := by
    have := extract_append_front ⟨(header f).toArray⟩ (body f) rest
    rw [encode_eq, ByteArray.append_assoc]
    have e : (⟨(header f).toArray⟩ : ByteArray).size = headerSize f := by
      rw [← length_header]; rfl
    rw [e, size_body] at this
    exact this
  rw [hb, size_encode]
  congr 1
  cases f with
  | mk fin opcode mask payload =>
    cases mask with
    | none => rfl
    | some k => simp [body, applyMask_applyMask]

end Lanes.WebSocket
