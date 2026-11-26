/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The bytes of a byte array cut short or put after another, through which the proofs about the
HTTP reader read what it reads.
-/

public section

namespace Lanes

theorem extract_append_front (a b rest : ByteArray) :
    (a ++ (b ++ rest)).extract a.size (a.size + b.size) = b := by
  have := ByteArray.extract_append_size_add (a := a) (b := b ++ rest) (i := 0) (j := b.size)
  rw [Nat.add_zero] at this
  rw [this]
  exact ByteArray.extract_append_eq_left rfl

theorem size_extract_zero (bytes : ByteArray) (n : Nat) :
    (bytes.extract 0 n).size = min n bytes.size := by
  simp [ByteArray.size_extract]

theorem getElem_extract_zero {bytes : ByteArray} {n i : Nat}
    (h : i < (bytes.extract 0 n).size) :
    (bytes.extract 0 n)[i] = bytes[i]'(by rw [size_extract_zero] at h; omega) := by
  simp [ByteArray.getElem_extract]

theorem getElem?_extract_zero (bytes : ByteArray) (n i : Nat) :
    (bytes.extract 0 n)[i]? = if i < n then bytes[i]? else none := by
  by_cases h : i < (bytes.extract 0 n).size
  · have h' := h
    rw [size_extract_zero] at h'
    rw [getElem?_pos (bytes.extract 0 n) i h, getElem_extract_zero h,
      getElem?_pos bytes i (show i < bytes.size by omega)]
    simp only [show i < n by omega, ↓reduceIte]
  · rw [size_extract_zero] at h
    rw [getElem?_neg _ _ (by rw [size_extract_zero]; omega)]
    by_cases hn : i < n
    · simp only [hn, ↓reduceIte]
      rw [getElem?_neg _ _ (by omega)]
    · simp [hn]

theorem toList_extract_zero (bytes : ByteArray) (n : Nat) :
    (bytes.extract 0 n).data.toList = bytes.data.toList.take n := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

theorem extract_extract_zero {bytes : ByteArray} {n i j : Nat} (h : j ≤ n) :
    (bytes.extract 0 n).extract i j = bytes.extract i j := by
  rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add, Nat.min_eq_left h]

theorem getElem?_data (b : ByteArray) (i : Nat) : b[i]? = b.data.toList[i]? := by
  by_cases h : i < b.size
  · rw [getElem?_pos b i h, Array.getElem?_toList, getElem?_pos b.data i h,
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg b i h, Array.getElem?_toList, getElem?_neg b.data i h]

theorem getElem?_append_front (pre bytes : ByteArray) (i : Nat) :
    (pre ++ bytes)[pre.size + i]? = bytes.data.toList[i]? := by
  rw [getElem?_data, ByteArray.data_append, Array.toList_append,
    List.getElem?_append_right (by simp)]
  congr 1
  simp only [Array.length_toList]
  have : pre.data.size = pre.size := rfl
  omega

theorem getElem_of_getElem? {bytes : ByteArray} {q : Nat} {b : UInt8}
    (h : bytes[q]? = some b) : ∃ hq : q < bytes.size, bytes[q] = b := by
  by_cases hq : q < bytes.size
  · rw [getElem?_pos bytes q hq] at h
    exact ⟨hq, Option.some.inj h⟩
  · rw [getElem?_neg bytes q hq] at h
    cases h

theorem foldl_append_bytes (acc : ByteArray) (cs : List ByteArray) :
    cs.foldl (· ++ ·) acc = acc ++ cs.foldl (· ++ ·) .empty := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (.empty ++ c), ByteArray.empty_append,
      ByteArray.append_assoc]

end Lanes
