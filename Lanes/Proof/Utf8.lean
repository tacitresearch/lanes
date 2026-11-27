/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Strings as lists of bytes: what UTF-8 makes of a character below 128, and the bytes of a
string.
-/

public section

namespace Lanes

theorem utf8EncodeChar_ascii {c : Char} {b : UInt8} (hb : b ∈ String.utf8EncodeChar c)
    (h : b.toNat < 128) : b.toNat = c.toNat := by
  simp only [String.utf8EncodeChar] at hb
  split at hb
  · simp only [List.mem_singleton] at hb
    subst hb
    rename_i hv
    rw [UInt8.toNat_ofNat']
    show _ = c.val.toNat
    omega
  · split at hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [UInt8.toNat_ofNat'] at h <;> omega
    · split at hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> simp [UInt8.toNat_ofNat'] at h <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> simp [UInt8.toNat_ofNat'] at h <;> omega

theorem data_toList_toByteArray (s : String) :
    s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [← String.utf8Encode_toList, List.utf8Encode_eq_toByteArray, List.data_toByteArray]

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

theorem toByteArray_inj {s t : String} : s.toByteArray = t.toByteArray ↔ s = t :=
  ⟨fun h => Option.some.inj ((fromUTF8?_toByteArray s).symm.trans
    ((congrArg String.fromUTF8? h).trans (fromUTF8?_toByteArray t))), fun h => h ▸ rfl⟩

theorem length_flatMap_utf8EncodeChar (s : String) :
    (s.toList.flatMap String.utf8EncodeChar).length = s.utf8ByteSize := by
  rw [← data_toList_toByteArray, Array.length_toList]
  rfl

end Lanes
