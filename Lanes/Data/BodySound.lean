/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Body
public import Lanes.Proof.ByteArray

/-!
The body reads back what it writes (`Body.read_write`), and what reads is what the writer writes
for the value read (`Body.write_read`), for every schema, value and limits: a value has one body.
Each reader is proved with the writer it mirrors (`readAt_writeAt`, `writeAt_readAt`), from any
bytes before the value and after it.
-/

@[expose] public section

namespace Lanes.Body

open Codec (Limits Error)

theorem push_eq_append (acc : ByteArray) (b : UInt8) : acc.push b = acc ++ [b].toByteArray :=
  ByteArray.append_toByteArray_singleton.symm

theorem getElem?_push_append (acc rest : ByteArray) (b : UInt8) :
    (acc.push b ++ rest)[acc.size]? = some b := by
  rw [push_eq_append, ByteArray.append_assoc]
  have := getElem?_append_front acc ([b].toByteArray ++ rest) 0
  rw [Nat.add_zero] at this
  rw [this]
  simp [List.data_toByteArray]

theorem writeNat_lt {acc : ByteArray} {n : Nat} (h : n < 128) :
    writeNat acc n = acc.push n.toUInt8 := by
  rw [writeNat]; simp [h]

theorem writeNat_ge {acc : ByteArray} {n : Nat} (h : ¬n < 128) :
    writeNat acc n = writeNat (acc.push (n % 128 + 128).toUInt8) (n / 128) := by
  rw [writeNat]; simp [h]

theorem natBytes_lt {n : Nat} (h : n < 128) : natBytes n = 1 := by
  rw [natBytes]; simp [h]

theorem natBytes_ge {n : Nat} (h : ¬n < 128) : natBytes n = natBytes (n / 128) + 1 := by
  rw [natBytes]; simp [h]

theorem writeNat_eq (acc : ByteArray) (n : Nat) : writeNat acc n = acc ++ writeNat .empty n := by
  by_cases h : n < 128
  · rw [writeNat_lt h, writeNat_lt h, push_eq_append, push_eq_append, ByteArray.empty_append]
  · rw [writeNat_ge h, writeNat_ge h, writeNat_eq _ (n / 128), writeNat_eq (ByteArray.empty.push _),
      push_eq_append, push_eq_append, ByteArray.empty_append, ByteArray.append_assoc]
termination_by n
decreasing_by all_goals omega

theorem size_writeNat (acc : ByteArray) (n : Nat) :
    (writeNat acc n).size = acc.size + natBytes n := by
  induction acc, n using writeNat.induct with
  | case1 acc n h => rw [writeNat_lt h, natBytes_lt h, ByteArray.size_push]
  | case2 acc n h ih =>
    rw [writeNat_ge h, natBytes_ge h, ih, ByteArray.size_push]
    omega

theorem readNatFrom_writeNat (acc rest : ByteArray) (n start bound budget : Nat) (first : Bool)
    (hb : natBytes n ≤ budget) (hf : first = true ∨ 0 < n) :
    readNatFrom (writeNat acc n ++ rest) start bound budget acc.size first
      = .ok (n, (writeNat acc n).size) := by
  induction acc, n using writeNat.induct generalizing budget first with
  | case1 acc n h =>
    obtain ⟨budget, rfl⟩ : ∃ k, budget = k + 1 := ⟨budget - 1, by rw [natBytes_lt h] at hb; omega⟩
    have hn : n.toUInt8.toNat = n := by simp; omega
    rw [writeNat_lt h, readNatFrom, getElem?_push_append]
    have hlt : n.toUInt8 < 128 := by rw [UInt8.lt_iff_toNat_lt, hn]; simp; omega
    have hpad : ¬(n.toUInt8 = 0 ∧ first = false) := by
      rintro ⟨h0, rfl⟩
      have := congrArg UInt8.toNat h0
      rw [hn] at this
      simp at this hf
      omega
    simp only [hlt, ↓reduceIte, hpad, hn, ByteArray.size_push]
  | case2 acc n h ih =>
    obtain ⟨budget, rfl⟩ : ∃ k, budget = k + 1 :=
      ⟨budget - 1, by rw [natBytes_ge h] at hb; omega⟩
    have hbyte : (n % 128 + 128).toUInt8.toNat = n % 128 + 128 := by simp; omega
    rw [writeNat_ge h, writeNat_eq, ByteArray.append_assoc, readNatFrom,
      getElem?_push_append, ← ByteArray.append_assoc, ← writeNat_eq]
    have hge : ¬(n % 128 + 128).toUInt8 < 128 := by
      rw [UInt8.lt_iff_toNat_lt, hbyte]; simp
    have hrest := ih budget false
      (by rw [natBytes_ge h] at hb; omega) (Or.inr (by omega))
    rw [ByteArray.size_push] at hrest
    simp only [hge, ↓reduceIte, hrest, hbyte]
    congr 2
    omega

variable {L : Limits}

@[simp] theorem within_eq_ok {α : Type} {step : Error.Step} {x : Except Error α} {a : α} :
    within step x = .ok a ↔ x = .ok a := by
  cases x <;> simp [within]

theorem writeNum_ok {acc out : ByteArray} {n : Nat} (h : writeNum L acc n = .ok out) :
    out = writeNat acc n ∧ natBytes n ≤ L.maxNumberBytes := by
  unfold writeNum at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem readNat_writeNat (acc rest : ByteArray) {n : Nat} (h : natBytes n ≤ L.maxNumberBytes) :
    readNat L (writeNat acc n ++ rest) acc.size = .ok (n, (writeNat acc n).size) :=
  readNatFrom_writeNat acc rest n _ _ _ true h (.inl rfl)

theorem readNat_writeNum {acc out : ByteArray} {n : Nat} (rest : ByteArray)
    (h : writeNum L acc n = .ok out) : readNat L (out ++ rest) acc.size = .ok (n, out.size) := by
  obtain ⟨rfl, hn⟩ := writeNum_ok h
  exact readNat_writeNat acc rest hn

theorem writeNum_extends {acc out : ByteArray} {n : Nat} (h : writeNum L acc n = .ok out) :
    ∃ e, out = acc ++ e ∧ 0 < e.size := by
  obtain ⟨rfl, _⟩ := writeNum_ok h
  refine ⟨_, writeNat_eq acc n, ?_⟩
  have := size_writeNat .empty n
  rw [natBytes] at this
  split at this <;> simp_all <;> omega

theorem writeBlob_ok {acc out blob : ByteArray} (h : writeBlob L acc blob = .ok out) :
    ∃ w, writeNum L acc blob.size = .ok w ∧ out = w ++ blob ∧ blob.size ≤ L.maxLength := by
  unfold writeBlob at h
  split at h
  · cases hw : writeNum L acc blob.size with
    | error e => rw [hw] at h; cases h
    | ok w => rw [hw] at h; cases h; exact ⟨w, rfl, rfl, by assumption⟩
  · cases h

theorem readBlob_writeBlob {acc out blob : ByteArray} (rest : ByteArray)
    (h : writeBlob L acc blob = .ok out) :
    readBlob L (out ++ rest) acc.size = .ok (blob, out.size) := by
  obtain ⟨w, hw, rfl, hl⟩ := writeBlob_ok h
  unfold readBlob
  rw [ByteArray.append_assoc, readNat_writeNum _ hw]
  have hsize : ¬w.size + (blob.size + rest.size) - w.size < blob.size := by omega
  simp only [Nat.not_lt.mpr hl, ↓reduceIte, extract_append_front, ByteArray.size_append, hsize]

theorem writeBlob_extends {acc out blob : ByteArray} (h : writeBlob L acc blob = .ok out) :
    ∃ e, out = acc ++ e ∧ 0 < e.size := by
  obtain ⟨w, hw, rfl, _⟩ := writeBlob_ok h
  obtain ⟨e, rfl, he⟩ := writeNum_extends hw
  exact ⟨e ++ blob, ByteArray.append_assoc, by simp only [ByteArray.size_append]; omega⟩

theorem writeCount_ok {acc out : ByteArray} {n : Nat} (h : writeCount L acc n = .ok out) :
    writeNum L acc n = .ok out ∧ n ≤ L.maxItems := by
  unfold writeCount at h
  split at h
  · exact ⟨h, by assumption⟩
  · cases h

theorem readCount_writeCount {acc out : ByteArray} {n : Nat} {consumes : Bool} (rest : ByteArray)
    (h : writeCount L acc n = .ok out) (hn : consumes = true → n ≤ rest.size) :
    readCount L (out ++ rest) consumes acc.size = .ok (n, out.size) := by
  obtain ⟨hw, hl⟩ := writeCount_ok h
  unfold readCount
  rw [readNat_writeNum _ hw]
  have hleft : ¬(consumes = true ∧ (out ++ rest).size - out.size < n) := by
    rintro ⟨hne, hlt⟩
    have := hn hne
    simp only [ByteArray.size_append] at hlt
    omega
  simp only [Nat.not_lt.mpr hl, hleft, ↓reduceIte]


theorem unzigzag_zigzag (i : Int) : unzigzag (zigzag i) = i := by
  unfold zigzag unzigzag
  split <;> split <;> omega

theorem extends_trans {a b c : ByteArray} :
    (∃ e, b = a ++ e) → (∃ e, c = b ++ e) → ∃ e, c = a ++ e
  | ⟨e, he⟩, ⟨f, hf⟩ => ⟨e ++ f, by rw [hf, he, ByteArray.append_assoc]⟩

theorem size_le_of_extends {a b : ByteArray} : (∃ e, b = a ++ e) → a.size ≤ b.size
  | ⟨e, he⟩ => by rw [he, ByteArray.size_append]; omega

theorem tags_distinct : Tag.int ≠ Tag.nat ∧ Tag.string ≠ Tag.nat ∧ Tag.string ≠ Tag.int ∧
    Tag.bytes ≠ Tag.nat ∧ Tag.bytes ≠ Tag.int ∧ Tag.bytes ≠ Tag.string ∧ Tag.list ≠ Tag.nat ∧
    Tag.list ≠ Tag.int ∧ Tag.list ≠ Tag.string ∧ Tag.list ≠ Tag.bytes ∧ Tag.ctor ≠ Tag.nat ∧
    Tag.ctor ≠ Tag.int ∧ Tag.ctor ≠ Tag.string ∧ Tag.ctor ≠ Tag.bytes ∧ Tag.ctor ≠ Tag.list := by
  decide

theorem pushed {acc out : ByteArray} {t : UInt8} : (∃ e, out = acc.push t ++ e) →
    ∃ e, out = acc ++ e
  | ⟨e, he⟩ => ⟨[t].toByteArray ++ e, by rw [he, push_eq_append, ByteArray.append_assoc]⟩

theorem tag_at {acc out rest : ByteArray} {t : UInt8} (h : ∃ e, out = acc.push t ++ e) :
    (out ++ rest)[acc.size]? = some t := by
  obtain ⟨e, rfl⟩ := h
  rw [ByteArray.append_assoc]
  exact getElem?_push_append acc _ t

mutual

theorem readAt_writeAt (d : Nat) (s : Schema) (v : Value) (acc out rest : ByteArray)
    (h : writeAt L d s v acc = .ok out) :
    (∃ e, out = acc ++ e) ∧ (consumes s = true → acc.size < out.size) ∧
      readAt L (out ++ rest) d s acc.size = .ok (v, out.size) := by
  rw [writeAt.eq_def] at h
  split at h
  · obtain ⟨e, rfl, he⟩ := writeNum_extends h
    refine ⟨⟨e, rfl⟩, fun _ => by simp only [ByteArray.size_append]; omega, ?_⟩
    simp only [readAt, readNat_writeNum rest h]
  · obtain ⟨e, rfl, he⟩ := writeNum_extends h
    refine ⟨⟨e, rfl⟩, fun _ => by simp only [ByteArray.size_append]; omega, ?_⟩
    simp only [readAt, readNat_writeNum rest h, unzigzag_zigzag]
  · obtain ⟨e, rfl, he⟩ := writeBlob_extends h
    refine ⟨⟨e, rfl⟩, fun _ => by simp only [ByteArray.size_append]; omega, ?_⟩
    simp only [readAt, readBlob_writeBlob rest h, Codec.fromUTF8?_toUTF8]
  · obtain ⟨e, rfl, he⟩ := writeBlob_extends h
    refine ⟨⟨e, rfl⟩, fun _ => by simp only [ByteArray.size_append]; omega, ?_⟩
    simp only [readAt, readBlob_writeBlob rest h]
  · cases h
    exact ⟨⟨.empty, ByteArray.append_empty.symm⟩, by simp [consumes], by simp only [readAt]⟩
  all_goals try (simp [fail] at h; done)
  · split at h
    · rename_i acc1 hc
      obtain ⟨⟨e2, rfl⟩, hn, hr⟩ := readItems_writeItems _ _ _ _ _ _ rest h
      obtain ⟨e1, he1, hpos⟩ := writeNum_extends (writeCount_ok hc).1
      have hcount := readCount_writeCount (consumes := consumes _) (e2 ++ rest) hc fun hne => by
        have := hn hne
        simp only [ByteArray.size_append] at this ⊢
        omega
      rw [← ByteArray.append_assoc] at hcount
      refine ⟨extends_trans ⟨e1, he1⟩ ⟨e2, rfl⟩, fun _ => ?_, by simp only [readAt, hcount, hr]⟩
      simp only [he1, ByteArray.size_append]
      omega
    · cases h
  · split at h
    · rename_i acc1 hc
      obtain ⟨⟨e2, rfl⟩, hn, hr⟩ := readEntries_writeEntries _ _ _ _ _ _ _ rest h
      obtain ⟨e1, he1, hpos⟩ := writeNum_extends (writeCount_ok hc).1
      have hcount := readCount_writeCount (consumes := consumes _ || consumes _) (e2 ++ rest) hc
        fun hne => by
          have := hn hne
          simp only [ByteArray.size_append] at this ⊢
          omega
      rw [← ByteArray.append_assoc] at hcount
      refine ⟨extends_trans ⟨e1, he1⟩ ⟨e2, rfl⟩, fun _ => ?_, by simp only [readAt, hcount, hr]⟩
      simp only [he1, ByteArray.size_append]
      omega
    · cases h
  · rw [within_eq_ok] at h
    obtain ⟨hext, hn, hr⟩ := readFields_writeFields _ _ _ _ _ rest h
    exact ⟨hext, by simpa [consumes] using hn, by simp only [readAt, hr, within_ok]⟩
  · split at h
    · simp [fail] at h
    · rename_i c hc
      split at h
      · rename_i acc1 hw
        rw [within_eq_ok, within_eq_ok] at h
        obtain ⟨⟨e2, rfl⟩, -, hr⟩ := readFields_writeFields _ _ _ _ _ rest h
        obtain ⟨e1, he1, hpos⟩ := writeNum_extends hw
        have hk := readNat_writeNum (e2 ++ rest) hw
        rw [← ByteArray.append_assoc] at hk
        refine ⟨extends_trans ⟨e1, he1⟩ ⟨e2, rfl⟩, fun _ => ?_,
          by simp only [readAt, hk, hc, hr, within_ok]⟩
        rw [he1, ByteArray.size_append, ByteArray.size_append]
        omega
      · cases h
  · split at h
    · rename_i acc1 h1
      rw [within_eq_ok] at h h1
      obtain ⟨⟨e2, rfl⟩, hpos, hr2⟩ := readTagged_writeTagged _ _ _ _ rest h
      obtain ⟨hext, -, hr1⟩ := readAt_writeAt _ _ _ _ _ (e2 ++ rest) h1
      rw [← ByteArray.append_assoc] at hr1
      refine ⟨extends_trans hext ⟨e2, rfl⟩, fun _ => ?_, by simp only [readAt, hr1, hr2, within_ok]⟩
      have := size_le_of_extends hext
      omega
    · cases h
termination_by (d, 0, 0)

theorem readFields_writeFields (d : Nat) (fields : List (Schema.Field Schema)) (vs : List Value)
    (acc out rest : ByteArray) (h : writeFields L d fields vs acc = .ok out) :
    (∃ e, out = acc ++ e) ∧ (consumesFields fields = true → acc.size < out.size) ∧
      readFields L (out ++ rest) d fields acc.size = .ok (vs, out.size) := by
  rw [writeFields.eq_def] at h
  split at h
  · cases h
    exact ⟨⟨.empty, ByteArray.append_empty.symm⟩, by simp [consumesFields],
      by simp only [readFields]⟩
  · rename_i f fs v vs
    split at h
    · rename_i acc1 h1
      rw [within_eq_ok] at h1
      obtain ⟨⟨e2, rfl⟩, hn2, hr2⟩ := readFields_writeFields _ _ _ _ _ rest h
      obtain ⟨hext, hn1, hr1⟩ := readAt_writeAt _ _ _ _ _ (e2 ++ rest) h1
      rw [← ByteArray.append_assoc] at hr1
      refine ⟨extends_trans hext ⟨e2, rfl⟩, fun hne => ?_,
        by simp only [readFields, hr1, hr2, within_ok]⟩
      have h1 := size_le_of_extends hext
      have h2 := size_le_of_extends ⟨e2, rfl⟩ (a := acc1)
      simp only [consumesFields, Bool.or_eq_true] at hne
      rcases hne with hne | hne
      · have := hn1 hne; omega
      · have := hn2 hne; omega
    · cases h
  · simp [fail] at h
termination_by (d, 1, vs.length)

theorem readItems_writeItems (d : Nat) (item : Schema) (vs : List Value) (index : Nat)
    (acc out rest : ByteArray) (h : writeItems L d item vs index acc = .ok out) :
    (∃ e, out = acc ++ e) ∧ (consumes item = true → acc.size + vs.length ≤ out.size) ∧
      readItems L (out ++ rest) d item vs.length index acc.size = .ok (vs, out.size) := by
  rw [writeItems.eq_def] at h
  split at h
  · cases h
    exact ⟨⟨.empty, ByteArray.append_empty.symm⟩, by simp, by simp only [List.length_nil, readItems]⟩
  · rename_i v vs
    split at h
    · rename_i acc1 h1
      rw [within_eq_ok] at h1
      obtain ⟨⟨e2, rfl⟩, hn2, hr2⟩ := readItems_writeItems _ _ _ _ _ _ rest h
      obtain ⟨hext, hn1, hr1⟩ := readAt_writeAt _ _ _ _ _ (e2 ++ rest) h1
      rw [← ByteArray.append_assoc] at hr1
      refine ⟨extends_trans hext ⟨e2, rfl⟩, fun hne => ?_,
        by simp only [List.length_cons, readItems, hr1, hr2, within_ok]⟩
      have := hn1 hne
      have := hn2 hne
      simp only [List.length_cons]
      omega
    · cases h
termination_by (d, 1, vs.length)

theorem readEntries_writeEntries (d : Nat) (key value : Schema) (es : List Value) (index : Nat)
    (acc out rest : ByteArray) (h : writeEntries L d key value es index acc = .ok out) :
    (∃ e, out = acc ++ e) ∧
      ((consumes key || consumes value) = true → acc.size + es.length ≤ out.size) ∧
      readEntries L (out ++ rest) d key value es.length index acc.size = .ok (es, out.size) := by
  rw [writeEntries.eq_def] at h
  split at h
  · cases h
    exact ⟨⟨.empty, ByteArray.append_empty.symm⟩, by simp,
      by simp only [List.length_nil, readEntries]⟩
  · rename_i k v es
    split at h
    · cases h
    · rename_i acc1 h1
      split at h
      · rename_i acc2 h2
        rw [within_eq_ok, within_eq_ok] at h1 h2
        obtain ⟨⟨e3, rfl⟩, hn3, hr3⟩ := readEntries_writeEntries _ _ _ _ _ _ _ rest h
        obtain ⟨⟨e2, rfl⟩, hn2, hr2⟩ := readAt_writeAt _ _ _ _ _ (e3 ++ rest) h2
        obtain ⟨hext, hn1, hr1⟩ := readAt_writeAt _ _ _ _ _ (e2 ++ e3 ++ rest) h1
        rw [← ByteArray.append_assoc] at hr2
        rw [← ByteArray.append_assoc, ← ByteArray.append_assoc] at hr1
        refine ⟨extends_trans hext (extends_trans ⟨e2, rfl⟩ ⟨e3, rfl⟩), fun hne => ?_,
          by simp only [List.length_cons, readEntries, hr1, hr2, hr3, within_ok]⟩
        have := hn3 hne
        have h1 := size_le_of_extends hext
        have h2 := size_le_of_extends ⟨e3, rfl⟩ (a := acc1 ++ e2)
        simp only [List.length_cons, ByteArray.size_append] at this h2 ⊢
        rcases Bool.or_eq_true_iff.mp hne with hne | hne
        · have := hn1 hne; omega
        · have := hn2 hne; simp only [ByteArray.size_append] at this; omega
      · cases h
  · simp [within, fail] at h
termination_by (d, 1, es.length)

theorem readTagged_writeTagged (d : Nat) (v : Value) (acc out rest : ByteArray)
    (h : writeTagged L d v acc = .ok out) :
    (∃ e, out = acc ++ e) ∧ acc.size < out.size ∧
      readTagged L (out ++ rest) d acc.size = .ok (v, out.size) := by
  rw [writeTagged.eq_def] at h
  split at h
  · obtain ⟨e, rfl, -⟩ := writeNum_extends h
    have hr := readNat_writeNum rest h
    rw [ByteArray.size_push] at hr
    refine ⟨pushed ⟨e, rfl⟩, by simp only [ByteArray.size_append, ByteArray.size_push]; omega, ?_⟩
    simp only [readTagged, tag_at ⟨e, rfl⟩, hr, ↓reduceIte]
  · obtain ⟨e, rfl, -⟩ := writeNum_extends h
    have hr := readNat_writeNum rest h
    rw [ByteArray.size_push] at hr
    refine ⟨pushed ⟨e, rfl⟩, by simp only [ByteArray.size_append, ByteArray.size_push]; omega, ?_⟩
    simp only [readTagged, tag_at ⟨e, rfl⟩, hr, ↓reduceIte, tags_distinct, unzigzag_zigzag]
  · obtain ⟨e, rfl, -⟩ := writeBlob_extends h
    have hr := readBlob_writeBlob rest h
    rw [ByteArray.size_push] at hr
    refine ⟨pushed ⟨e, rfl⟩, by simp only [ByteArray.size_append, ByteArray.size_push]; omega, ?_⟩
    simp only [readTagged, tag_at ⟨e, rfl⟩, hr, ↓reduceIte, tags_distinct,
      Codec.fromUTF8?_toUTF8]
  · obtain ⟨e, rfl, -⟩ := writeBlob_extends h
    have hr := readBlob_writeBlob rest h
    rw [ByteArray.size_push] at hr
    refine ⟨pushed ⟨e, rfl⟩, by simp only [ByteArray.size_append, ByteArray.size_push]; omega, ?_⟩
    simp only [readTagged, tag_at ⟨e, rfl⟩, hr, ↓reduceIte, tags_distinct]
  · simp [fail] at h
  · simp [fail] at h
  · split at h
    · rename_i acc1 hc
      obtain ⟨⟨e2, rfl⟩, hn, hr⟩ := readTaggedItems_writeTaggedItems _ _ _ _ _ rest h
      obtain ⟨e1, he1, -⟩ := writeNum_extends (writeCount_ok hc).1
      have hcount := readCount_writeCount (consumes := true) (e2 ++ rest) hc fun _ => by
        simp only [ByteArray.size_append] at hn ⊢
        omega
      rw [← ByteArray.append_assoc, ByteArray.size_push] at hcount
      have hext : ∃ e, acc1 ++ e2 = acc.push Tag.list ++ e :=
        ⟨e1 ++ e2, by rw [he1, ByteArray.append_assoc]⟩
      refine ⟨pushed hext, ?_, ?_⟩
      · have := size_le_of_extends hext
        simp only [ByteArray.size_push] at this
        omega
      · simp only [readTagged, tag_at hext, hcount, hr, ↓reduceIte, tags_distinct, true_or]
    · cases h
  · split at h
    · cases h
    · rename_i acc1 hw
      split at h
      · rename_i acc2 hc
        obtain ⟨⟨e3, rfl⟩, hn, hr⟩ := readTaggedItems_writeTaggedItems _ _ _ _ _ rest h
        obtain ⟨e2, he2, -⟩ := writeNum_extends (writeCount_ok hc).1
        obtain ⟨e1, he1, -⟩ := writeNum_extends hw
        have hcount := readCount_writeCount (consumes := true) (e3 ++ rest) hc fun _ => by
          simp only [ByteArray.size_append] at hn ⊢
          omega
        rw [← ByteArray.append_assoc] at hcount
        have hk := readNat_writeNum (e2 ++ e3 ++ rest) hw
        have hb : acc2 ++ e3 ++ rest = acc1 ++ (e2 ++ e3 ++ rest) := by
          rw [he2]; simp only [ByteArray.append_assoc]
        rw [← hb, ByteArray.size_push] at hk
        have hext : ∃ e, acc2 ++ e3 = acc.push Tag.ctor ++ e :=
          ⟨e1 ++ e2 ++ e3, by rw [he2, he1]; simp only [ByteArray.append_assoc]⟩
        refine ⟨pushed hext, ?_, ?_⟩
        · have := size_le_of_extends hext
          simp only [ByteArray.size_push] at this
          omega
        · simp only [readTagged, tag_at hext, hk, hcount, hr, ↓reduceIte, tags_distinct,
            or_true]
      · cases h
termination_by (d, 0, 0)

theorem readTaggedItems_writeTaggedItems (d : Nat) (vs : List Value) (index : Nat)
    (acc out rest : ByteArray) (h : writeTaggedItems L d vs index acc = .ok out) :
    (∃ e, out = acc ++ e) ∧ acc.size + vs.length ≤ out.size ∧
      readTaggedItems L (out ++ rest) d vs.length index acc.size = .ok (vs, out.size) := by
  rw [writeTaggedItems.eq_def] at h
  split at h
  · cases h
    exact ⟨⟨.empty, ByteArray.append_empty.symm⟩, by simp,
      by simp only [List.length_nil, readTaggedItems]⟩
  · rename_i v vs
    split at h
    · rename_i acc1 h1
      rw [within_eq_ok] at h1
      obtain ⟨⟨e2, rfl⟩, hn2, hr2⟩ := readTaggedItems_writeTaggedItems _ _ _ _ _ rest h
      obtain ⟨hext, hn1, hr1⟩ := readTagged_writeTagged _ _ _ _ (e2 ++ rest) h1
      rw [← ByteArray.append_assoc] at hr1
      refine ⟨extends_trans hext ⟨e2, rfl⟩, ?_,
        by simp only [List.length_cons, readTaggedItems, hr1, hr2, within_ok]⟩
      simp only [List.length_cons]
      omega
    · cases h
termination_by (d, 1, vs.length)

end

/-- What is written reads back: for every schema, value and limits. -/
theorem read_write {limits : Limits} {s : Schema} {v : Value} {bytes : ByteArray}
    (h : write limits s v = .ok bytes) : read limits s bytes = .ok v := by
  unfold write at h
  split at h
  · rename_i out hw
    split at h
    · cases h
      rename_i hsize
      have hr := (readAt_writeAt _ _ _ _ _ .empty hw).2.2
      rw [ByteArray.append_empty, ByteArray.size_empty] at hr
      simp only [read, Nat.not_lt.mpr hsize, ↓reduceIte, hr]
    · cases h
  · cases h

/-! Each value has one body: what is read is what the writer writes for the value read. -/

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.mp
  simp

theorem extract_one {bytes : ByteArray} {pos : Nat} {b : UInt8} (h : bytes[pos]? = some b) :
    bytes.extract pos (pos + 1) = [b].toByteArray := by
  obtain ⟨hp, rfl⟩ := getElem_of_getElem? h
  exact ByteArray.extract_add_one (by omega)

theorem append_extract {acc bytes : ByteArray} {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    acc ++ bytes.extract i j ++ bytes.extract j k = acc ++ bytes.extract i k := by
  rw [ByteArray.append_assoc, ByteArray.extract_append_extract, Nat.min_eq_left hij,
    Nat.max_eq_right hjk]

theorem writeNat_readNatFrom {bytes : ByteArray} {start bound budget pos stop n : Nat}
    {first : Bool} (acc : ByteArray)
    (h : readNatFrom bytes start bound budget pos first = .ok (n, stop)) :
    pos < stop ∧ natBytes n ≤ budget ∧ (first = false → 0 < n) ∧
      writeNat acc n = acc ++ bytes.extract pos stop := by
  induction budget generalizing pos first n stop acc with
  | zero => simp [readNatFrom, fail] at h
  | succ budget ih =>
    rw [readNatFrom] at h
    split at h
    · simp [fail] at h
    · rename_i b hb
      have hlt := UInt8.toNat_lt b
      split at h
      · rename_i hsmall
        split at h
        · simp [fail] at h
        · rename_i hpad
          cases h
          have h128 : b.toNat < 128 := UInt8.lt_iff_toNat_lt.mp hsmall
          refine ⟨by omega, by rw [natBytes_lt h128]; omega, fun hf => ?_, ?_⟩
          · have : b ≠ 0 := fun h0 => hpad ⟨h0, hf⟩
            have : b.toNat ≠ 0 := fun h0 => this (UInt8.toNat_inj.mp (by simpa using h0))
            omega
          · rw [writeNat_lt h128, toUInt8_toNat, extract_one hb, push_eq_append]
      · rename_i hbig
        have h128 : ¬b.toNat < 128 := fun h => hbig (UInt8.lt_iff_toNat_lt.mpr h)
        split at h
        · rename_i m stop' hrec
          cases h
          obtain ⟨hpos, hbytes, hm, hw⟩ := ih (acc.push b) hrec
          have hm := hm rfl
          have hge : ¬b.toNat - 128 + 128 * m < 128 := by omega
          have hdiv : (b.toNat - 128 + 128 * m) / 128 = m := by omega
          refine ⟨by omega, by rw [natBytes_ge hge, hdiv]; omega, fun _ => by omega, ?_⟩
          have hmod : ((b.toNat - 128 + 128 * m) % 128 + 128).toUInt8 = b := by
            rw [show (b.toNat - 128 + 128 * m) % 128 + 128 = b.toNat by omega, toUInt8_toNat]
          rw [writeNat_ge hge, hdiv, hmod, hw, push_eq_append, ← extract_one hb,
            append_extract (by omega) (by omega)]
        · cases h

theorem writeNum_readNat {bytes : ByteArray} {pos n stop : Nat} (acc : ByteArray)
    (h : readNat L bytes pos = .ok (n, stop)) :
    pos < stop ∧ writeNum L acc n = .ok (acc ++ bytes.extract pos stop) := by
  obtain ⟨hpos, hn, -, hw⟩ := writeNat_readNatFrom acc h
  exact ⟨hpos, by simp only [writeNum, hn, ↓reduceIte, hw]⟩

theorem writeBlob_readBlob {bytes : ByteArray} {pos stop : Nat} {blob : ByteArray}
    (acc : ByteArray) (h : readBlob L bytes pos = .ok (blob, stop)) :
    pos < stop ∧ writeBlob L acc blob = .ok (acc ++ bytes.extract pos stop) := by
  unfold readBlob at h
  split at h
  · cases h
  · rename_i n start hn
    split at h
    · simp [fail] at h
    · rename_i hl
      split at h
      · simp [fail] at h
      · rename_i hleft
        cases h
        obtain ⟨hpos, hw⟩ := writeNum_readNat acc hn
        have hsize : (bytes.extract start (start + n)).size = n := by
          rw [ByteArray.size_extract]; omega
        refine ⟨by omega, ?_⟩
        simp only [writeBlob, hsize, Nat.le_of_not_lt hl, ↓reduceIte, hw, Except.map,
          append_extract (Nat.le_of_lt hpos) (Nat.le_add_right start n)]

theorem writeCount_readCount {bytes : ByteArray} {pos n stop : Nat} {consumes : Bool}
    (acc : ByteArray) (h : readCount L bytes consumes pos = .ok (n, stop)) :
    pos < stop ∧ writeCount L acc n = .ok (acc ++ bytes.extract pos stop) := by
  unfold readCount at h
  split at h
  · cases h
  · rename_i m start hm
    split at h
    · simp [fail] at h
    · rename_i hl
      split at h
      · simp [fail] at h
      · cases h
        obtain ⟨hpos, hw⟩ := writeNum_readNat acc hm
        exact ⟨hpos, by simp only [writeCount, Nat.le_of_not_lt hl, ↓reduceIte, hw]⟩

theorem zigzag_unzigzag (n : Nat) : zigzag (unzigzag n) = n := by
  unfold zigzag unzigzag
  split <;> split <;> omega

theorem toUTF8_of_fromUTF8? {b : ByteArray} {t : String} (h : String.fromUTF8? b = some t) :
    t.toUTF8 = b := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

theorem push_extract {acc bytes : ByteArray} {pos stop : Nat} {t : UInt8}
    (hb : bytes[pos]? = some t) (hle : pos + 1 ≤ stop) :
    acc.push t ++ bytes.extract (pos + 1) stop = acc ++ bytes.extract pos stop := by
  rw [push_eq_append, ← extract_one hb, append_extract (by omega) hle]

mutual

theorem writeAt_readAt (bytes : ByteArray) (d : Nat) (s : Schema) (pos : Nat) (v : Value)
    (stop : Nat) (acc : ByteArray) (h : readAt L bytes d s pos = .ok (v, stop)) :
    pos ≤ stop ∧ writeAt L d s v acc = .ok (acc ++ bytes.extract pos stop) := by
  rw [readAt.eq_def] at h
  split at h
  · split at h
    · cases h
      rename_i hn
      obtain ⟨hpos, hw⟩ := writeNum_readNat acc hn
      exact ⟨by omega, by simp only [writeAt, hw]⟩
    · cases h
  · split at h
    · cases h
      rename_i hn
      obtain ⟨hpos, hw⟩ := writeNum_readNat acc hn
      exact ⟨by omega, by simp only [writeAt, zigzag_unzigzag, hw]⟩
    · cases h
  · split at h
    · split at h
      · cases h
        rename_i t ht hb
        obtain ⟨hpos, hw⟩ := writeBlob_readBlob acc hb
        exact ⟨by omega, by simp only [writeAt, toUTF8_of_fromUTF8? ht, hw]⟩
      · simp [fail] at h
    · cases h
  · split at h
    · cases h
      rename_i hb
      obtain ⟨hpos, hw⟩ := writeBlob_readBlob acc hb
      exact ⟨by omega, by simp only [writeAt, hw]⟩
    · cases h
  · cases h
    exact ⟨Nat.le_refl _, by simp only [writeAt, ByteArray.extract_same, ByteArray.append_empty]⟩
  all_goals try (simp [fail] at h; done)
  · split at h
    · rename_i n p1 hc
      split at h
      · cases h
        rename_i vs stop hi
        obtain ⟨hp1, hw1⟩ := writeCount_readCount acc hc
        obtain ⟨hp2, hlen, hw2⟩ := writeItems_readItems _ _ _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hi
        refine ⟨by omega, ?_⟩
        simp only [writeAt, hlen, hw1, hw2, append_extract (Nat.le_of_lt hp1) hp2]
      · cases h
    · cases h
  · split at h
    · rename_i n p1 hc
      split at h
      · cases h
        rename_i es stop hi
        obtain ⟨hp1, hw1⟩ := writeCount_readCount acc hc
        obtain ⟨hp2, hlen, hw2⟩ :=
          writeEntries_readEntries _ _ _ _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hi
        refine ⟨by omega, ?_⟩
        simp only [writeAt, hlen, hw1, hw2, append_extract (Nat.le_of_lt hp1) hp2]
      · cases h
    · cases h
  · split at h
    · cases h
      rename_i vs stop hf
      rw [within_eq_ok] at hf
      obtain ⟨hp, hw⟩ := writeFields_readFields _ _ _ _ _ _ acc hf
      exact ⟨hp, by simp only [writeAt, hw, within_ok]⟩
    · cases h
  · split at h
    · cases h
    · rename_i k p1 hk
      split at h
      · simp [within, fail] at h
      · rename_i c hc
        split at h
        · cases h
          rename_i vs stop hf
          rw [within_eq_ok, within_eq_ok] at hf
          obtain ⟨hp1, hw1⟩ := writeNum_readNat acc hk
          obtain ⟨hp2, hw2⟩ := writeFields_readFields _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hf
          refine ⟨by omega, ?_⟩
          simp only [writeAt, hc, hw1, hw2, within_ok, append_extract (Nat.le_of_lt hp1) hp2]
        · cases h
  · split at h
    · cases h
    · rename_i i p1 hi
      split at h
      · cases h
        rename_i x stop hx
        rw [within_eq_ok] at hi hx
        obtain ⟨hp1, hw1⟩ := writeAt_readAt _ _ _ _ _ _ acc hi
        obtain ⟨hp2, hw2⟩ := writeTagged_readTagged _ _ _ _ _ (acc ++ bytes.extract pos p1) hx
        refine ⟨by omega, ?_⟩
        simp only [writeAt, hw1, hw2, within_ok, append_extract hp1 hp2]
      · cases h
termination_by (d, 0, 0)

theorem writeFields_readFields (bytes : ByteArray) (d : Nat) (fields : List (Schema.Field Schema))
    (pos : Nat) (vs : List Value) (stop : Nat) (acc : ByteArray)
    (h : readFields L bytes d fields pos = .ok (vs, stop)) :
    pos ≤ stop ∧ writeFields L d fields vs acc = .ok (acc ++ bytes.extract pos stop) := by
  rw [readFields.eq_def] at h
  split at h
  · cases h
    exact ⟨Nat.le_refl _, by simp only [writeFields, ByteArray.extract_same, ByteArray.append_empty]⟩
  · rename_i f fs
    split at h
    · cases h
    · rename_i v p1 hv
      split at h
      · cases h
        rename_i vs stop hr
        rw [within_eq_ok] at hv
        obtain ⟨hp1, hw1⟩ := writeAt_readAt _ _ _ _ _ _ acc hv
        obtain ⟨hp2, hw2⟩ := writeFields_readFields _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hr
        refine ⟨by omega, ?_⟩
        simp only [writeFields, hw1, hw2, within_ok, append_extract hp1 hp2]
      · cases h
termination_by (d, 1, fields.length)

theorem writeItems_readItems (bytes : ByteArray) (d : Nat) (item : Schema) (n index pos : Nat)
    (vs : List Value) (stop : Nat) (acc : ByteArray)
    (h : readItems L bytes d item n index pos = .ok (vs, stop)) :
    pos ≤ stop ∧ vs.length = n ∧
      writeItems L d item vs index acc = .ok (acc ++ bytes.extract pos stop) := by
  rw [readItems.eq_def] at h
  split at h
  · cases h
    exact ⟨Nat.le_refl _, rfl,
      by simp only [writeItems, ByteArray.extract_same, ByteArray.append_empty]⟩
  · rename_i n
    split at h
    · cases h
    · rename_i v p1 hv
      split at h
      · cases h
        rename_i vs stop hr
        rw [within_eq_ok] at hv
        obtain ⟨hp1, hw1⟩ := writeAt_readAt _ _ _ _ _ _ acc hv
        obtain ⟨hp2, hlen, hw2⟩ :=
          writeItems_readItems _ _ _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hr
        refine ⟨by omega, by simp [hlen], ?_⟩
        simp only [writeItems, hw1, hw2, within_ok, append_extract hp1 hp2]
      · cases h
termination_by (d, 1, n)

theorem writeEntries_readEntries (bytes : ByteArray) (d : Nat) (key value : Schema)
    (n index pos : Nat) (es : List Value) (stop : Nat) (acc : ByteArray)
    (h : readEntries L bytes d key value n index pos = .ok (es, stop)) :
    pos ≤ stop ∧ es.length = n ∧
      writeEntries L d key value es index acc = .ok (acc ++ bytes.extract pos stop) := by
  rw [readEntries.eq_def] at h
  split at h
  · cases h
    exact ⟨Nat.le_refl _, rfl,
      by simp only [writeEntries, ByteArray.extract_same, ByteArray.append_empty]⟩
  · rename_i n
    split at h
    · cases h
    · rename_i k p1 hk
      split at h
      · cases h
      · rename_i v p2 hv
        split at h
        · cases h
          rename_i es stop hr
          rw [within_eq_ok, within_eq_ok] at hk hv
          obtain ⟨hp1, hw1⟩ := writeAt_readAt _ _ _ _ _ _ acc hk
          obtain ⟨hp2, hw2⟩ := writeAt_readAt _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hv
          rw [append_extract hp1 hp2] at hw2
          obtain ⟨hp3, hlen, hw3⟩ :=
            writeEntries_readEntries _ _ _ _ _ _ _ _ _ (acc ++ bytes.extract pos p2) hr
          refine ⟨by omega, by simp [hlen], ?_⟩
          simp only [writeEntries, hw1, hw2, hw3, within_ok, append_extract (by omega : pos ≤ p2) hp3]
        · cases h
termination_by (d, 1, n)

theorem writeTagged_readTagged (bytes : ByteArray) (d pos : Nat) (v : Value) (stop : Nat)
    (acc : ByteArray) (h : readTagged L bytes d pos = .ok (v, stop)) :
    pos ≤ stop ∧ writeTagged L d v acc = .ok (acc ++ bytes.extract pos stop) := by
  rw [readTagged.eq_def] at h
  split at h
  · simp [fail] at h
  · rename_i tag hb
    split at h
    · rename_i ht
      subst ht
      split at h
      · cases h
        rename_i hn
        obtain ⟨hpos, hw⟩ := writeNum_readNat (acc.push Tag.nat) hn
        exact ⟨by omega, by simp only [writeTagged, hw, push_extract hb (Nat.le_of_lt hpos)]⟩
      · cases h
    split at h
    · rename_i ht
      subst ht
      split at h
      · cases h
        rename_i hn
        obtain ⟨hpos, hw⟩ := writeNum_readNat (acc.push Tag.int) hn
        exact ⟨by omega, by simp only [writeTagged, zigzag_unzigzag, hw, push_extract hb (Nat.le_of_lt hpos)]⟩
      · cases h
    split at h
    · rename_i ht
      subst ht
      split at h
      · split at h
        · cases h
          rename_i t ht hblob
          obtain ⟨hpos, hw⟩ := writeBlob_readBlob (acc.push Tag.string) hblob
          exact ⟨by omega, by
            simp only [writeTagged, toUTF8_of_fromUTF8? ht, hw, push_extract hb (Nat.le_of_lt hpos)]⟩
        · simp [fail] at h
      · cases h
    split at h
    · rename_i ht
      subst ht
      split at h
      · cases h
        rename_i hblob
        obtain ⟨hpos, hw⟩ := writeBlob_readBlob (acc.push Tag.bytes) hblob
        exact ⟨by omega, by simp only [writeTagged, hw, push_extract hb (Nat.le_of_lt hpos)]⟩
      · cases h
    split at h
    · split at h
      · simp [fail] at h
      · rename_i d
        split at h
        · rename_i ht
          subst ht
          split at h
          · cases h
          · rename_i n p1 hc
            split at h
            · cases h
              rename_i vs stop hi
              obtain ⟨hp1, hw1⟩ := writeCount_readCount (acc.push Tag.list) hc
              obtain ⟨hp2, hlen, hw2⟩ := writeTaggedItems_readTaggedItems _ _ _ _ _ _ _
                (acc.push Tag.list ++ bytes.extract (pos + 1) p1) hi
              refine ⟨by omega, ?_⟩
              simp only [writeTagged, hlen, hw1, hw2, append_extract (Nat.le_of_lt hp1) hp2]
              rw [push_extract hb]
              omega
            · cases h
        · rename_i hnot
          have ht : tag = Tag.ctor := (‹tag = Tag.list ∨ tag = Tag.ctor›).resolve_left hnot
          subst ht
          split at h
          · cases h
          · rename_i k p1 hk
            split at h
            · cases h
            · rename_i n p2 hc
              split at h
              · cases h
                rename_i vs stop hi
                obtain ⟨hp1, hw1⟩ := writeNum_readNat (acc.push Tag.ctor) hk
                obtain ⟨hp2, hw2⟩ :=
                  writeCount_readCount (acc.push Tag.ctor ++ bytes.extract (pos + 1) p1) hc
                rw [append_extract (Nat.le_of_lt hp1) (Nat.le_of_lt hp2)] at hw2
                obtain ⟨hp3, hlen, hw3⟩ := writeTaggedItems_readTaggedItems _ _ _ _ _ _ _
                  (acc.push Tag.ctor ++ bytes.extract (pos + 1) p2) hi
                refine ⟨by omega, ?_⟩
                simp only [writeTagged, hlen, hw1, hw2, hw3,
                  append_extract (by omega : pos + 1 ≤ p2) hp3]
                rw [push_extract hb]
                omega
              · cases h
    · simp [fail] at h
termination_by (d, 0, 0)

theorem writeTaggedItems_readTaggedItems (bytes : ByteArray) (d n index pos : Nat)
    (vs : List Value) (stop : Nat) (acc : ByteArray)
    (h : readTaggedItems L bytes d n index pos = .ok (vs, stop)) :
    pos ≤ stop ∧ vs.length = n ∧
      writeTaggedItems L d vs index acc = .ok (acc ++ bytes.extract pos stop) := by
  rw [readTaggedItems.eq_def] at h
  split at h
  · cases h
    exact ⟨Nat.le_refl _, rfl,
      by simp only [writeTaggedItems, ByteArray.extract_same, ByteArray.append_empty]⟩
  · rename_i n
    split at h
    · cases h
    · rename_i v p1 hv
      split at h
      · cases h
        rename_i vs stop hr
        rw [within_eq_ok] at hv
        obtain ⟨hp1, hw1⟩ := writeTagged_readTagged _ _ _ _ _ acc hv
        obtain ⟨hp2, hlen, hw2⟩ :=
          writeTaggedItems_readTaggedItems _ _ _ _ _ _ _ (acc ++ bytes.extract pos p1) hr
        refine ⟨by omega, by simp [hlen], ?_⟩
        simp only [writeTaggedItems, hw1, hw2, within_ok, append_extract hp1 hp2]
      · cases h
termination_by (d, 1, n)

end

/-- What is read is what the writer writes for the value read: a value has one body. -/
theorem write_read {limits : Limits} {s : Schema} {v : Value} {bytes : ByteArray}
    (h : read limits s bytes = .ok v) : write limits s v = .ok bytes := by
  unfold read at h
  split at h
  · simp [fail] at h
  · rename_i hsize
    split at h
    · rename_i v' stop hr
      split at h
      · rename_i hstop
        cases h
        have hw := (writeAt_readAt _ _ _ _ _ _ .empty hr).2
        rw [hstop, ByteArray.extract_zero_size, ByteArray.empty_append] at hw
        simp only [write, hw, Nat.le_of_not_lt hsize, ↓reduceIte]
      · simp [fail] at h
    · cases h

theorem read_eq_ok_iff {limits : Limits} {s : Schema} {v : Value} {bytes : ByteArray} :
    read limits s bytes = .ok v ↔ write limits s v = .ok bytes :=
  ⟨write_read, read_write⟩

end Lanes.Body
