/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Cbor.Decode
public import Lanes.Proof.ByteArray
public import Lanes.Proof.Utf8

/-!
# What the CBOR decoder and encoder are proved to do

- `Cbor.decode_encode`: the decoder reads back what the encoder writes, every value within the
  decoder's limits, taking any encoding or only preferred ones.
- `Cbor.decode_deterministic_encode`: the decoder that takes only deterministic encodings reads
  back every value whose maps are in deterministic order, from its encoding.
- `Cbor.encodeDeterministic_eq_of_equiv`: the deterministic encoding is canonical: two values
  equal in the data model, `Cbor.Equiv`, whose maps may hold their entries in other orders, have
  the same deterministic encoding.
- `Cbor.encode_of_decode_preferred`, `Cbor.encodeDeterministic_of_decode`: a strict decoder takes
  only the bytes the encoder writes for what it read, so a value has one accepted encoding.
- `Cbor.decode_tooLarge`, `Cbor.fits_of_decode`: the decoder refuses an input over its size, and
  what it reads is within its depth and length.
-/

@[expose] public section

namespace Lanes.Cbor

/-! ### Writing -/

theorem push_eq (out : ByteArray) (bytes : List UInt8) : push out bytes = out ++ bytes.toByteArray := by
  induction bytes generalizing out with
  | nil => simp [push, ByteArray.append_empty]
  | cons b bs ih =>
    simp only [push, List.foldl_cons] at ih ⊢
    rw [ih, show b :: bs = [b] ++ bs from rfl, List.toByteArray_append, ← ByteArray.append_assoc,
      ByteArray.append_toByteArray_singleton]

/-- The items of a list one after the other. -/
def encodeList (xs : List Cbor) : ByteArray := encodeAll .empty xs

/-- The entries of a map one after the other. -/
def encodeMap (es : List (Cbor × Cbor)) : ByteArray := encodeEntries .empty es

mutual
theorem encodeTo_eq : (out : ByteArray) → (v : Cbor) → encodeTo out v = out ++ encode v
  | out, .array xs => by
    simp only [encode, encodeTo]
    rw [encodeAll_eq, encodeAll_eq (push _ _), push_eq, push_eq, ByteArray.append_assoc,
      ByteArray.empty_append]
  | out, .map es => by
    simp only [encode, encodeTo]
    rw [encodeEntries_eq, encodeEntries_eq (push _ _), push_eq, push_eq, ByteArray.append_assoc,
      ByteArray.empty_append]
  | out, .tag t v => by
    simp only [encode, encodeTo]
    rw [encodeTo_eq _ v, encodeTo_eq (push _ _) v, push_eq, push_eq, ByteArray.append_assoc,
      ByteArray.empty_append]
  | out, .bytes b | out, .text s => by
    simp only [encode, encodeTo, push_eq, ByteArray.append_assoc, ByteArray.empty_append]
  | out, .bool b => by cases b <;> simp only [encode, encodeTo, push_eq, ByteArray.empty_append]
  | out, .uint _ | out, .nint _ | out, .null | out, .undefined | out, .simple _ | out, .float _ => by
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append]

theorem encodeAll_eq : (out : ByteArray) → (xs : List Cbor) →
    encodeAll out xs = out ++ encodeAll .empty xs
  | out, [] => by simp [encodeAll, ByteArray.append_empty]
  | out, x :: xs => by
    simp only [encodeAll]
    rw [encodeAll_eq _ xs, encodeAll_eq (encodeTo .empty x) xs, encodeTo_eq out x,
      ← encode, ByteArray.append_assoc]

theorem encodeEntries_eq : (out : ByteArray) → (es : List (Cbor × Cbor)) →
    encodeEntries out es = out ++ encodeEntries .empty es
  | out, [] => by simp [encodeEntries, ByteArray.append_empty]
  | out, e :: es => by
    simp only [encodeEntries]
    rw [encodeEntries_eq _ es, encodeEntries_eq (encodeTo (encodeTo .empty e.1) e.2) es,
      encodeTo_eq (encodeTo out e.1) e.2, encodeTo_eq out e.1,
      encodeTo_eq (encodeTo .empty e.1) e.2, ← encode, ByteArray.append_assoc,
      ByteArray.append_assoc, ByteArray.append_assoc]
end

theorem encodeList_cons (x : Cbor) (xs : List Cbor) :
    encodeList (x :: xs) = encode x ++ encodeList xs := by
  simp only [encodeList, encodeAll]
  rw [encodeAll_eq, ← encode]

theorem encodeMap_cons (e : Cbor × Cbor) (es : List (Cbor × Cbor)) :
    encodeMap (e :: es) = encode e.1 ++ encode e.2 ++ encodeMap es := by
  simp only [encodeMap, encodeEntries]
  rw [encodeEntries_eq, encodeTo_eq, ← encode]

theorem encode_array (xs : List Cbor) :
    encode (.array xs) = (head 4 xs.length).toByteArray ++ encodeList xs := by
  simp only [encode, encodeTo]
  rw [encodeAll_eq, push_eq, ByteArray.empty_append]; rfl

theorem encode_map (es : List (Cbor × Cbor)) :
    encode (.map es) = (head 5 es.length).toByteArray ++ encodeMap es := by
  simp only [encode, encodeTo]
  rw [encodeEntries_eq, push_eq, ByteArray.empty_append]; rfl

theorem encode_tag (t : UInt64) (v : Cbor) :
    encode (.tag t v) = (head 6 t.toNat).toByteArray ++ encode v := by
  simp only [encode, encodeTo]
  rw [encodeTo_eq, push_eq, ByteArray.empty_append]; rfl

/-! ### Reading a head -/

theorem byte_at (p s : ByteArray) (l : List UInt8) (i : Nat) (h : i < l.length) :
    (p ++ l.toByteArray ++ s)[p.size + i]? = some l[i] := by
  rw [ByteArray.append_assoc, getElem?_append_front, ByteArray.toList_data_append,
    List.toList_data_toByteArray, List.getElem?_append_left h, List.getElem?_eq_getElem h]

theorem extract_after (p s : ByteArray) (b : UInt8) (l : List UInt8) :
    (p ++ (b :: l).toByteArray ++ s).extract (p.size + 1) (p.size + 1 + l.length) =
      l.toByteArray := by
  have hp : (p ++ [b].toByteArray).size = p.size + 1 := by
    rw [ByteArray.size_append, List.size_toByteArray]; rfl
  have := extract_append_front (p ++ [b].toByteArray) l.toByteArray s
  rw [hp, List.size_toByteArray] at this
  rw [← this, show b :: l = [b] ++ l from rfl, List.toByteArray_append]
  simp only [ByteArray.append_assoc]

theorem toNat_toUInt8 {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem join_argument {w n : Nat} (h : n < 256 ^ w) :
    Digits.join 256 ((argument w n).map UInt8.toNat) = n := by
  have : (argument w n).map UInt8.toNat = Digits.split 256 w n := by
    rw [argument, List.map_map]
    conv => rhs; rw [← List.map_id (Digits.split 256 w n)]
    exact List.map_congr_left fun d hd => toNat_toUInt8 (Digits.lt_of_mem_split (by decide) hd)
  rw [this, Digits.join_split, Nat.mod_eq_of_lt h]

theorem length_argument (w n : Nat) : (argument w n).length = w := by
  simp [argument, Digits.length_split]

theorem readHead_short (p s : ByteArray) {major n : Nat} (hm : major < 8) (hn : n < 24) :
    readHead (p ++ [(major * 32 + n).toUInt8].toByteArray ++ s) p.size =
      .ok (major, n, n, p.size + 1) := by
  have := byte_at p s [(major * 32 + n).toUInt8] 0 (by simp)
  rw [Nat.add_zero] at this
  simp only [readHead, this, List.getElem_cons_zero]
  rw [toNat_toUInt8 (by omega)]
  simp only [show (major * 32 + n) % 32 = n by omega, hn, ↓reduceIte,
    show (major * 32 + n) / 32 = major by omega]

theorem readHead_long (p s : ByteArray) {major info n : Nat} (hm : major < 8) (hi : 24 ≤ info)
    (hi' : info < 28) (hn : n < 256 ^ 2 ^ (info - 24)) :
    readHead (p ++ (longHead major info n).toByteArray ++ s) p.size =
      .ok (major, info, n, p.size + 1 + 2 ^ (info - 24)) := by
  have := byte_at p s (longHead major info n) 0 (by simp [longHead])
  rw [Nat.add_zero] at this
  have hsize : p.size + 1 + 2 ^ (info - 24) ≤
      (p ++ (longHead major info n).toByteArray ++ s).size := by
    simp [ByteArray.size_append, List.size_toByteArray, longHead, length_argument]; omega
  unfold readHead
  rw [this]
  simp only [longHead, List.getElem_cons_zero] at hsize ⊢
  simp only [toNat_toUInt8 (n := major * 32 + info) (by omega)]
  simp only [show (major * 32 + info) % 32 = info by omega, show ¬info < 24 by omega,
    show info < 28 by omega, ↓reduceIte, show (major * 32 + info) / 32 = major by omega, hsize,
    readArgument]
  have := extract_after p s (major * 32 + info).toUInt8 (argument (2 ^ (info - 24)) n)
  rw [length_argument] at this
  rw [this, List.toList_data_toByteArray, join_argument hn]

/-- The additional information of the head `head` writes for `n`. -/
def headInfo (n : Nat) : Nat :=
  if n < 24 then n else if n < 2 ^ 8 then 24 else if n < 2 ^ 16 then 25
  else if n < 2 ^ 32 then 26 else 27

theorem headInfo_ne (n : Nat) : headInfo n ≠ 31 := by
  unfold headInfo; split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem readHead_head (p s : ByteArray) {major n : Nat} (hm : major < 8) (hn : n < 2 ^ 64) :
    readHead (p ++ (head major n).toByteArray ++ s) p.size =
      .ok (major, headInfo n, n, p.size + (head major n).length) := by
  unfold head headInfo
  by_cases h0 : n < 24
  · simp only [h0, ↓reduceIte]; exact readHead_short p s hm h0
  by_cases h1 : n < 2 ^ 8
  · simp only [h0, h1, ↓reduceIte]; rw [readHead_long p s hm (by decide) (by decide) (by simpa)]
    simp [longHead, length_argument]
  by_cases h2 : n < 2 ^ 16
  · simp only [h0, h1, h2, ↓reduceIte]; rw [readHead_long p s hm (by decide) (by decide) (by simpa)]
    simp [longHead, length_argument]
  by_cases h3 : n < 2 ^ 32
  · simp only [h0, h1, h2, h3, ↓reduceIte]
    rw [readHead_long p s hm (by decide) (by decide) (by simpa)]
    simp [longHead, length_argument]
  · simp only [h0, h1, h2, h3, ↓reduceIte]
    rw [readHead_long p s hm (by decide) (by decide) (by simpa)]
    simp [longHead, length_argument]

/-! ### Reading back what is written -/

theorem append_shift (p a b s : ByteArray) : p ++ (a ++ b) ++ s = p ++ a ++ (b ++ s) := by
  simp only [ByteArray.append_assoc]

theorem append_shift' (p a b s : ByteArray) : p ++ a ++ (b ++ s) = p ++ a ++ b ++ s := by
  simp only [ByteArray.append_assoc]

theorem size_head_append (p a : ByteArray) (l : List UInt8) :
    p.size + (l.toByteArray ++ a).size = (p ++ l.toByteArray).size + a.size := by
  simp only [ByteArray.size_append, List.size_toByteArray]; omega

theorem readString_after (cfg : Config) (q b s : ByteArray) (h : b.size ≤ cfg.maxLength) :
    readString cfg (q ++ b ++ s) b.size q.size = .ok (b, q.size + b.size) := by
  have hs : ¬(q ++ b ++ s).size < q.size + b.size := by simp [ByteArray.size_append]
  simp only [readString, show ¬cfg.maxLength < b.size by omega, hs, ↓reduceIte]
  rw [ByteArray.append_assoc, extract_append_front]

theorem special_simple (v : Simple) {info : Nat} (hi : info = headInfo v.val.toNat) :
    special info v.val.toNat = .ok (.simple v) := by
  obtain ⟨v, hv⟩ := v
  have hlt : v.toNat < 256 := v.toNat_lt
  have hv' : v.toNat < 20 ∨ 32 ≤ v.toNat := by
    rcases hv with h | h
    · exact .inl (UInt8.lt_iff_toNat_lt.mp h)
    · exact .inr (UInt8.le_iff_toNat_le.mp h)
  have hi' : info ≠ 20 ∧ info ≠ 21 ∧ info ≠ 22 ∧ info ≠ 23 ∧ info ≠ 25 ∧ info ≠ 26 ∧
      info ≠ 27 ∧ info ≠ 31 := by
    subst hi; unfold headInfo; simp only
    split <;> (try split) <;> (try split) <;> (try split) <;> omega
  unfold special
  simp only [hi'.1, hi'.2.1, hi'.2.2.1, hi'.2.2.2.1, hi'.2.2.2.2.1, hi'.2.2.2.2.2.1,
    hi'.2.2.2.2.2.2.1, hi'.2.2.2.2.2.2.2, ↓reduceIte]
  split
  · congr
    exact UInt8.ofNat_toNat
  · omega

mutual
theorem item_encode (cfg : Config) (hL : cfg.maxLength < 2 ^ 64) : (v : Cbor) → (d : Nat) →
    (p s : ByteArray) → v.fits d cfg.maxLength = true →
    item cfg (p ++ encode v ++ s) d p.size = .ok (v, p.size + (encode v).size)
  | _, 0, _, _, h => by simp [fits] at h
  | .uint n, d + 1, p, s, _ => by
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item]
    rw [readHead_head p s (by decide) n.toNat_lt]
    simp [headInfo_ne, List.size_toByteArray]
  | .nint n, d + 1, p, s, _ => by
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item]
    rw [readHead_head p s (by decide) n.toNat_lt]
    simp [headInfo_ne, List.size_toByteArray]
  | .bytes b, d + 1, p, s, h => by
    simp only [fits, decide_eq_true_eq] at h
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item, append_shift]
    rw [readHead_head p (b ++ s) (by decide) (by omega)]
    simp only [headInfo_ne, ↓reduceIte, ← List.size_toByteArray]
    rw [append_shift', ← @ByteArray.size_append p, readString_after cfg _ b s h, size_head_append]
  | .text t, d + 1, p, s, h => by
    simp only [fits, decide_eq_true_eq] at h
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item, append_shift]
    rw [readHead_head p (t.toUTF8 ++ s) (by decide) (by omega)]
    simp only [headInfo_ne, ↓reduceIte, ← List.size_toByteArray]
    rw [append_shift', ← @ByteArray.size_append p, show t.utf8ByteSize = t.toUTF8.size from rfl,
      readString_after cfg _ t.toUTF8 s (by simpa using h), size_head_append]
    simp [readText, Except.map, fromUTF8?_toByteArray]
  | .array xs, d + 1, p, s, h => by
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [encode_array, append_shift, item, readHead_head p _ (by decide) (by omega)]
    simp only [readItems, headInfo_ne, show ¬cfg.maxLength < xs.length by omega, ↓reduceIte,
      ← List.size_toByteArray]
    rw [append_shift', ← @ByteArray.size_append p, readMany_encodeList cfg hL xs d _ s [] h.2,
      size_head_append]
    rfl
  | .map es, d + 1, p, s, h => by
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [encode_map, append_shift, item, readHead_head p _ (by decide) (by omega)]
    simp only [readItems, headInfo_ne, show ¬cfg.maxLength < es.length by omega, ↓reduceIte,
      ← List.size_toByteArray]
    rw [append_shift', ← @ByteArray.size_append p, readMany_encodeMap cfg hL es d _ s [] h.2,
      size_head_append]
    rfl
  | .tag t v, d + 1, p, s, h => by
    simp only [fits] at h
    rw [encode_tag, append_shift, item, readHead_head p _ (by decide) t.toNat_lt]
    simp only [headInfo_ne, ↓reduceIte, ← List.size_toByteArray]
    rw [append_shift', ← @ByteArray.size_append p, item_encode cfg hL v d _ s h, size_head_append]
    simp
  | .bool b, d + 1, p, s, _ => by
    cases b <;>
    · simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item]
      rw [readHead_head p s (by decide) (by decide)]
      simp [special, headInfo, List.size_toByteArray, Except.map]
  | .null, d + 1, p, s, _ | .undefined, d + 1, p, s, _ => by
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item]
    rw [readHead_head p s (by decide) (by decide)]
    simp [special, headInfo, List.size_toByteArray, Except.map]
  | .simple v, d + 1, p, s, _ => by
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item]
    rw [readHead_head p s (by decide) (by have := v.val.toNat_lt; omega)]
    simp only [special_simple v rfl, Except.map, List.size_toByteArray]
  | .float b, d + 1, p, s, _ => by
    simp only [encode, encodeTo, push_eq, ByteArray.empty_append, item]
    unfold floatHead
    cases e : toHalf? b with
    | some h =>
      dsimp only
      rw [readHead_long p s (by decide) (by decide) (by decide) (by have := h.toNat_lt; simpa)]
      simp [special, Except.map, ofHalf_of_toHalf? e, List.size_toByteArray, longHead,
        length_argument]
    | none =>
      cases e' : toSingle? b with
      | some s' =>
        dsimp only
        rw [readHead_long p s (by decide) (by decide) (by decide)
          (by have := s'.toNat_lt; simpa)]
        simp [special, Except.map, ofSingle_of_toSingle? e', List.size_toByteArray, longHead,
          length_argument]
      | none =>
        dsimp only
        rw [readHead_long p s (by decide) (by decide) (by decide) (by have := b.toNat_lt; simpa)]
        simp [special, Except.map, List.size_toByteArray, longHead, length_argument]

theorem readMany_encodeList (cfg : Config) (hL : cfg.maxLength < 2 ^ 64) : (xs : List Cbor) →
    (d : Nat) → (q s : ByteArray) → (acc : List Cbor) → xs.all (fits d cfg.maxLength) = true →
    readMany (item cfg (q ++ encodeList xs ++ s) d) xs.length q.size acc =
      .ok (acc.reverse ++ xs, q.size + (encodeList xs).size)
  | [], _, q, s, acc, _ => by simp [readMany, encodeList, encodeAll]
  | x :: xs, d, q, s, acc, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [encodeList_cons, append_shift, List.length_cons, readMany, item_encode cfg hL x d q _ h.1]
    simp only
    rw [append_shift', ← ByteArray.size_append,
      readMany_encodeList cfg hL xs d (q ++ encode x) s (x :: acc) h.2]
    simp [ByteArray.size_append, Nat.add_assoc]

theorem readMany_encodeMap (cfg : Config) (hL : cfg.maxLength < 2 ^ 64) :
    (es : List (Cbor × Cbor)) → (d : Nat) → (q s : ByteArray) → (acc : List (Cbor × Cbor)) →
    es.all (fun e => fits d cfg.maxLength e.1 && fits d cfg.maxLength e.2) = true →
    readMany (readPair (item cfg (q ++ encodeMap es ++ s) d)) es.length q.size acc =
      .ok (acc.reverse ++ es, q.size + (encodeMap es).size)
  | [], _, q, s, acc, _ => by simp [readMany, encodeMap, encodeEntries]
  | e :: es, d, q, s, acc, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [encodeMap_cons, List.length_cons, readMany]
    have hb : q ++ (encode e.1 ++ encode e.2 ++ encodeMap es) ++ s =
        q ++ encode e.1 ++ (encode e.2 ++ (encodeMap es ++ s)) := by
      simp only [ByteArray.append_assoc]
    rw [hb, readPair, item_encode cfg hL e.1 d q _ h.1.1]
    simp only
    have hb2 : q ++ encode e.1 ++ (encode e.2 ++ (encodeMap es ++ s)) =
        q ++ encode e.1 ++ encode e.2 ++ (encodeMap es ++ s) := by
      simp only [ByteArray.append_assoc]
    rw [hb2, ← ByteArray.size_append, item_encode cfg hL e.2 d (q ++ encode e.1) _ h.1.2]
    simp only
    rw [← ByteArray.size_append, append_shift',
      readMany_encodeMap cfg hL es d (q ++ encode e.1 ++ encode e.2) s (e :: acc) h.2]
    simp [ByteArray.size_append, Nat.add_assoc]
end

theorem item_encode_whole (cfg : Config) (hL : cfg.maxLength < 2 ^ 64) (v : Cbor)
    (hv : v.fits cfg.maxDepth cfg.maxLength = true) :
    item cfg (encode v) cfg.maxDepth 0 = .ok (v, (encode v).size) := by
  have := item_encode cfg hL v cfg.maxDepth .empty .empty hv
  simpa [ByteArray.empty_append, ByteArray.append_empty] using this

/-- The decoder reads back what the encoder writes, taking any encoding or only preferred ones,
for every value within its limits. -/
theorem decode_encode (cfg : Config) (v : Cbor) (hL : cfg.maxLength < 2 ^ 64)
    (hv : v.fits cfg.maxDepth cfg.maxLength = true) (hsize : (encode v).size ≤ cfg.maxSize)
    (hacc : cfg.accept ≠ .deterministic) : decode cfg (encode v) = .ok v := by
  simp only [decode, show ¬cfg.maxSize < (encode v).size by omega, ↓reduceIte,
    item_encode_whole cfg hL v hv, ne_eq, not_true_eq_false]
  cases h : cfg.accept <;> simp_all

/-- The decoder that takes only deterministic encodings reads back a value whose maps are in
deterministic order, from its encoding. -/
theorem decode_deterministic_encode (cfg : Config) (v : Cbor) (hL : cfg.maxLength < 2 ^ 64)
    (hv : v.fits cfg.maxDepth cfg.maxLength = true) (hsize : (encode v).size ≤ cfg.maxSize)
    (hacc : cfg.accept = .deterministic) (hd : encodeDeterministic v = encode v) :
    decode cfg (encode v) = .ok v := by
  simp [decode, show ¬cfg.maxSize < (encode v).size by omega, item_encode_whole cfg hL v hv, hacc,
    hd]

/-! ### What a strict decoder takes -/

theorem encode_of_decode_preferred {cfg : Config} {bytes : ByteArray} {v : Cbor}
    (hacc : cfg.accept = .preferred) (h : decode cfg bytes = .ok v) : encode v = bytes := by
  unfold decode at h
  split at h; · cases h
  split at h; · cases h
  simp only [hacc] at h
  split at h
  · cases h
  split at h
  · cases h; assumption
  · cases h

theorem encodeDeterministic_of_decode {cfg : Config} {bytes : ByteArray} {v : Cbor}
    (hacc : cfg.accept = .deterministic) (h : decode cfg bytes = .ok v) :
    encodeDeterministic v = bytes := by
  unfold decode at h
  split at h; · cases h
  split at h; · cases h
  simp only [hacc] at h
  split at h
  · cases h
  split at h
  · cases h; assumption
  · cases h

/-- A strict decoder takes one encoding of each value: two inputs it reads as the same value are
the same bytes. -/
theorem eq_of_decode_strict {cfg : Config} {a b : ByteArray} {v : Cbor}
    (hacc : cfg.accept ≠ .wellFormed) (ha : decode cfg a = .ok v) (hb : decode cfg b = .ok v) :
    a = b := by
  cases h : cfg.accept with
  | wellFormed => exact absurd h hacc
  | preferred => rw [← encode_of_decode_preferred h ha, encode_of_decode_preferred h hb]
  | deterministic => rw [← encodeDeterministic_of_decode h ha, encodeDeterministic_of_decode h hb]

/-! ### Limits -/

theorem decode_tooLarge {cfg : Config} {bytes : ByteArray} (h : cfg.maxSize < bytes.size) :
    decode cfg bytes = .error .tooLarge := by
  simp [decode, h]

theorem size_of_readString {cfg : Config} {bytes : ByteArray} {n pos q : Nat} {b : ByteArray}
    (h : readString cfg bytes n pos = .ok (b, q)) : b.size ≤ cfg.maxLength ∧ b.size ≤ n := by
  unfold readString at h
  split at h; · cases h
  split at h; · cases h
  cases h
  simp only [ByteArray.size_extract]
  omega

theorem size_of_readChunks (cfg : Config) (bytes : ByteArray) (major : Nat) :
    ∀ (fuel pos : Nat) (acc b : ByteArray) (q : Nat), acc.size ≤ cfg.maxLength →
      readChunks cfg bytes major fuel pos acc = .ok (b, q) → b.size ≤ cfg.maxLength
  | 0, _, _, _, _, _, h => by simp [readChunks] at h
  | fuel + 1, pos, acc, b, q, hacc, h => by
    unfold readChunks at h
    split at h
    · cases h; exact hacc
    split at h; · cases h
    rename_i m info n next _
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i hn
    split at h; · cases h
    rename_i chunk next' hs
    split at h; · cases h
    refine size_of_readChunks cfg bytes major fuel next' (acc ++ chunk) b q ?_ h
    have := (size_of_readString hs).2
    rw [ByteArray.size_append]; omega

theorem readMany_ok {α : Type} {P : α → Prop} {read : Nat → Except Error (α × Nat)}
    (hr : ∀ pos x q, read pos = .ok (x, q) → P x) :
    ∀ (n pos : Nat) (acc xs : List α) (q : Nat), readMany read n pos acc = .ok (xs, q) →
      (∀ a ∈ acc, P a) → (∀ x ∈ xs, P x) ∧ xs.length = acc.length + n
  | 0, pos, acc, xs, q, h, hacc => by
    simp only [readMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun x hx => hacc x (List.mem_reverse.mp hx), by simp⟩
  | n + 1, pos, acc, xs, q, h, hacc => by
    unfold readMany at h
    split at h; · cases h
    rename_i x next hx
    have := readMany_ok hr n next (x :: acc) xs q h (by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hr _ _ _ hx
      · exact hacc a ha)
    refine ⟨this.1, ?_⟩
    rw [this.2, List.length_cons]; omega

theorem readUntilBreak_ok {α : Type} {P : α → Prop} {cfg : Config} {bytes : ByteArray}
    {read : Nat → Except Error (α × Nat)} (hr : ∀ pos x q, read pos = .ok (x, q) → P x) :
    ∀ (fuel pos count : Nat) (acc xs : List α) (q : Nat),
      readUntilBreak cfg bytes read fuel pos count acc = .ok (xs, q) → acc.length = count →
      count ≤ cfg.maxLength → (∀ a ∈ acc, P a) → (∀ x ∈ xs, P x) ∧ xs.length ≤ cfg.maxLength
  | 0, _, _, _, _, _, h, _, _, _ => by simp [readUntilBreak] at h
  | fuel + 1, pos, count, acc, xs, q, h, hlen, hcount, hacc => by
    unfold readUntilBreak at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun x hx => hacc x (List.mem_reverse.mp hx), by simp; omega⟩
    split at h; · cases h
    rename_i hlt
    split at h; · cases h
    rename_i x next hx
    exact readUntilBreak_ok hr fuel next (count + 1) (x :: acc) xs q h (by simp [hlen])
      (by omega) (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hr _ _ _ hx
        · exact hacc a ha)

theorem readItems_ok {α : Type} {P : α → Prop} {cfg : Config} {bytes : ByteArray}
    {read : Nat → Except Error (α × Nat)} (hr : ∀ pos x q, read pos = .ok (x, q) → P x)
    {info n pos q : Nat} {xs : List α} (h : readItems cfg bytes read info n pos = .ok (xs, q)) :
    (∀ x ∈ xs, P x) ∧ xs.length ≤ cfg.maxLength := by
  unfold readItems at h
  split at h
  · exact readUntilBreak_ok hr _ _ _ [] xs q h rfl (Nat.zero_le _) (by simp)
  split at h; · cases h
  have := readMany_ok hr n pos [] xs q h (by simp)
  exact ⟨this.1, by simp at this; omega⟩

theorem readPair_ok {α : Type} {P : α → Prop} {read : Nat → Except Error (α × Nat)}
    (hr : ∀ pos x q, read pos = .ok (x, q) → P x) {pos q : Nat} {e : α × α}
    (h : readPair read pos = .ok (e, q)) : P e.1 ∧ P e.2 := by
  unfold readPair at h
  split at h; · cases h
  rename_i k next hk
  split at h; · cases h
  rename_i v next' hv
  cases h
  exact ⟨hr _ _ _ hk, hr _ _ _ hv⟩

theorem size_of_readText {b : ByteArray} {v : Cbor} (h : readText b = .ok v) :
    ∃ s, v = .text s ∧ s.utf8ByteSize = b.size := by
  unfold readText at h
  split at h
  · rename_i s hs
    cases h
    refine ⟨s, rfl, ?_⟩
    unfold String.fromUTF8? at hs
    split at hs
    · cases hs; rfl
    · cases hs
  · cases h

theorem fits_of_special {info n : Nat} {v : Cbor} (h : special info n = .ok v) (d L : Nat) :
    v.fits (d + 1) L = true := by
  unfold special at h
  repeat (split at h; · (cases h <;> rfl))
  cases h

theorem fits_of_item (cfg : Config) (bytes : ByteArray) :
    ∀ (d pos : Nat) (v : Cbor) (q : Nat), item cfg bytes d pos = .ok (v, q) →
      v.fits d cfg.maxLength = true
  | 0, _, _, _, h => by simp [item] at h
  | d + 1, pos, v, q, h => by
    have ih := fits_of_item cfg bytes d
    unfold item at h
    split at h; · cases h
    rename_i major info n pos' _
    split at h
    · split at h; · cases h
      cases h; rfl
    · split at h; · cases h
      cases h; rfl
    · split at h; · cases h
      rename_i r b p2 hr
      cases h
      simp only [fits, decide_eq_true_eq]
      split at hr
      · exact size_of_readChunks cfg bytes 2 _ _ _ b _ (by simp [ByteArray.size_empty]) hr
      · exact (size_of_readString hr).1
    · split at h; · cases h
      rename_i r b p2 hr
      cases ht : readText b with
      | error e => simp [ht, Except.map] at h
      | ok w =>
        simp only [ht, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨s, rfl, hs⟩ := size_of_readText ht
        simp only [fits, decide_eq_true_eq, hs]
        split at hr
        · exact size_of_readChunks cfg bytes 3 _ _ _ b p2 (by simp [ByteArray.size_empty]) hr
        · exact (size_of_readString hr).1
    · split at h; · cases h
      rename_i xs p2 hr
      cases h
      obtain ⟨hall, hlen⟩ := readItems_ok (P := fun x => x.fits d cfg.maxLength = true)
        (fun pos x q hx => ih pos x q hx) hr
      simp [fits, hlen, List.all_eq_true.mpr hall]
    · split at h; · cases h
      rename_i es p2 hr
      cases h
      obtain ⟨hall, hlen⟩ := readItems_ok
        (P := fun e => e.1.fits d cfg.maxLength = true ∧ e.2.fits d cfg.maxLength = true)
        (fun pos e q he => readPair_ok (fun pos x q hx => ih pos x q hx) he) hr
      simp only [fits, Bool.and_eq_true, decide_eq_true_eq, hlen, true_and, List.all_eq_true]
      exact fun e he => ⟨(hall e he).1, (hall e he).2⟩
    · split at h; · cases h
      split at h; · cases h
      rename_i w p2 hw
      cases h
      exact ih _ _ _ hw
    · cases hs : special info n with
      | error e => simp [hs, Except.map] at h
      | ok w =>
        simp only [hs, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact fits_of_special hs d cfg.maxLength

/-- What the decoder reads is within its depth and its length. -/
theorem fits_of_decode {cfg : Config} {bytes : ByteArray} {v : Cbor}
    (h : decode cfg bytes = .ok v) : v.fits cfg.maxDepth cfg.maxLength = true := by
  unfold decode at h
  split at h; · cases h
  split at h; · cases h
  rename_i w pos hw
  have := fits_of_item cfg bytes _ _ _ _ hw
  split at h; · cases h
  split at h
  · cases h; exact this
  · split at h
    · cases h; exact this
    · cases h
  · split at h
    · cases h; exact this
    · cases h

theorem size_of_decode {cfg : Config} {bytes : ByteArray} {v : Cbor}
    (h : decode cfg bytes = .ok v) : bytes.size ≤ cfg.maxSize := by
  unfold decode at h
  split at h
  · cases h
  · omega

end Lanes.Cbor
