/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Mime.Multipart
public import Lanes.Lib.Mime.MediaTypeSound
public import Lanes.Proof.ByteArray
public import Lanes.Proof.Utf8

/-!
What `Lanes.Multipart` is proved to do. `parse` reads back what `write` writes
(`Multipart.parse_write`), for parts that are `valid` and `clear` of the delimiter, within the
limits; and it refuses what is over its limits: a body larger than `bytes_max`
(`Multipart.parse_tooLarge`), more parts than `parts_max` (`Multipart.length_le_of_parse`), a
part with more header lines than `headers_max` (`Multipart.headers_le_of_parse`).

The proofs read byte arrays as lists: `find` finds the first place where a needle is a prefix of
the rest (`Multipart.find_eq_some`), and what `write` writes, after a line break, is the
delimiter and then each part, its bytes and the next delimiter, then `--` (`Multipart.frame`).
-/

@[expose] public section

namespace Lanes.Multipart

open Http (tokenChar plain trimOws ows)

/-! ### Bytes as lists -/

theorem toList_extract (b : ByteArray) (i j : Nat) :
    (b.extract i j).data.toList = (b.data.toList.drop i).take (j - i) := by
  simp [ByteArray.data_extract, Array.toList_extract]

theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length :=
  Array.length_toList.symm

theorem getElem?_toList (b : ByteArray) (i : Nat) : b[i]? = b.data.toList[i]? :=
  getElem?_data b i

theorem prefix_of_append {l a b : List UInt8} (hl : l.length ≤ a.length) (h : l <+: a ++ b) :
    l <+: a := by
  rw [List.prefix_iff_eq_take] at h ⊢
  rw [List.take_append_of_le_length hl] at h
  exact h

/-- `matchesAt` is a prefix of the rest. -/
theorem matchesAt_iff {hay needle : ByteArray} (hn : 0 < needle.size) (i : Nat) :
    matchesAt hay needle i = true ↔ needle.data.toList <+: hay.data.toList.drop i := by
  rw [List.prefix_iff_eq_take]
  simp only [matchesAt, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨-, h⟩
    have := congrArg (fun b : ByteArray => b.data.toList) h
    simp only [toList_extract, Nat.add_sub_cancel_left] at this
    rw [← size_eq_length]
    exact this.symm
  · intro h
    refine ⟨?_, eq_of_toList ?_⟩
    · rw [getElem?_toList, getElem?_toList, h, List.getElem?_take]
      rw [← size_eq_length]
      simp [hn]
    · rw [toList_extract, Nat.add_sub_cancel_left, size_eq_length]
      exact h.symm

theorem bound_of_prefix {hay needle : ByteArray} {j : Nat} (hn : 0 < needle.size)
    (hm : needle.data.toList <+: hay.data.toList.drop j) : j + needle.size ≤ hay.size := by
  have := hm.length_le
  simp only [List.length_drop] at this
  rw [size_eq_length] at hn ⊢
  rw [size_eq_length]
  omega

/-- `find` gives the first place from `i` where the needle is. -/
theorem find_eq_some {hay needle : ByteArray} (hn : 0 < needle.size) {i j : Nat} (hij : i ≤ j)
    (hm : needle.data.toList <+: hay.data.toList.drop j)
    (hno : ∀ k, i ≤ k → k < j → ¬ needle.data.toList <+: hay.data.toList.drop k) :
    find hay needle i = some j := by
  have hb := bound_of_prefix hn hm
  induction h : j - i generalizing i with
  | zero =>
    have : i = j := by omega
    subst this
    rw [find, dite_eq_left ⟨by omega, by omega⟩, ite_eq_left ((matchesAt_iff hn i).mpr hm)]
  | succ d ih =>
    rw [find, dite_eq_left ⟨by omega, by omega⟩,
      ite_eq_right (fun e => hno i (Nat.le_refl _) (by omega) ((matchesAt_iff hn i).mp e))]
    exact ih (by omega) (fun k hk1 hk2 => hno k (by omega) hk2) (by omega)

/-! ### A header line -/

theorem dropWhile_append_of {p : Char → Bool} {a : List Char} (b : List Char)
    (h : ∀ c ∈ a, p c = true) : (a ++ b).dropWhile p = b.dropWhile p := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    rw [List.cons_append, List.dropWhile_cons, ite_eq_left (h c (by simp))]
    exact ih fun d hd => h d (by simp [hd])

theorem takeWhile_append_of {p : Char → Bool} {a : List Char} (b : List Char)
    (h : ∀ c ∈ a, p c = true) : (a ++ b).takeWhile p = a ++ b.takeWhile p := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    rw [List.cons_append, List.takeWhile_cons, ite_eq_left (h c (by simp)), ih fun d hd => h d (by simp [hd])]
    rfl

theorem trimOws_space (v : List Char) : trimOws (' ' :: v) = trimOws v := by
  simp [trimOws, show ows ' ' = true by decide]

theorem ne_colon_of_tokenChar {c : Char} (h : tokenChar c = true) : (c != ':') = true := by
  have : tokenChar ':' = false := by decide
  simp only [bne_iff_ne, ne_eq]
  rintro rfl
  simp_all

/-- A header line as `write` writes it reads back. -/
theorem field?_line {n v : String} (hn : MediaType.isToken n = true)
    (hl : Url.lower n.toList = n.toList) (hv : v.toList.all plain = true)
    (ht : trimOws v.toList = v.toList) : field? (n ++ ": " ++ v).toList = some (n, v) := by
  simp only [MediaType.isToken, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hn
  have hne : n.toList ≠ [] := by simpa using hn.1
  have hc : ∀ c ∈ n.toList, (c != ':') = true := fun c h => ne_colon_of_tokenChar (hn.2 c h)
  have e : (n ++ ": " ++ v).toList = n.toList ++ (':' :: ' ' :: v.toList) := by simp
  rw [field?, e, dropWhile_append_of _ hc]
  simp only [List.dropWhile_cons, show (':' != ':') = false by decide, Bool.false_eq_true,
    ↓reduceIte]
  rw [takeWhile_append_of _ hc]
  simp only [List.takeWhile_cons, show (':' != ':') = false by decide, Bool.false_eq_true,
    ↓reduceIte, List.append_nil, trimOws_space, ht, hl, String.ofList_toList]
  rw [ite_eq_left ⟨hne, List.all_eq_true.mpr hn.2, by simp [hv]; decide⟩]

/-! ### Header lines -/

/-- The bytes of a string. -/
abbrev bytesOf (s : String) : List UInt8 := s.toUTF8.data.toList

theorem bytesOf_eq (s : String) : bytesOf s = s.toList.flatMap String.utf8EncodeChar := by
  simp [bytesOf, data_toList_toByteArray]

theorem bytesOf_append (a b : String) : bytesOf (a ++ b) = bytesOf a ++ bytesOf b := by
  simp [bytesOf_eq]

theorem bytesOf_crlf : bytesOf "\r\n" = [13, 10] := by decide

theorem headerText_cons (n v : String) (hs : List (String × String)) :
    bytesOf (headerText ((n, v) :: hs)) =
      bytesOf (n ++ ": " ++ v) ++ [13, 10] ++ bytesOf (headerText hs) := by
  simp only [headerText, List.map_cons, String.join_cons]
  rw [bytesOf_append, bytesOf_append, bytesOf_crlf]

theorem headerText_nil : bytesOf (headerText []) = [] := by simp [headerText]

theorem fromUTF8?_bytesOf {b : ByteArray} {s : String} (h : b.data.toList = bytesOf s) :
    String.fromUTF8? b = some s := by
  rw [eq_of_toList h, String.toUTF8_eq_toByteArray]
  exact fromUTF8?_toByteArray s

/-- A character that is no line break has none in its bytes. -/
theorem ne_cr_of_mem {s : String} (h : ∀ c ∈ s.toList, c ≠ '\r') : ∀ b ∈ bytesOf s, b ≠ 13 := by
  rw [bytesOf_eq]
  intro b hb e
  obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
  subst e
  have := utf8EncodeChar_ascii hb (by decide)
  exact h c hc (Char.ext (by
    have : c.toNat = 13 := by simpa using this.symm
    simp only [Char.toNat] at this
    exact UInt32.toNat_inj.mp (by simpa using this)))

/-- What a header line must be to read back. -/
def HeaderOk (h : String × String) : Prop :=
  MediaType.isToken h.1 = true ∧ Url.lower h.1.toList = h.1.toList ∧ h.2.toList.all plain = true ∧
    trimOws h.2.toList = h.2.toList

theorem line_ne_cr {h : String × String} (ok : HeaderOk h) :
    ∀ b ∈ bytesOf (h.1 ++ ": " ++ h.2), b ≠ 13 := by
  obtain ⟨hn, -, hv, -⟩ := ok
  apply ne_cr_of_mem
  intro c hc e
  subst e
  simp only [String.toList_append, List.mem_append] at hc
  simp only [MediaType.isToken, Bool.and_eq_true, List.all_eq_true] at hn hv
  rcases hc with (h1 | h2) | h3
  · exact absurd (hn.2 _ h1) (by decide)
  · revert h2; decide
  · exact absurd (hv _ h3) (by decide)

theorem line_ne_nil (h : String × String) : bytesOf (h.1 ++ ": " ++ h.2) ≠ [] := by
  rw [bytesOf_append, bytesOf_append]
  have : bytesOf ": " = [58, 32] := by decide
  simp [this]

/-- The first line break from `pos` in a list that holds none before `m` more bytes. -/
theorem find_crlf {data : ByteArray} {pos : Nat} {line rest : List UInt8}
    (hl : ∀ b ∈ line, b ≠ 13) (hd : data.data.toList.drop pos = line ++ [13, 10] ++ rest) :
    find data crlf pos = some (pos + line.length) := by
  have hn : 0 < crlf.size := by decide
  have hcrlf : crlf.data.toList = [13, 10] := rfl
  apply find_eq_some hn (Nat.le_add_right _ _)
  · rw [hcrlf, ← List.drop_drop, hd]
    simp
  · intro k hk1 hk2 hp
    rw [hcrlf] at hp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk1
    rw [← List.drop_drop, hd, List.append_assoc, List.drop_append_of_le_length (by omega)] at hp
    have hm : m < line.length := by omega
    obtain ⟨t, ht⟩ := hp
    have := congrArg List.head? ht
    rw [List.head?_append, List.head?_append, List.head?_drop, List.getElem?_eq_getElem hm] at this
    simp at this
    exact hl _ (List.getElem_mem hm) this.symm

theorem headers_of {data : ByteArray} (R : List UInt8) : (hs : List (String × String)) →
    (∀ h ∈ hs, HeaderOk h) → ∀ (fuel pos : Nat), hs.length ≤ fuel →
    data.data.toList.drop pos = bytesOf (headerText hs) ++ [13, 10] ++ R →
    headers data fuel pos = .ok (hs, pos + (bytesOf (headerText hs)).length + 2)
  | [], _, fuel, pos, _, hd => by
    rw [headerText_nil] at hd ⊢
    rw [headers, find_crlf (line := []) (by simp) (by simpa using hd)]
    simp
  | (n, v) :: hs, hok, fuel, pos, hf, hd => by
    have ok := hok (n, v) (by simp)
    rw [headerText_cons] at hd ⊢
    have hd' : data.data.toList.drop pos = bytesOf (n ++ ": " ++ v) ++ [13, 10]
        ++ (bytesOf (headerText hs) ++ [13, 10] ++ R) := by
      rw [hd]; simp
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hne : 0 < (bytesOf (n ++ ": " ++ v)).length := List.length_pos_iff.mpr (line_ne_nil (n, v))
    rw [headers, find_crlf (line_ne_cr ok) hd']
    simp only [show ¬(pos + (bytesOf (n ++ ": " ++ v)).length = pos) by omega, ↓reduceIte]
    have hx : (data.extract pos (pos + (bytesOf (n ++ ": " ++ v)).length)).data.toList
        = bytesOf (n ++ ": " ++ v) := by
      rw [toList_extract, hd', Nat.add_sub_cancel_left]; simp
    rw [fromUTF8?_bytesOf hx]
    simp only [Option.bind_some, field?_line ok.1 ok.2.1 ok.2.2.1 ok.2.2.2]
    have hr : data.data.toList.drop (pos + (bytesOf (n ++ ": " ++ v)).length + 2)
        = bytesOf (headerText hs) ++ [13, 10] ++ R := by
      rw [← List.drop_drop, ← List.drop_drop, hd']; simp
    rw [headers_of R hs (fun h hh => hok h (by simp [hh])) f _ (by simpa using hf) hr]
    simp only [Except.map, List.length_append, List.length_cons, List.length_nil]
    congr 2
    omega

/-- A part reads back from its bytes. -/
theorem part_of (limits : Limits) (p : Part) (ok : ∀ h ∈ p.headers, HeaderOk h)
    (hl : p.headers.length ≤ limits.headers_max) : part limits p.bytes = .ok p := by
  have hd : p.bytes.data.toList.drop 0
      = bytesOf (headerText p.headers) ++ [13, 10] ++ p.body.data.toList := by
    simp [Part.bytes, crlf]
  have hL : p.bytes.data.toList
      = bytesOf (headerText p.headers) ++ [13, 10] ++ p.body.data.toList := by simpa using hd
  have hne : p.bytes.size ≠ 0 := by rw [size_eq_length, hL]; simp
  rw [part, ite_eq_right hne, headers_of _ p.headers ok _ 0 hl hd]
  simp only [Except.map, Except.ok.injEq]
  congr
  apply eq_of_toList
  rw [toList_extract, size_eq_length p.bytes, hL, List.drop_left' (by simp),
    List.take_of_length_le (by simp; omega)]

/-! ### The frame -/

/-- What follows a delimiter in what `write` writes: each part, its bytes and the next delimiter,
then `--` and a line break. -/
def tail (boundary : String) : List Part → List UInt8
  | [] => [45, 45, 13, 10]
  | p :: ps => [13, 10] ++ p.bytes.data.toList ++ (delimiter boundary).data.toList ++ tail boundary ps

theorem foldl_write (o : ByteArray) : (ps : List Part) → (acc : ByteArray) →
    (ps.foldl (fun acc p => acc ++ o ++ crlf ++ p.bytes ++ crlf) acc).data.toList
      = acc.data.toList ++ ps.flatMap fun p =>
          o.data.toList ++ [13, 10] ++ p.bytes.data.toList ++ [13, 10]
  | [], acc => by simp
  | p :: ps, acc => by
    rw [List.foldl_cons, foldl_write o ps]
    simp [crlf]

theorem delimiter_toList (boundary : String) :
    (delimiter boundary).data.toList = [13, 10] ++ (dashes ++ boundary.toUTF8).data.toList := by
  simp [delimiter, crlf]

theorem tail_eq (boundary : String) (o : List UInt8)
    (ho : (delimiter boundary).data.toList = [13, 10] ++ o) : (ps : List Part) →
    [13, 10] ++ ((ps.flatMap fun p => o ++ [13, 10] ++ p.bytes.data.toList ++ [13, 10])
      ++ (o ++ [45, 45, 13, 10])) = [13, 10] ++ o ++ tail boundary ps
  | [] => by simp [tail]
  | p :: ps => by
    have ih := tail_eq boundary o ho ps
    simp only [List.flatMap_cons, tail, ho, List.append_assoc, List.cons_append, List.nil_append,
      List.cons.injEq, true_and] at ih ⊢
    rw [ih]

/-- After a line break, what `write` writes is the delimiter and then `tail`. -/
theorem frame (boundary : String) (ps : List Part) :
    (crlf ++ write boundary ps).data.toList = (delimiter boundary).data.toList ++ tail boundary ps := by
  have he : (ByteArray.empty).data.toList = [] := rfl
  have hc : crlf.data.toList = [13, 10] := rfl
  have hd : dashes.data.toList = [45, 45] := rfl
  rw [delimiter_toList, ← tail_eq boundary _ (delimiter_toList boundary) ps]
  simp only [write, toList_append, foldl_write, he, hc, hd, List.nil_append, List.append_assoc]
  rfl

theorem clear_go {hay needle : ByteArray} : ∀ n, clear.go hay needle n = true ↔
    ∀ k < n, matchesAt hay needle k = false
  | 0 => by simp [clear.go]
  | n + 1 => by
    rw [clear.go, Bool.and_eq_true, clear_go n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      by_cases e : k = n
      · subst e; simpa using h1
      · exact h2 k (by omega)
    · intro h
      exact ⟨by simpa using h n (by omega), fun k hk => h k (by omega)⟩

theorem delimiter_size (boundary : String) : 0 < (delimiter boundary).size := by
  rw [delimiter, ByteArray.size_append, ByteArray.size_append]
  have : crlf.size = 2 := rfl
  omega

/-- The delimiter is not in a clear part before its end. -/
theorem not_prefix_of_clear {boundary : String} {p : Part} (hc : clear boundary p = true)
    {m : Nat} (hm : m < p.bytes.size) (T : List UInt8) :
    ¬ (delimiter boundary).data.toList <+:
      (p.bytes.data.toList ++ (delimiter boundary).data.toList ++ T).drop m := by
  intro h
  have hno := (clear_go _).mp hc m hm
  rw [List.drop_append_of_le_length (by simp; omega)] at h
  have h' := prefix_of_append (by simp; omega) h
  rw [← toList_append, ← matchesAt_iff (delimiter_size boundary)] at h'
  simp_all

/-- What a part needs to read back: its headers read back, the delimiter is not in it, and it
has no more header lines than the limit. -/
def Fits (limits : Limits) (boundary : String) (p : Part) : Prop :=
  (∀ h ∈ p.headers, HeaderOk h) ∧ clear boundary p = true ∧ p.headers.length ≤ limits.headers_max

theorem skipBlanks_cr {data : ByteArray} {pos : Nat} {rest : List UInt8}
    (h : data.data.toList.drop pos = 13 :: rest) : skipBlanks data pos = pos := by
  have hp : data[pos]? = some 13 := by
    rw [getElem?_toList, ← Nat.add_zero pos, ← List.getElem?_drop, h]; rfl
  obtain ⟨hlt, he⟩ := getElem_of_getElem? hp
  rw [skipBlanks, dite_eq_left hlt, he]
  simp

theorem parts_of (limits : Limits) (boundary : String) (data : ByteArray) : (ps : List Part) →
    (∀ p ∈ ps, Fits limits boundary p) → ∀ (fuel pos : Nat), ps.length ≤ fuel →
    data.data.toList.drop pos = tail boundary ps →
    parts limits (delimiter boundary) data fuel pos = .ok ps
  | [], _, fuel, pos, _, hd => by
    have hd2 : data.data.toList.drop (pos + 2) = 13 :: [10] := by
      rw [← List.drop_drop, hd]; rfl
    have hends : ends data (pos + 2) = true := by
      rw [ends, skipBlanks_cr hd2, (matchesAt_iff (by decide) _).mpr (by rw [hd2]; exact ⟨[], rfl⟩)]
      simp
    rw [parts, ite_eq_left ((matchesAt_iff (by decide) pos).mpr (by rw [hd]; exact ⟨[13, 10], rfl⟩)),
      ite_eq_left hends]
  | p :: ps, hfit, fuel, pos, hf, hd => by
    obtain ⟨hok, hc, hh⟩ := hfit p (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hd' : data.data.toList.drop pos = 13 :: 10 :: (p.bytes.data.toList
        ++ (delimiter boundary).data.toList ++ tail boundary ps) := by
      rw [hd, tail]; simp
    have hdash : matchesAt data dashes pos = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨t, ht⟩ := (matchesAt_iff (by decide) pos).mp h
      rw [hd'] at ht
      cases ht
    have hcrlf : matchesAt data crlf pos = true :=
      (matchesAt_iff (by decide) pos).mpr (by rw [hd']; exact ⟨_, rfl⟩)
    have hfind : find data (delimiter boundary) (pos + 2)
        = some (pos + 2 + p.bytes.data.toList.length) := by
      apply find_eq_some (delimiter_size boundary) (Nat.le_add_right _ _)
      · rw [← List.drop_drop, ← List.drop_drop, hd']
        simp
      · intro k hk1 hk2
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk1
        rw [← List.drop_drop, ← List.drop_drop, hd']
        simp only [List.drop_succ_cons, List.drop_zero]
        exact not_prefix_of_clear hc (by rw [size_eq_length]; omega) _
    have hx : data.extract (pos + 2) (pos + 2 + p.bytes.data.toList.length) = p.bytes := by
      apply eq_of_toList
      rw [toList_extract, ← List.drop_drop, hd', Nat.add_sub_cancel_left]
      simp
    have hr : data.data.toList.drop (pos + 2 + p.bytes.data.toList.length + (delimiter boundary).size)
        = tail boundary ps := by
      rw [← List.drop_drop, ← List.drop_drop, ← List.drop_drop, hd', size_eq_length]
      simp
    rw [parts, ite_eq_right (by simp [hdash]), skipBlanks_cr hd',
      ite_eq_right (by simp [hcrlf])]
    simp only [hfind, hx, part_of limits p hok hh]
    rw [parts_of limits boundary data ps (fun q hq => hfit q (by simp [hq])) f _
      (by simpa using hf) hr]
    rfl

theorem headerOk_of_valid {p : Part} (h : p.valid = true) : ∀ hd ∈ p.headers, HeaderOk hd := by
  intro hd hm
  have := List.all_eq_true.mp h hd hm
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- `parse` reads back what `write` writes: parts whose header names are lowercase tokens and
whose values are plain text with no blank at either end (`Part.valid`), in which the delimiter is
nowhere (`clear`), within the limits. -/
theorem parse_write (limits : Limits) (boundary : String) (ps : List Part)
    (hsize : (write boundary ps).size ≤ limits.bytes_max) (hparts : ps.length ≤ limits.parts_max)
    (hvalid : ∀ p ∈ ps, p.valid = true) (hclear : ∀ p ∈ ps, clear boundary p = true)
    (hheaders : ∀ p ∈ ps, p.headers.length ≤ limits.headers_max) :
    parse limits boundary (write boundary ps) = .ok ps := by
  have hL := frame boundary ps
  rw [parse, ite_eq_right (by omega)]
  simp only
  rw [find_eq_some (delimiter_size boundary) (Nat.le_refl 0) (by rw [hL]; simp) (by omega)]
  simp only
  apply parts_of limits boundary _ ps
    (fun p hp => ⟨headerOk_of_valid (hvalid p hp), hclear p hp, hheaders p hp⟩) _ _ hparts
  rw [hL, Nat.zero_add, size_eq_length, List.drop_left]

/-! ### Limits -/

/-- A body larger than `bytes_max` is refused. -/
theorem parse_tooLarge {limits : Limits} {boundary : String} {body : ByteArray}
    (h : limits.bytes_max < body.size) : parse limits boundary body = .error .tooLarge := by
  rw [parse, ite_eq_left h]

theorem length_le_of_headers {data : ByteArray} : ∀ {fuel pos : Nat}
    {hs : List (String × String)} {start : Nat}, headers data fuel pos = .ok (hs, start) →
      hs.length ≤ fuel
  | fuel, pos, hs, start, h => by
    rw [headers] at h
    split at h
    · cases h
    · split at h
      · cases h; simp
      · cases fuel with
        | zero => cases h
        | succ f =>
          simp only at h
          split at h
          · cases h
          · simp only [Except.map] at h
            split at h
            · cases h
            · rename_i v hv
              cases h
              have := length_le_of_headers hv
              simp; omega

theorem headers_le_of_part {limits : Limits} {bytes : ByteArray} {p : Part}
    (h : part limits bytes = .ok p) : p.headers.length ≤ limits.headers_max := by
  unfold part at h
  split at h
  · cases h; simp
  cases hr : headers bytes limits.headers_max 0 with
  | error => simp [hr, Except.map] at h
  | ok r =>
    simp only [hr, Except.map, Except.ok.injEq] at h
    subst h
    exact length_le_of_headers hr

theorem length_le_of_parts {limits : Limits} {delim data : ByteArray} :
    ∀ {fuel pos : Nat} {ps : List Part}, parts limits delim data fuel pos = .ok ps →
      ps.length ≤ fuel ∧ ∀ p ∈ ps, p.headers.length ≤ limits.headers_max
  | fuel, pos, ps, h => by
    rw [parts] at h
    split at h
    · split at h
      · cases h; simp
      · cases h
    · simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases fuel with
          | zero => cases h
          | succ f =>
            simp only at h
            split at h
            · cases h
            · rename_i q hq
              simp only [Except.map] at h
              split at h
              · cases h
              · rename_i rest hr
                cases h
                have := length_le_of_parts hr
                refine ⟨by simp; omega, ?_⟩
                intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · exact headers_le_of_part hq
                · exact this.2 p hp

/-- `parse` accepts at most `parts_max` parts. -/
theorem length_le_of_parse {limits : Limits} {boundary : String} {body : ByteArray}
    {ps : List Part} (h : parse limits boundary body = .ok ps) : ps.length ≤ limits.parts_max := by
  unfold parse at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
    · exact (length_le_of_parts h).1

/-- `parse` accepts no part with more than `headers_max` header lines. -/
theorem headers_le_of_parse {limits : Limits} {boundary : String} {body : ByteArray}
    {ps : List Part} (h : parse limits boundary body = .ok ps) :
    ∀ p ∈ ps, p.headers.length ≤ limits.headers_max := by
  unfold parse at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
    · exact (length_le_of_parts h).2

/-! ### Forms -/

theorem join_param : (ps : List (String × String)) →
    (String.join (ps.map fun (n, v) => param n v)).toList = ps.flatMap MediaType.paramChars
  | [] => by simp
  | (n, v) :: ps => by
    simp only [List.map_cons, String.join_cons, String.toList_append, List.flatMap_cons,
      join_param ps]
    simp [param, MediaType.paramChars]

theorem disposition?_of {p : Part} {ps : List (String × String)}
    (hl : p.headers.lookup "content-disposition"
      = some ("form-data" ++ String.join (ps.map fun (n, v) => param n v)))
    (hp : ps.all fun (n, v) => MediaType.isToken n && v.toList.all Http.isQuotable)
    (hn : ∀ q ∈ ps, Url.lower q.1.toList = q.1.toList) :
    p.disposition? = some ("form-data", ps) := by
  have hchars : ("form-data" ++ String.join (ps.map fun (n, v) => param n v)).toList
      = "form-data".toList ++ ps.flatMap MediaType.paramChars := by
    rw [String.toList_append, join_param]
  have hrest : MediaType.EndsToken (ps.flatMap MediaType.paramChars) := by
    cases ps with
    | nil => exact .inl rfl
    | cons q qs =>
      exact .inr ⟨';', ' ' :: (q.1.toList ++ '=' :: (MediaType.valueChars q.2
        ++ qs.flatMap MediaType.paramChars)), by simp [MediaType.paramChars], by decide⟩
  have ht := MediaType.token_append (t := "form-data".toList) _ (by decide) hrest
  unfold Part.disposition?
  rw [hl]
  simp only [Option.bind_eq_bind, Option.bind_some, hchars, ht, MediaType.parseParams_chars ps hp,
    List.map_map]
  have hl' : String.ofList (Url.lower "form-data".toList) = "form-data" := by decide
  rw [hl']
  show some _ = some _
  congr 2
  conv => rhs; rw [← List.map_id ps]
  apply List.map_congr_left
  intro ⟨n, v⟩ hm
  simp [hn _ hm]

/-- A text field's name reads back. -/
theorem name?_field {name value : String} (hq : name.toList.all Http.isQuotable) :
    (Part.field name value).name? = some name := by
  rw [Part.name?, disposition?_of (ps := [("name", name)]) (by simp [Part.field]) (by simp [hq]; decide)
    (by simp; decide)]
  rfl

/-- A file's name and file name read back. -/
theorem filename?_file {name filename contentType : String} {body : ByteArray}
    (hn : name.toList.all Http.isQuotable) (hf : filename.toList.all Http.isQuotable) :
    (Part.file name filename contentType body).name? = some name ∧
      (Part.file name filename contentType body).filename? = some filename := by
  have hd := disposition?_of (p := Part.file name filename contentType body)
    (ps := [("name", name), ("filename", filename)]) (by simp [Part.file, String.append_assoc])
    (by simp [hn, hf]; decide) (by simp; decide)
  constructor
  · rw [Part.name?, hd]; rfl
  · rw [Part.filename?, hd]; rfl

end Lanes.Multipart
