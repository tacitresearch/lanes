/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.List
public import Lanes.Http.Wire

/-!
What the reader of `Lanes.Http.Wire` does, for every response and every limit:

- it reads a response written by `Response.wire` or `Response.wireChunked` back as written, as
  soon as its last byte is there, whatever follows it and whether or not the connection has
  ended (`Response.read_wire`, `Response.read_wireChunked`);
- on every strict start of one, it waits while the connection is open and refuses once it has
  ended (`Response.read_wire_extract`, `Response.read_wireChunked_extract`);
- it asks for more only while the connection is open and at most `limit` bytes have arrived
  (`Response.read_more`), and a response it gives ends within `limit` bytes, its body too
  (`Response.read_some`);
- an answer it gives while the connection is open is final (`Response.read_append`).

The head is found through a model of `headEnd` on lists (`blankAt`), whose first blank line in
the bytes of a head is its end because UTF-8 writes a CR only for a CR. What is read from fewer
bytes is that more is needed or what is read from all of them (`readFrom_extract`); with
`readFrom_bound`, that is why a strict start of a whole response waits.
-/

@[expose] public section

namespace Lanes.Http

private theorem ne_13_of_ne_cr {cs : List Char} (h : ∀ c ∈ cs, c ≠ '\r') :
    ∀ b ∈ cs.flatMap String.utf8EncodeChar, b ≠ 13 := by
  intro b hb e
  obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp hb
  have := utf8EncodeChar_ascii hbc (by rw [e]; decide)
  rw [e] at this
  exact h c hc (Char.toNat_inj.mp this.symm)

private def blankAt : List UInt8 → Option Nat
  | [] => none
  | b :: rest =>
    if (b :: rest).take 4 = [13, 10, 13, 10] then some 4 else (blankAt rest).map (· + 1)

private theorem blankAt_short : ∀ {l : List UInt8}, l.length < 4 → blankAt l = none
  | [], _ => rfl
  | b :: rest, h => by
    have : (b :: rest).take 4 ≠ [13, 10, 13, 10] := by
      rw [List.take_of_length_le (by omega)]
      intro e
      have := congrArg List.length e
      simp at this h
      omega
    simp only [blankAt, this, ↓reduceIte, blankAt_short (l := rest) (by simp at h; omega),
      Option.map_none]

private theorem headEnd_eq (bytes : ByteArray) (pos : Nat) :
    headEnd bytes pos = (blankAt (bytes.data.toList.drop pos)).map (pos + ·) := by
  fun_induction headEnd bytes pos with
  | case1 pos h hblank =>
    have hl : pos + 3 < bytes.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons (by omega), blankAt]
    simp only [Bool.and_eq_true, beq_iff_eq] at hblank
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hblank
    have : (bytes.data.toList[pos] :: bytes.data.toList.drop (pos + 1)).take 4
        = [13, 10, 13, 10] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega)]
      simp only [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
      simp [h0, h1, h2, h3]
    simp only [this, ↓reduceIte]
    rfl
  | case2 pos h hblank ih =>
    have hl : pos + 3 < bytes.data.toList.length := by simpa using h
    rw [ih, List.drop_eq_getElem_cons (i := pos) (by omega), blankAt]
    have : (bytes.data.toList[pos] :: bytes.data.toList.drop (pos + 1)).take 4
        ≠ [13, 10, 13, 10] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega)]
      simp only [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
      simpa using hblank
    simp only [this, ↓reduceIte, Option.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply]
    omega
  | case3 pos h =>
    have hl : bytes.data.toList.length ≤ pos + 3 := by simp at h ⊢; omega
    rw [blankAt_short (by rw [List.length_drop]; omega)]
    rfl

private theorem blankAt_append_of_ne {x : List UInt8} (t : List UInt8) (h : ∀ b ∈ x, b ≠ 13) :
    blankAt (x ++ t) = (blankAt t).map (· + x.length) := by
  induction x with
  | nil => simp
  | cons b x ih =>
    have hb := h b List.mem_cons_self
    have : (b :: (x ++ t)).take 4 ≠ [13, 10, 13, 10] := by
      intro e
      simp at e
      exact hb e.1
    rw [List.cons_append, blankAt, ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
    simp only [this, ↓reduceIte, Option.map_map]
    congr 1

private theorem blankAt_crlf {t : List UInt8} (h : t.head? ≠ some 13) :
    blankAt (13 :: 10 :: t) = (blankAt t).map (· + 2) := by
  have h1 : (13 :: 10 :: t : List UInt8).take 4 ≠ [13, 10, 13, 10] := by
    intro e
    cases t with
    | nil => simp at e
    | cons c t => simp at e h; exact h e.1
  have h2 : (10 :: t : List UInt8).take 4 ≠ [13, 10, 13, 10] := by
    intro e; simp at e
  rw [blankAt, blankAt]
  simp only [h1, h2, ↓reduceIte, Option.map_map]
  congr 1

private theorem blankAt_blank (t : List UInt8) : blankAt (13 :: 10 :: 13 :: 10 :: t) = some 4 := by
  simp [blankAt]

private theorem blankAt_le {l : List UInt8} {m : Nat} (h : blankAt l = some m) :
    4 ≤ m ∧ m ≤ l.length := by
  induction l generalizing m with
  | nil => simp [blankAt] at h
  | cons b rest ih =>
    rw [blankAt] at h
    split at h
    · rename_i e
      cases h
      have := congrArg List.length e
      simp at this
      simp
      omega
    · cases hr : blankAt rest with
      | none => simp [hr] at h
      | some k =>
        simp [hr] at h
        have := ih hr
        simp
        omega

private theorem blankAt_take {l : List UInt8} {m : Nat} (h : blankAt l = some m) (n : Nat) :
    blankAt (l.take n) = if m ≤ n then some m else none := by
  induction l generalizing m n with
  | nil => simp [blankAt] at h
  | cons b rest ih =>
    rw [blankAt] at h
    split at h
    · rename_i e
      cases h
      by_cases hn : 4 ≤ n
      · have : (List.take n (b :: rest)).take 4 = [13, 10, 13, 10] := by
          rw [List.take_take, Nat.min_eq_left hn, e]
        cases n with
        | zero => omega
        | succ n =>
          rw [List.take_succ_cons, blankAt, ← List.take_succ_cons]
          simp only [eq_true this, ↓reduceIte, hn]
      · rw [blankAt_short (by simp; omega)]
        simp [hn]
    · rename_i e
      cases hr : blankAt rest with
      | none => simp [hr] at h
      | some k =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        cases n with
        | zero => simp [blankAt]
        | succ n =>
          have : (b :: rest.take n).take 4 ≠ [13, 10, 13, 10] := by
            intro e'
            rw [← List.take_succ_cons, List.take_take] at e'
            have hl := congrArg List.length e'
            by_cases h4 : 4 ≤ n + 1
            · rw [Nat.min_eq_left h4] at e'
              exact e e'
            · simp at hl
              omega
          rw [List.take_succ_cons, blankAt, ih hr n]
          by_cases hk : k ≤ n
          · simp only [this, ↓reduceIte, hk, Option.map_some, Nat.add_le_add_iff_right]
          · simp only [this, ↓reduceIte, hk, Option.map_none, Nat.add_le_add_iff_right]

private theorem ne_cr_of_plain {c : Char} (h : plain c) : c ≠ '\r' := by
  rintro rfl
  exact absurd h (by decide)

private theorem blankAt_lines (t : List UInt8) : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, l ≠ [] ∧ ∀ c ∈ l, c ≠ '\r') →
    blankAt ((['\r', '\n'].intercalate ls).flatMap String.utf8EncodeChar
        ++ 13 :: 10 :: 13 :: 10 :: t)
      = some (((['\r', '\n'].intercalate ls).flatMap String.utf8EncodeChar).length + 4)
  | [l], _, h => by
    rw [List.intercalate_singleton, blankAt_append_of_ne _ (ne_13_of_ne_cr (h l (by simp)).2),
      blankAt_blank]
    simp only [Option.map_some, Nat.add_comm]
  | l :: l' :: ls, _, h => by
    have hl := h l (by simp)
    have hrest := blankAt_lines t (ls := l' :: ls) (by simp) fun x hx => h x (by simp_all)
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (h l' (by simp)).1
    have hc0 : c ≠ '\r' := (h l' (by simp)).2 c (by simp [hc])
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (String.utf8EncodeChar_ne_nil (c := c))
    have hb0 : b ≠ 13 := ne_13_of_ne_cr (cs := [c]) (by simpa using hc0) b (by simp [hb])
    rw [List.intercalate_cons_cons, List.flatMap_append, List.flatMap_append, List.append_assoc,
      List.append_assoc, blankAt_append_of_ne _ (ne_13_of_ne_cr hl.2)]
    have hsep : (['\r', '\n'] : List Char).flatMap String.utf8EncodeChar = [13, 10] := by decide
    rw [hsep, List.cons_append, List.cons_append, List.nil_append]
    have hhead : ((['\r', '\n'].intercalate (l' :: ls)).flatMap String.utf8EncodeChar
        ++ 13 :: 10 :: 13 :: 10 :: t).head? ≠ some 13 := by
      cases ls with
      | nil => simp [hc, hb, hb0]
      | cons l'' ls => simp [List.intercalate_cons_cons, hc, hb, hb0]
    rw [blankAt_crlf hhead, hrest]
    simp only [Option.map_some, Option.some.injEq, List.length_append, List.length_cons,
      List.length_nil]
    omega

private theorem lines_toList {lines : List String} :
    ("\r\n".intercalate lines).toList = ['\r', '\n'].intercalate (lines.map String.toList) := by
  rw [String.toList_intercalate]
  rfl

private theorem headEnd_head {lines : List String} (hne : lines ≠ [])
    (h : ∀ l ∈ lines, l ≠ "" ∧ l.toList.all plain) (t : ByteArray) :
    headEnd (("\r\n".intercalate lines ++ "\r\n\r\n").toUTF8 ++ t) 0
      = some (("\r\n".intercalate lines).utf8ByteSize + 4) := by
  have hsep : ("\r\n\r\n".toList.flatMap String.utf8EncodeChar) = [13, 10, 13, 10] := by decide
  rw [headEnd_eq, String.toUTF8_eq_toByteArray, ByteArray.data_append, Array.toList_append,
    data_toList_toByteArray, String.toList_append, List.flatMap_append, hsep, List.drop_zero,
    List.append_assoc, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, ← length_flatMap_utf8EncodeChar, lines_toList, blankAt_lines]
  · simp
  · simpa using hne
  · intro l hl
    obtain ⟨line, hline, rfl⟩ := List.mem_map.mp hl
    have := h line hline
    refine ⟨fun e => this.1 (String.toList_inj.mp (e.trans (by simp))), fun c hc =>
      ne_cr_of_plain ?_⟩
    exact List.all_eq_true.mp this.2 c hc

private theorem extract_head (text : String) (t : ByteArray) :
    ((text ++ "\r\n\r\n").toUTF8 ++ t).extract 0 text.utf8ByteSize = text.toUTF8 := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.append_assoc]
  exact ByteArray.extract_append_eq_left String.size_toByteArray.symm

private theorem splitLines_append {l : List Char} (h : ∀ c ∈ l, c ≠ '\r') (rest line : List Char)
    (done : List (List Char)) :
    splitLines (l ++ rest) line done = splitLines rest (l.reverse ++ line) done := by
  induction l generalizing line with
  | nil => rfl
  | cons c l ih =>
    rw [List.cons_append,
      splitLines.eq_3 _ _ c _ fun _ hc _ => h c List.mem_cons_self hc,
      ih fun c hc => h c (List.mem_cons_of_mem _ hc)]
    simp

private theorem splitLines_intercalate : ∀ {ls : List (List Char)}, ls ≠ [] →
    (∀ l ∈ ls, ∀ c ∈ l, c ≠ '\r') → ∀ done : List (List Char),
    splitLines (['\r', '\n'].intercalate ls) [] done = done.reverse ++ ls
  | [l], _, h, done => by
    rw [List.intercalate_singleton, ← List.append_nil l, splitLines_append (h l (by simp)),
      splitLines.eq_1]
    simp
  | l :: l' :: ls, _, h, done => by
    rw [List.intercalate_cons_cons, List.append_assoc, splitLines_append (h l (by simp)),
      List.cons_append, List.cons_append, List.nil_append, splitLines.eq_2,
      splitLines_intercalate (by simp) (fun x hx => h x (by simp_all))]
    simp

theorem decimal?_toString {n : Nat} (h : n < 10 ^ 18) : decimal? (toString n) = some n := by
  have hlength : n.repr.length ≤ 18 := (Nat.length_repr_le_iff (by decide)).mpr h
  have hdigits : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simpa [decimal?, hlength] using hdigits

private theorem toDigits_three {n : Nat} (h1 : 100 ≤ n) (h2 : n < 1000) :
    ∃ a b c, Nat.toDigits 10 n = [a, b, c] := by
  have hle := (Nat.length_toDigits_le_iff (b := 10) (n := n) (k := 3) (by decide) (by decide)).mpr
    (by simpa using h2)
  have hgt : ¬ (Nat.toDigits 10 n).length ≤ 2 := by
    rw [Nat.length_toDigits_le_iff (by decide) (by decide)]
    simpa using h1
  match hd : Nat.toDigits 10 n with
  | [a, b, c] => exact ⟨a, b, c, rfl⟩
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp_all

private theorem statusLine?_toString {status : Nat} (h1 : 100 ≤ status) (h2 : status < 1000) :
    statusLine? ("HTTP/1.1 " ++ toString status ++ " ").toList = some status := by
  obtain ⟨a, b, c, hd⟩ := toDigits_three h1 h2
  have hdec : decimal? (String.ofList [a, b, c]) = some status := by
    rw [← hd, ← Nat.toString_eq_ofList_toDigits]
    exact decimal?_toString (by omega)
  simp only [String.toList_append, Nat.toString_eq_repr, Nat.toList_repr, hd]
  simp at hdec
  simp [statusLine?, hdec, h1, plain]

private theorem trimOws_cons {v : List Char} (hstart : v.head?.any ows = false)
    (hend : v.getLast?.any ows = false) : trimOws (' ' :: v) = v := by
  rw [trimOws, List.dropWhile_cons_of_pos (by decide), dropWhile_of_head_any hstart,
    dropWhile_of_head_any (by rwa [List.head?_reverse]), List.reverse_reverse]

private theorem ne_colon_of_token {name : String} (h : token name = true) :
    ∀ c ∈ name.toList, (c != ':') = true := by
  intro c hc
  simp only [token, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 c hc
  refine bne_iff_ne.mpr fun e => ?_
  subst e
  exact absurd this (by decide)

private theorem headerLine?_line {name value : String} (hname : token name = true)
    (hplain : value.toList.all plain = true) (hstart : value.toList.head?.any ows = false)
    (hend : value.toList.getLast?.any ows = false) :
    headerLine? (name ++ ": " ++ value).toList = some (name.toLower, value) := by
  have hcolon := ne_colon_of_token hname
  have hline : (name ++ ": " ++ value).toList = name.toList ++ ':' :: ' ' :: value.toList := by
    simp
  have hplain' : (' ' :: value.toList).all plain = true := by simpa [plain] using hplain
  rw [headerLine?, hline, List.takeWhile_append_of_pos hcolon,
    List.dropWhile_append_of_pos hcolon, List.takeWhile_cons_of_neg (by decide),
    List.dropWhile_cons_of_neg (by decide), List.append_nil, String.ofList_toList]
  simp only [hname, hplain', Bool.and_self, ↓reduceIte, trimOws_cons hstart hend,
    String.ofList_toList]

private theorem plain_of_isDigit {c : Char} (h : c.isDigit = true) : plain c := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [plain, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  refine .inr ⟨?_, ?_⟩
  · exact Nat.le_trans (by decide) (Char.le_def.mp h.1)
  · intro e
    have := Char.le_def.mp h.2
    rw [e] at this
    exact absurd this (by decide)

private theorem kept_iff {field : String × String} :
    Response.kept field = true ↔ token field.1 = true ∧ field.1.toLower = field.1
      ∧ field.1 ≠ "content-length" ∧ field.1 ≠ "transfer-encoding"
      ∧ field.2.toList.all plain = true ∧ field.2.toList.head?.any ows = false
      ∧ field.2.toList.getLast?.any ows = false := by
  simp only [Response.kept, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    and_assoc]

private theorem token_plain {name : String} (h : token name = true) :
    name ≠ "" ∧ name.toList.all plain = true := by
  simp only [token, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
  exact ⟨h.1, List.all_eq_true.mpr fun c hc => plain_of_visible (visible_of_tokenChar (h.2 c hc))⟩

private theorem fieldLine_plain {field : String × String} (h : Response.kept field = true) :
    field.1 ++ ": " ++ field.2 ≠ "" ∧ (field.1 ++ ": " ++ field.2).toList.all plain = true := by
  obtain ⟨htoken, -, -, -, hplain, -, -⟩ := kept_iff.mp h
  obtain ⟨-, hname⟩ := token_plain htoken
  refine ⟨fun e => ?_, ?_⟩
  · have := congrArg String.length e
    simp at this
  · simp only [String.toList_append, List.all_append, hname, hplain, Bool.and_true, Bool.true_and]
    decide

private theorem statusLine_plain {status : Nat} :
    "HTTP/1.1 " ++ toString status ++ " " ≠ ""
      ∧ ("HTTP/1.1 " ++ toString status ++ " ").toList.all plain = true := by
  refine ⟨fun e => ?_, ?_⟩
  · have := congrArg String.length e
    simp at this
  · simp only [String.toList_append, List.all_append, Bool.and_eq_true]
    refine ⟨⟨by decide, ?_⟩, by decide⟩
    simp only [Nat.toString_eq_repr, Nat.toList_repr, List.all_eq_true]
    exact fun c hc => plain_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

private def headLines (r : Response) (framing : String) : List String :=
  ("HTTP/1.1 " ++ toString r.status ++ " ") :: framing
    :: r.headers.map fun field => field.1 ++ ": " ++ field.2

private theorem headWire_eq (r : Response) (framing : String) :
    r.headWire framing = ("\r\n".intercalate (headLines r framing) ++ "\r\n\r\n").toUTF8 := rfl

private theorem size_headWire (r : Response) (framing : String) :
    (r.headWire framing).size = ("\r\n".intercalate (headLines r framing)).utf8ByteSize + 4 := by
  rw [headWire_eq, String.toUTF8_eq_toByteArray, String.size_toByteArray,
    String.utf8ByteSize_append]
  rfl

private theorem headLines_plain {r : Response} (hr : r.headers.all Response.kept = true)
    {framing : String} (hframing : framing ≠ "" ∧ framing.toList.all plain = true) :
    ∀ l ∈ headLines r framing, l ≠ "" ∧ l.toList.all plain = true := by
  intro l hl
  simp only [headLines, List.mem_cons, List.mem_map] at hl
  rcases hl with rfl | rfl | ⟨field, hfield, rfl⟩
  · exact statusLine_plain
  · exact hframing
  · exact fieldLine_plain (List.all_eq_true.mp hr field hfield)

private theorem head?_headWire {r : Response} (hr : r.writable = true) {framing : String}
    {field : String × String} (hframing : framing ≠ "" ∧ framing.toList.all plain = true)
    (hfield : headerLine? framing.toList = some field) (t : ByteArray) :
    headEnd (r.headWire framing ++ t) 0 = some (r.headWire framing).size
      ∧ (String.fromUTF8?
          ((r.headWire framing ++ t).extract 0 ((r.headWire framing).size - 4))).bind
          (head? ·.toList) = some (r.status, field :: r.headers) := by
  simp only [Response.writable, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨h200, h1000⟩, -⟩, -⟩, hkept⟩ := hr
  have hplain := headLines_plain hkept hframing
  refine ⟨?_, ?_⟩
  · rw [size_headWire, headWire_eq, headEnd_head (by simp [headLines]) hplain]
  · rw [size_headWire, Nat.add_sub_cancel, headWire_eq, extract_head, String.toUTF8_eq_toByteArray,
      fromUTF8?_toByteArray, Option.bind_some, lines_toList, head?,
      splitLines_intercalate (by simp [headLines])]
    · simp only [headLines, List.reverse_nil, List.nil_append, List.map_cons, List.map_map]
      rw [statusLine?_toString (by omega) h1000]
      simp only [Option.bind_eq_bind, Option.bind_some, List.mapM_cons, hfield]
      rw [List.mapM_map, mapM_some (g := id)]
      · simp
      · intro ⟨name, value⟩ hmem
        obtain ⟨htoken, hlower, -, -, hvalue, hstart, hend⟩ :=
          kept_iff.mp (List.all_eq_true.mp hkept _ hmem)
        simp only [Function.comp_apply, id]
        rw [headerLine?_line htoken hvalue hstart hend, hlower]
    · intro l hl c hc
      obtain ⟨line, hline, rfl⟩ := List.mem_map.mp hl
      exact ne_cr_of_plain (List.all_eq_true.mp (hplain line hline).2 c hc)

private theorem ows_of_isDigit {c : Char} (h : c.isDigit = true) : ows c = false := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := Char.le_def.mp h.1
  simp only [ows, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor <;> intro e <;> rw [e] at h1 <;> exact absurd h1 (by decide)

private theorem headerLine?_digits (name : String) (hname : token name = true) (n : Nat) :
    name ++ ": " ++ toString n ≠ "" ∧ (name ++ ": " ++ toString n).toList.all plain = true
      ∧ headerLine? (name ++ ": " ++ toString n).toList = some (name.toLower, toString n) := by
  have hdigit : ∀ c ∈ (toString n).toList, c.isDigit = true := by
    simp only [Nat.toString_eq_repr, Nat.toList_repr]
    exact fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hplain : (toString n).toList.all plain = true :=
    List.all_eq_true.mpr fun c hc => plain_of_isDigit (hdigit c hc)
  have hends : ∀ o : Option Char, (∀ c ∈ o, c ∈ (toString n).toList) → o.any ows = false := by
    rintro (_ | c) hc
    · rfl
    · exact ows_of_isDigit (hdigit c (hc c rfl))
  refine ⟨fun e => by have := congrArg String.length e; simp at this, ?_,
    headerLine?_line hname hplain (hends _ fun c hc => List.mem_of_mem_head? hc)
      (hends _ fun c hc => List.mem_of_getLast? hc)⟩
  simp only [String.toList_append, List.all_append, hplain, (token_plain hname).2, Bool.and_true,
    Bool.true_and]
  decide

private theorem framing?_length {r : Response} (hr : r.writable = true) :
    framing? r.status (("content-length", toString r.body.size) :: r.headers)
      = some (.length r.body.size) := by
  simp only [Response.writable, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨-, -⟩, hempty⟩, hsize⟩, hkept⟩ := hr
  have hnames : ∀ field ∈ r.headers, field.1 ≠ "content-length" ∧ field.1 ≠ "transfer-encoding" :=
    fun field hfield => by
      obtain ⟨-, -, h1, h2, -⟩ := kept_iff.mp (List.all_eq_true.mp hkept field hfield)
      exact ⟨h1, h2⟩
  have hte : r.headers.filter (·.1 == "transfer-encoding") = [] :=
    List.filter_eq_nil_iff.mpr fun field hfield => by simp [(hnames field hfield).2]
  have hcl : r.headers.filter (·.1 == "content-length") = [] :=
    List.filter_eq_nil_iff.mpr fun field hfield => by simp [(hnames field hfield).1]
  have hne : ("content-length" == "transfer-encoding") = false := by decide
  simp only [framing?, List.filter_cons, hne, Bool.false_eq_true, ↓reduceIte, hte, hcl,
    List.map_nil, List.map_cons, beq_self_eq_true, decimal?_toString hsize]
  split
  · rename_i hstatus
    simp only [Bool.or_eq_true, beq_iff_eq] at hempty hstatus
    rcases hempty with h | h
    · rw [h]
    · simp_all
  · simp

theorem readFrom_wire {r : Response} (hr : r.writable = true) (rest : ByteArray) (ended : Bool)
    (fuel : Nat) :
    readFrom (r.wire ++ rest) ended (fuel + 1) 0
      = .done (some ({ r with headers := ("content-length", toString r.body.size) :: r.headers },
          r.wire.size)) := by
  obtain ⟨-, hplain, hfield⟩ := headerLine?_digits "Content-Length" (by decide) r.body.size
  have hframing : "Content-Length: " ++ toString r.body.size
      = "Content-Length" ++ ": " ++ toString r.body.size := by
    rw [String.append_assoc]
    rfl
  have hlower : "Content-Length".toLower = "content-length" := by
    rw [← String.toList_inj, String.toLower, String.toList_map]
    decide
  rw [hlower] at hfield
  rw [← hframing] at hfield hplain
  have hwire : r.wire ++ rest = r.headWire ("Content-Length: " ++ toString r.body.size)
      ++ (r.body ++ rest) := by
    rw [Response.wire, ByteArray.append_assoc]
  obtain ⟨hend, hhead⟩ := head?_headWire hr ⟨by simp [← String.toList_inj] , hplain⟩ hfield
    (r.body ++ rest)
  have h200 : ¬ r.status < 200 := by
    simp only [Response.writable, Bool.and_eq_true, decide_eq_true_eq] at hr
    omega
  rw [hwire, readFrom, hend]
  simp only [hhead, h200, ↓reduceIte, framing?_length hr, ByteArray.size_append]
  have hle : (r.headWire ("Content-Length: " ++ toString r.body.size)).size + r.body.size
      ≤ (r.headWire ("Content-Length: " ++ toString r.body.size)).size
        + (r.body.size + rest.size) :=
    by omega
  simp only [hle, ↓reduceIte, extract_append_front, Response.wire, ByteArray.size_append]

/-! Bytes cut at `n` -/

private theorem crlf_of_le {bytes : ByteArray} {pos : Nat} (h : bytes.size ≤ pos) :
    crlf bytes pos = .more := by
  unfold crlf
  simp only [show ¬ pos + 1 < bytes.size by omega, show ¬ pos < bytes.size by omega, ↓reduceDIte]

private theorem crlf_extract (bytes : ByteArray) (n pos : Nat) :
    crlf (bytes.extract 0 n) pos = .more ∨ crlf (bytes.extract 0 n) pos = crlf bytes pos := by
  have hsize := size_extract_zero bytes n
  unfold crlf
  by_cases h1 : pos + 1 < (bytes.extract 0 n).size
  · have h1' : pos + 1 < bytes.size := by omega
    right
    simp only [h1, h1', ↓reduceDIte, getElem_extract_zero]
  · by_cases h2 : pos < (bytes.extract 0 n).size
    · simp only [h1, h2, ↓reduceDIte, getElem_extract_zero]
      have h2' : pos < bytes.size := by omega
      by_cases h13 : bytes[pos] = 13
      · simp [h13]
      · right
        by_cases h1' : pos + 1 < bytes.size
        · simp [h13, h1']
        · simp [h13, h1', h2']
    · left
      simp only [h1, h2, ↓reduceDIte]

private theorem skip_extract (bytes : ByteArray) (n : Nat) (keep : UInt8 → Bool) :
    ∀ fuel pos, skip (bytes.extract 0 n) keep fuel pos = skip bytes keep fuel pos
      ∨ (bytes.extract 0 n).size ≤ skip (bytes.extract 0 n) keep fuel pos
  | 0, pos => .inl rfl
  | fuel + 1, pos => by
    simp only [skip, getElem?_extract_zero]
    by_cases hn : pos < n
    · simp only [hn, ↓reduceIte]
      split
      · exact skip_extract bytes n keep fuel (pos + 1)
      · exact .inl rfl
    · right
      simp only [hn, ↓reduceIte, Option.any_none, Bool.false_eq_true]
      rw [size_extract_zero]
      omega

private theorem hex_extract (bytes : ByteArray) (n : Nat) :
    ∀ fuel pos value, hex (bytes.extract 0 n) fuel pos value = hex bytes fuel pos value
      ∨ (bytes.extract 0 n).size ≤ (hex (bytes.extract 0 n) fuel pos value).2
  | 0, pos, value => .inl rfl
  | fuel + 1, pos, value => by
    simp only [hex, getElem?_extract_zero]
    by_cases hn : pos < n
    · simp only [hn, ↓reduceIte]
      split
      · exact hex_extract bytes n fuel (pos + 1) _
      · exact .inl rfl
    · right
      simp only [hn, ↓reduceIte, Option.bind_none]
      rw [size_extract_zero]
      omega

private theorem le_skip (bytes : ByteArray) (keep : UInt8 → Bool) :
    ∀ fuel pos, pos ≤ skip bytes keep fuel pos
  | 0, pos => Nat.le_refl _
  | fuel + 1, pos => by
    simp only [skip]
    split
    · exact Nat.le_trans (Nat.le_succ _) (le_skip bytes keep fuel (pos + 1))
    · exact Nat.le_refl _

private theorem le_sizeLineEnd (bytes : ByteArray) (pos : Nat) : pos ≤ sizeLineEnd bytes pos := by
  simp only [sizeLineEnd]
  split
  · exact Nat.le_trans (le_skip ..) (le_skip ..)
  · exact le_skip ..

private theorem sizeLineEnd_extract (bytes : ByteArray) (n pos : Nat) :
    sizeLineEnd (bytes.extract 0 n) pos = sizeLineEnd bytes pos
      ∨ (bytes.extract 0 n).size ≤ sizeLineEnd (bytes.extract 0 n) pos := by
  have hnone : ∀ i, (bytes.extract 0 n).size ≤ i → (bytes.extract 0 n)[i]? = none :=
    fun i h => getElem?_neg _ _ (by omega)
  simp only [sizeLineEnd]
  rcases skip_extract bytes n (fun b => b == 32 || b == 9) chunkExtensionBytes_max pos with h | h
  · rw [h]
    generalize skip bytes (fun b => b == 32 || b == 9) chunkExtensionBytes_max pos = blanksEnd
      at h ⊢
    by_cases hb : (bytes.extract 0 n).size ≤ blanksEnd
    · right
      simp only [hnone _ hb]
      exact hb
    · have hb' : blanksEnd < n := by rw [size_extract_zero] at hb; omega
      rw [getElem?_extract_zero]
      simp only [hb', ↓reduceIte]
      split
      · exact skip_extract ..
      · exact .inl rfl
  · right
    simp only [hnone _ h]
    exact h

private theorem chunkHead_extract (bytes : ByteArray) (n pos : Nat) :
    chunkHead (bytes.extract 0 n) pos = .more
      ∨ chunkHead (bytes.extract 0 n) pos = chunkHead bytes pos := by
  have hmap : ∀ (r : Reading Nat) (size : Nat), r = .more → r.map (size, ·) = .more := by
    rintro _ _ rfl; rfl
  unfold chunkHead
  rcases hex_extract bytes n chunkSizeDigits_max pos 0 with h | h
  · rw [h]
    generalize hex bytes chunkSizeDigits_max pos 0 = full
    obtain ⟨size, d⟩ := full
    simp only
    by_cases hd : d = pos
    · subst hd
      simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hpos : d < (bytes.extract 0 n).size
      · right
        have hpos' := hpos
        rw [size_extract_zero] at hpos'
        simp only [hpos, show d < bytes.size by omega, ↓reduceIte]
      · left
        simp only [hpos, ↓reduceIte]
    · simp only [beq_iff_eq, hd, ↓reduceIte]
      rcases sizeLineEnd_extract bytes n d with he | he
      · rw [he]
        rcases crlf_extract bytes n (sizeLineEnd bytes d) with hc | hc
        · exact .inl (hmap _ _ hc)
        · exact .inr (by rw [hc])
      · exact .inl (hmap _ _ (crlf_of_le he))
  · left
    generalize hex (bytes.extract 0 n) chunkSizeDigits_max pos 0 = cut at h ⊢
    obtain ⟨size, d⟩ := cut
    simp only at h ⊢
    by_cases hd : d = pos
    · subst hd
      simp only [beq_self_eq_true, ↓reduceIte, show ¬ d < (bytes.extract 0 n).size by omega]
    · simp only [beq_iff_eq, hd, ↓reduceIte]
      exact hmap _ _ (crlf_of_le (Nat.le_trans h (le_sizeLineEnd _ _)))

private theorem blankAt_append_of_some {l : List UInt8} {m : Nat} (h : blankAt l = some m)
    (t : List UInt8) : blankAt (l ++ t) = some m := by
  induction l generalizing m with
  | nil => simp [blankAt] at h
  | cons b rest ih =>
    rw [blankAt] at h
    split at h
    · rename_i e
      cases h
      have hl : 4 ≤ (b :: rest).length := by
        have := congrArg List.length e
        simp only [List.length_take, List.length_cons] at this
        simp only [List.length_cons]
        omega
      rw [List.cons_append, blankAt, ← List.cons_append, List.take_append_of_le_length hl]
      simp [e]
    · rename_i e
      cases hr : blankAt rest with
      | none => simp [hr] at h
      | some k =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        have hl : 4 ≤ (b :: rest).length := by
          have := (blankAt_le hr).2
          have := (blankAt_le hr).1
          simp only [List.length_cons]
          omega
        rw [List.cons_append, blankAt, ← List.cons_append, List.take_append_of_le_length hl]
        simp only [e, ↓reduceIte, ih hr, Option.map_some]

private theorem headEnd_extract (bytes : ByteArray) (n pos : Nat) :
    headEnd (bytes.extract 0 n) pos = none
      ∨ headEnd (bytes.extract 0 n) pos = headEnd bytes pos := by
  rw [headEnd_eq, headEnd_eq, toList_extract_zero, List.drop_take]
  cases hb : blankAt (bytes.data.toList.drop pos) with
  | some m =>
    rw [blankAt_take hb]
    split
    · exact .inr rfl
    · exact .inl rfl
  | none =>
    left
    cases hc : blankAt ((bytes.data.toList.drop pos).take (n - pos)) with
    | none => rfl
    | some m =>
      have := blankAt_append_of_some hc ((bytes.data.toList.drop pos).drop (n - pos))
      rw [List.take_append_drop, hb] at this
      cases this

/-! Where an answer ends -/

private theorem headEnd_bound {bytes : ByteArray} {pos stop : Nat}
    (h : headEnd bytes pos = some stop) : pos + 4 ≤ stop ∧ stop ≤ bytes.size := by
  rw [headEnd_eq] at h
  cases hb : blankAt (bytes.data.toList.drop pos) with
  | none => simp [hb] at h
  | some m =>
    simp only [hb, Option.map_some, Option.some.injEq] at h
    have := blankAt_le hb
    simp only [List.length_drop, Array.length_toList] at this
    have : bytes.data.size = bytes.size := rfl
    omega

private theorem crlf_bound {bytes : ByteArray} {pos stop : Nat}
    (h : crlf bytes pos = .done (some stop)) : stop = pos + 2 ∧ stop ≤ bytes.size := by
  unfold crlf at h
  split at h
  · split at h
    · cases h; omega
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h

private theorem le_hex (bytes : ByteArray) :
    ∀ fuel pos value, pos ≤ (hex bytes fuel pos value).2
  | 0, pos, value => Nat.le_refl _
  | fuel + 1, pos, value => by
    simp only [hex]
    split
    · exact Nat.le_trans (Nat.le_succ _) (le_hex bytes fuel (pos + 1) _)
    · exact Nat.le_refl _

private theorem chunkHead_bound {bytes : ByteArray} {pos size start : Nat}
    (h : chunkHead bytes pos = .done (some (size, start))) :
    pos + 3 ≤ start ∧ start ≤ bytes.size := by
  unfold chunkHead at h
  have hle := le_hex bytes chunkSizeDigits_max pos 0
  generalize hex bytes chunkSizeDigits_max pos 0 = read at h hle
  obtain ⟨v, d⟩ := read
  simp only at h hle
  split at h
  · split at h <;> cases h
  · rename_i hd
    simp only [beq_iff_eq] at hd
    cases hc : crlf bytes (sizeLineEnd bytes d) with
    | more => simp [hc, Reading.map] at h
    | done answer =>
      cases answer with
      | none => simp [hc, Reading.map] at h
      | some q =>
        simp only [hc, Reading.map, Option.map_some, Reading.done.injEq, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := crlf_bound hc
        have := le_sizeLineEnd bytes d
        omega

private theorem dechunk_bound {bytes : ByteArray} :
    ∀ {fuel pos : Nat} {body body' : ByteArray} {stop : Nat},
      dechunk bytes fuel pos body = .done (some (body', stop)) →
      body'.size + pos ≤ body.size + stop ∧ stop ≤ bytes.size
  | 0, _, _, _, _, h => by simp [dechunk] at h
  | fuel + 1, pos, body, body', stop, h => by
    unfold dechunk at h
    split at h
    · cases h
    · cases h
    · rename_i size start hhead
      have hstart := chunkHead_bound hhead
      split at h
      · split at h
        · split at h
          · rename_i hend
            cases h
            have := headEnd_bound hend
            omega
          · cases h
        · rename_i _ hc
          cases hcr : crlf bytes start with
          | more => simp [hcr, Reading.map] at h
          | done answer =>
            cases answer with
            | none => exact absurd hcr hc
            | some q =>
              simp only [hcr, Reading.map, Option.map_some, Reading.done.injEq,
                Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := crlf_bound hcr
              omega
      · split at h
        · rename_i next hnext
          have hn := crlf_bound hnext
          have := dechunk_bound h
          simp only [ByteArray.size_append, ByteArray.size_extract] at this
          omega
        · cases h
        · cases h

theorem readFrom_bound {bytes : ByteArray} {ended : Bool} :
    ∀ {fuel pos : Nat} {r : Response} {stop : Nat},
      readFrom bytes ended fuel pos = .done (some (r, stop)) →
      r.body.size + pos ≤ stop ∧ stop ≤ bytes.size
  | 0, _, _, _, h => by simp [readFrom] at h
  | fuel + 1, pos, r, stop, h => by
    unfold readFrom at h
    split at h
    · cases h
    · rename_i bodyStart hend
      have hb := headEnd_bound hend
      split at h
      · cases h
      · split at h
        · have := readFrom_bound h
          omega
        · split at h
          · cases h
          · split at h
            · rename_i hle
              cases h
              simp only [ByteArray.size_extract]
              omega
            · cases h
          · cases hd : dechunk bytes (bytes.size + 1) bodyStart .empty with
            | more => simp [hd, Reading.map] at h
            | done answer =>
              cases answer with
              | none => simp [hd, Reading.map] at h
              | some found =>
                obtain ⟨body, stop'⟩ := found
                simp only [hd, Reading.map, Option.map_some, Reading.done.injEq,
                  Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have := dechunk_bound hd
                simp only [ByteArray.size_empty] at this
                simp only
                omega
          · split at h
            · cases h
              simp only [ByteArray.size_extract]
              omega
            · cases h

/-! Enough fuel -/

private theorem dechunk_fuel (bytes : ByteArray) :
    ∀ {f₁ f₂ pos : Nat} (body : ByteArray), bytes.size - pos < f₁ → bytes.size - pos < f₂ →
      dechunk bytes f₁ pos body = dechunk bytes f₂ pos body
  | 0, _, _, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, h₂ => absurd h₂ (Nat.not_lt_zero _)
  | f₁ + 1, f₂ + 1, pos, body, h₁, h₂ => by
    unfold dechunk
    split
    · rfl
    · rfl
    · rename_i size start hhead
      have hstart := chunkHead_bound hhead
      split
      · rfl
      · split
        · rename_i next hnext
          have := crlf_bound hnext
          exact dechunk_fuel bytes _ (by omega) (by omega)
        · rfl
        · rfl

theorem readFrom_fuel (bytes : ByteArray) (ended : Bool) :
    ∀ {f₁ f₂ pos : Nat}, bytes.size - pos < f₁ → bytes.size - pos < f₂ →
      readFrom bytes ended f₁ pos = readFrom bytes ended f₂ pos
  | 0, _, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h₂ => absurd h₂ (Nat.not_lt_zero _)
  | f₁ + 1, f₂ + 1, pos, h₁, h₂ => by
    unfold readFrom
    split
    · rfl
    · rename_i bodyStart hend
      have hb := headEnd_bound hend
      split
      · rfl
      · split
        · exact readFrom_fuel bytes ended (by omega) (by omega)
        · rfl

/-! Fewer bytes -/

private theorem dechunk_extract (bytes : ByteArray) (n : Nat) :
    ∀ fuel pos body, dechunk (bytes.extract 0 n) fuel pos body = .more
      ∨ dechunk (bytes.extract 0 n) fuel pos body = dechunk bytes fuel pos body
  | 0, _, _ => .inr rfl
  | fuel + 1, pos, body => by
    rcases chunkHead_extract bytes n pos with h | h
    · left
      simp only [dechunk, h]
    · simp only [dechunk, h]
      split
      · exact .inr rfl
      · exact .inr rfl
      · rename_i size start _
        split
        · rcases crlf_extract bytes n start with hc | hc
          · left
            simp [hc, Reading.map]
          · rw [hc]
            split
            · rcases headEnd_extract bytes n start with he | he
              · left
                simp [he]
              · exact .inr (by rw [he])
            · exact .inr rfl
        · rcases crlf_extract bytes n (start + size) with hc | hc
          · left
            simp [hc]
          · rw [hc]
            split
            · rename_i next hnext
              have hn := crlf_bound (hc ▸ hnext)
              rw [size_extract_zero] at hn
              rw [extract_extract_zero (by omega)]
              exact dechunk_extract bytes n fuel next _
            · exact .inr rfl
            · exact .inr rfl

/-- What the reader makes of the first `n` bytes is that it needs more, or what it makes of all
of them; or, where the connection ends there, a body that runs to the end of the connection,
which with the connection open would need more. -/
theorem readFrom_extract (bytes : ByteArray) (n : Nat) (ended : Bool) :
    ∀ fuel pos, readFrom (bytes.extract 0 n) ended fuel pos = .more
      ∨ readFrom (bytes.extract 0 n) ended fuel pos = readFrom bytes ended fuel pos
      ∨ (ended = true ∧ readFrom bytes false fuel pos = .more)
  | 0, _ => .inr (.inl rfl)
  | fuel + 1, pos => by
    rcases headEnd_extract bytes n pos with h | h
    · left
      simp only [readFrom, h]
    · cases hf : headEnd bytes pos with
      | none =>
        left
        simp only [readFrom, h, hf]
      | some bodyStart =>
        have hb := headEnd_bound (h.trans hf)
        rw [size_extract_zero] at hb
        have hhead : (bytes.extract 0 n).extract pos (bodyStart - 4)
            = bytes.extract pos (bodyStart - 4) := extract_extract_zero (by omega)
        simp only [readFrom, h, hf, hhead]
        cases hparse : (String.fromUTF8? (bytes.extract pos (bodyStart - 4))).bind
            (head? ·.toList) with
        | none => exact .inr (.inl rfl)
        | some sh =>
          obtain ⟨status, headers⟩ := sh
          simp only
          by_cases hs : status < 200
          · simp only [hs, ↓reduceIte]
            exact readFrom_extract bytes n ended fuel bodyStart
          · simp only [hs, ↓reduceIte]
            cases hfr : framing? status headers with
            | none => exact .inr (.inl rfl)
            | some fr =>
              cases fr with
              | length len =>
                simp only
                by_cases hl : bodyStart + len ≤ (bytes.extract 0 n).size
                · have hl' := hl
                  rw [size_extract_zero] at hl'
                  right; left
                  simp only [hl, show bodyStart + len ≤ bytes.size by omega, ↓reduceIte,
                    extract_extract_zero (show bodyStart + len ≤ n by omega)]
                · left
                  simp only [hl, ↓reduceIte]
              | chunked =>
                simp only
                rw [dechunk_fuel (bytes.extract 0 n) (f₂ := bytes.size + 1) _ (by omega)
                  (by rw [size_extract_zero]; omega)]
                rcases dechunk_extract bytes n (bytes.size + 1) bodyStart .empty with hd | hd
                · left
                  simp [hd, Reading.map]
                · right; left
                  rw [hd]
              | toEnd =>
                cases ended
                · left
                  simp
                · right; right
                  simp

theorem readFrom_ended (bytes : ByteArray) :
    ∀ fuel pos, readFrom bytes false fuel pos ≠ .more →
      readFrom bytes true fuel pos = readFrom bytes false fuel pos
  | 0, _, _ => rfl
  | fuel + 1, pos, h => by
    unfold readFrom at h ⊢
    split
    · rfl
    · rename_i bodyStart hend
      simp only [hend] at h
      split
      · rfl
      · rename_i status headers hparse
        simp only [hparse] at h
        split
        · rename_i hs
          simp only [hs, ↓reduceIte] at h
          exact readFrom_ended bytes fuel bodyStart h
        · rename_i hs
          simp only [hs, ↓reduceIte] at h
          split
          · rfl
          · rfl
          · rfl
          · rename_i hfr
            simp [hfr] at h

namespace Response

/-- The reader asks for more only while the connection is open and no more than `limit` bytes
have arrived: so the adapter's loop ends, and holds at most `limit` bytes and one read. -/
theorem read_more {limit : Nat} {bytes : ByteArray} {ended : Bool}
    (h : read limit bytes ended = .more) : ended = false ∧ bytes.size ≤ limit := by
  unfold read at h
  split at h
  · split at h <;> cases h
  · cases h
  · split at h
    · cases h
    · simp_all

/-- A response the reader gives ends within `limit` bytes, and so does its body. -/
theorem read_some {limit : Nat} {bytes : ByteArray} {ended : Bool} {r : Response}
    (h : read limit bytes ended = .done (some r)) :
    ∃ stop, readFrom bytes ended (bytes.size + 1) 0 = .done (some (r, stop))
      ∧ r.body.size ≤ stop ∧ stop ≤ limit ∧ stop ≤ bytes.size := by
  unfold read at h
  split at h
  · rename_i response stop hread
    split at h
    · cases h
      have := readFrom_bound hread
      exact ⟨stop, hread, by omega, by assumption, this.2⟩
    · cases h
  · cases h
  · split at h <;> cases h

private theorem readFrom_append_of_ne_more {bytes : ByteArray} {answer : Option (Response × Nat)}
    (h : readFrom bytes false (bytes.size + 1) 0 = .done answer) (tail : ByteArray)
    (ended : Bool) :
    readFrom (bytes ++ tail) ended ((bytes ++ tail).size + 1) 0 = .done answer := by
  have hcut : (bytes ++ tail).extract 0 bytes.size = bytes := ByteArray.extract_append_eq_left rfl
  have hfuel : readFrom bytes false ((bytes ++ tail).size + 1) 0 = .done answer := by
    rw [readFrom_fuel bytes false (f₂ := bytes.size + 1) (by simp; omega) (by omega), h]
  have hfalse : readFrom (bytes ++ tail) false ((bytes ++ tail).size + 1) 0 = .done answer := by
    rcases readFrom_extract (bytes ++ tail) bytes.size false ((bytes ++ tail).size + 1) 0 with
      e | e | e
    · rw [hcut, hfuel] at e; cases e
    · rw [hcut, hfuel] at e; exact e.symm
    · cases e.1
  cases ended
  · exact hfalse
  · rw [readFrom_ended _ _ _ (by rw [hfalse]; simp), hfalse]

/-- An answer given while the connection is open is final: whatever arrives after it, and
whether or not the connection then ends, the answer is the same. -/
theorem read_append {limit : Nat} {bytes : ByteArray} {r : Response}
    (h : read limit bytes false = .done (some r)) (tail : ByteArray) (ended : Bool) :
    read limit (bytes ++ tail) ended = .done (some r) := by
  obtain ⟨stop, hread, -, hstop, -⟩ := read_some h
  unfold read
  rw [readFrom_append_of_ne_more hread]
  simp [hstop]

/-- A response written by `wire` is read back as written, with its `Content-Length`, as soon as
its last byte is there, whatever follows it and whether or not the connection has ended. -/
theorem read_wire {r : Response} (hr : r.writable = true) {limit : Nat}
    (hlimit : r.wire.size ≤ limit) (tail : ByteArray) (ended : Bool) :
    read limit (r.wire ++ tail) ended
      = .done (some
          { r with headers := ("content-length", toString r.body.size) :: r.headers }) := by
  unfold read
  rw [readFrom_wire hr]
  simp [hlimit]

private theorem readFrom_cut {wire : ByteArray} {r : Response}
    (h : ∀ ended, readFrom wire ended (wire.size + 1) 0 = .done (some (r, wire.size)))
    {n : Nat} (hn : n < wire.size) (ended : Bool) :
    readFrom (wire.extract 0 n) ended ((wire.extract 0 n).size + 1) 0 = .more := by
  have hsize : (wire.extract 0 n).size = n := by rw [size_extract_zero]; omega
  rw [readFrom_fuel _ ended (f₂ := wire.size + 1) (by omega) (by omega)]
  rcases readFrom_extract wire n ended (wire.size + 1) 0 with e | e | e
  · exact e
  · rw [h] at e
    have := (readFrom_bound e).2
    omega
  · rw [h] at e
    cases e.2

private theorem read_cut {wire : ByteArray} {r : Response}
    (h : ∀ ended, readFrom wire ended (wire.size + 1) 0 = .done (some (r, wire.size)))
    {limit : Nat} (hlimit : wire.size ≤ limit) {n : Nat} (hn : n < wire.size) (ended : Bool) :
    read limit (wire.extract 0 n) ended = if ended then .done none else .more := by
  have hsize : (wire.extract 0 n).size = n := by rw [size_extract_zero]; omega
  unfold read
  rw [readFrom_cut h hn]
  cases ended <;> simp [hsize, show ¬ limit < n by omega]

/-- Every strict start of a response written by `wire` waits for more while the connection is
open, and is refused once it has ended. -/
theorem read_wire_extract {r : Response} (hr : r.writable = true) {limit : Nat}
    (hlimit : r.wire.size ≤ limit) {n : Nat} (hn : n < r.wire.size) (ended : Bool) :
    read limit (r.wire.extract 0 n) ended = if ended then .done none else .more :=
  read_cut (fun ended => by simpa using readFrom_wire hr .empty ended r.wire.size) hlimit hn ended

end Response

/-! Chunks -/

private theorem hex_digits (bytes : ByteArray) :
    ∀ (ds : List Nat) (fuel pos value : Nat), ds.length ≤ fuel →
      (∀ i (hi : i < ds.length),
        bytes[pos + i]?.bind (fun b => hexValue? (Char.ofNat b.toNat)) = some ds[i]) →
      (ds.length < fuel → bytes[pos + ds.length]?.bind (fun b => hexValue? (Char.ofNat b.toNat))
        = none) →
      hex bytes fuel pos value = (ds.foldl (fun v d => v * 16 + d) value, pos + ds.length)
  | [], 0, pos, value, _, _, _ => rfl
  | [], fuel + 1, pos, value, _, _, hend => by
    have := hend (by simp)
    simp only [List.length_nil, Nat.add_zero] at this
    simp only [hex, this, List.foldl_nil, List.length_nil, Nat.add_zero]
  | d :: ds, fuel + 1, pos, value, hlen, hds, hend => by
    simp only [hex]
    have h0 := hds 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    rw [h0]
    simp only
    rw [hex_digits bytes ds fuel (pos + 1) _ (by simp at hlen; omega)
      (fun i hi => by
        have := hds (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      (fun h => by
        have := hend (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this)]
    simp [Nat.add_assoc, Nat.add_comm 1]

private def hexChars : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

private theorem digitChar_eq {d : Nat} (h : d < 16) :
    Nat.digitChar d = hexChars[d]'(by simp [hexChars]; omega) := by
  match d, h with
  | 0, _ => simp [hexChars]
  | 1, _ => simp [hexChars]
  | 2, _ => simp [hexChars]
  | 3, _ => simp [hexChars]
  | 4, _ => simp [hexChars]
  | 5, _ => simp [hexChars]
  | 6, _ => simp [hexChars]
  | 7, _ => simp [hexChars]
  | 8, _ => simp [hexChars]
  | 9, _ => simp [hexChars]
  | 10, _ => simp [hexChars]
  | 11, _ => simp [hexChars]
  | 12, _ => simp [hexChars]
  | 13, _ => simp [hexChars]
  | 14, _ => simp [hexChars]
  | 15, _ => simp [hexChars]
  | _ + 16, h => exact absurd h (by omega)

private theorem hexChars_spec : ∀ d (h : d < 16),
    String.utf8EncodeChar (hexChars[d]'(by simp [hexChars]; omega))
        = [(String.utf8EncodeChar (hexChars[d]'(by simp [hexChars]; omega))).headD 0]
      ∧ hexValue? (Char.ofNat
          ((String.utf8EncodeChar (hexChars[d]'(by simp [hexChars]; omega))).headD 0).toNat)
        = some d
      ∧ hexValue? (hexChars[d]'(by simp [hexChars]; omega)) = some d := by
  decide

private theorem digit_byte {d : Nat} (h : d < 16) :
    String.utf8EncodeChar (Nat.digitChar d) = [(String.utf8EncodeChar (Nat.digitChar d)).headD 0]
      ∧ hexValue? (Char.ofNat ((String.utf8EncodeChar (Nat.digitChar d)).headD 0).toNat)
        = some d := by
  rw [digitChar_eq h]
  exact ⟨(hexChars_spec d h).1, (hexChars_spec d h).2.1⟩

private theorem hexValue?_digitChar {d : Nat} (h : d < 16) :
    hexValue? (Nat.digitChar d) = some d := by
  rw [digitChar_eq h]
  exact (hexChars_spec d h).2.2

private theorem mem_toDigits_hex {n : Nat} :
    ∀ c ∈ Nat.toDigits 16 n, ∃ d < 16, c = Nat.digitChar d := by
  induction n using Nat.base_induction 16 (by decide) with
  | single m hm =>
    intro c hc
    rw [Nat.toDigits_of_lt_base hm] at hc
    exact ⟨m, hm, List.mem_singleton.mp hc⟩
  | digit m k hk hm ih =>
    intro c hc
    rw [← Nat.toDigits_append_toDigits (by decide) hm hk, Nat.toDigits_of_lt_base hk] at hc
    rcases List.mem_append.mp hc with h | h
    · exact ih c h
    · exact ⟨k, hk, List.mem_singleton.mp h⟩

private def hexDigits (n : Nat) : List Nat :=
  (Nat.toDigits 16 n).map fun c => (hexValue? c).getD 0

private theorem foldl_hexDigits (n : Nat) :
    (hexDigits n).foldl (fun v d => v * 16 + d) 0 = n := by
  induction n using Nat.base_induction 16 (by decide) with
  | single m hm =>
    simp [hexDigits, Nat.toDigits_of_lt_base hm, hexValue?_digitChar hm]
  | digit m k hk hm ih =>
    rw [hexDigits, ← Nat.toDigits_append_toDigits (by decide) hm hk, Nat.toDigits_of_lt_base hk,
      List.map_append, List.foldl_append, ← hexDigits, ih]
    simp [hexValue?_digitChar hk]
    omega

private theorem toByteArray_digits {cs : List Char} (h : ∀ c ∈ cs, ∃ d < 16, c = Nat.digitChar d) :
    (String.ofList cs).toByteArray.data.toList
      = cs.map fun c => (String.utf8EncodeChar c).headD 0 := by
  rw [data_toList_toByteArray, String.toList_ofList]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨d, hd, rfl⟩ := h c List.mem_cons_self
    rw [List.flatMap_cons, (digit_byte hd).1, ih fun c hc => h c (List.mem_cons_of_mem _ hc)]
    rfl

private theorem crlf_of_getElem? {bytes : ByteArray} {q : Nat} (h0 : bytes[q]? = some 13)
    (h1 : bytes[q + 1]? = some 10) : crlf bytes q = .done (some (q + 2)) := by
  obtain ⟨hq0, e0⟩ := getElem_of_getElem? h0
  obtain ⟨hq1, e1⟩ := getElem_of_getElem? h1
  unfold crlf
  simp [hq1, e0, e1]

private theorem sizeLineEnd_of_cr {bytes : ByteArray} {q : Nat} (h : bytes[q]? = some 13) :
    sizeLineEnd bytes q = q := by
  simp [sizeLineEnd, chunkExtensionBytes_max, skip, h]

private theorem toList_chunk (c : ByteArray) :
    (Response.chunk c).data.toList
      = (Nat.toDigits 16 c.size).map (fun ch => (String.utf8EncodeChar ch).headD 0)
        ++ 13 :: 10 :: (c.data.toList ++ [13, 10]) := by
  have hcrlf : "\r\n".toByteArray.data.toList = [13, 10] := by
    rw [data_toList_toByteArray]; decide
  simp only [Response.chunk, String.toUTF8_eq_toByteArray, String.toByteArray_append,
    ByteArray.data_append, Array.toList_append, toByteArray_digits mem_toDigits_hex, hcrlf]
  simp

private theorem size_chunk (c : ByteArray) :
    (Response.chunk c).size = (Nat.toDigits 16 c.size).length + 2 + c.size + 2 := by
  have := congrArg List.length (toList_chunk c)
  simp only [Array.length_toList, List.length_append, List.length_map, List.length_cons,
    List.length_nil] at this
  have hc : c.data.size = c.size := rfl
  have hk : (Response.chunk c).data.size = (Response.chunk c).size := rfl
  omega

private theorem hex_chunk {c : ByteArray} (hc : c.size < 16 ^ 16) (pre tail : ByteArray) :
    hex (pre ++ (Response.chunk c ++ tail)) chunkSizeDigits_max pre.size 0
      = (c.size, pre.size + (Nat.toDigits 16 c.size).length) := by
  have hlen : (Nat.toDigits 16 c.size).length ≤ 16 :=
    (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr hc
  have hlist : ∀ i, (pre ++ (Response.chunk c ++ tail))[pre.size + i]?
      = ((Response.chunk c).data.toList ++ tail.data.toList)[i]? := by
    intro i
    rw [getElem?_append_front, ByteArray.data_append, Array.toList_append]
  have hds : (hexDigits c.size).length = (Nat.toDigits 16 c.size).length := by
    simp [hexDigits]
  have := hex_digits (pre ++ (Response.chunk c ++ tail)) (hexDigits c.size) chunkSizeDigits_max
    pre.size 0 (by rw [hds]; exact hlen) ?_ ?_
  · rw [this, foldl_hexDigits, hds]
  · intro i hi
    rw [hlist, toList_chunk, List.append_assoc, List.getElem?_append_left (by simp; omega),
      List.getElem?_map]
    have hi' : i < (Nat.toDigits 16 c.size).length := by rw [← hds]; exact hi
    rw [List.getElem?_eq_getElem hi']
    obtain ⟨d, hd, e⟩ := mem_toDigits_hex _ (List.getElem_mem hi')
    simp only [Option.map_some, Option.bind_some, hexDigits, List.getElem_map, e,
      (digit_byte hd).2, hexValue?_digitChar hd, Option.getD_some]
  · intro _
    rw [hlist, toList_chunk, List.append_assoc, List.getElem?_append_right (by simp; omega)]
    simp [hds]
    rfl

private theorem dechunk_chunk {c : ByteArray} (hc : 0 < c.size) (hc' : c.size < 16 ^ 16)
    (pre tail : ByteArray) (fuel : Nat) (body : ByteArray) :
    dechunk (pre ++ (Response.chunk c ++ tail)) (fuel + 1) pre.size body
      = dechunk (pre ++ (Response.chunk c ++ tail)) fuel (pre.size + (Response.chunk c).size)
          (body ++ c) := by
  have k1 : 0 < (Nat.toDigits 16 c.size).length := Nat.length_toDigits_pos
  generalize hk : (Nat.toDigits 16 c.size).length = k at k1
  have hlist : ∀ i, (pre ++ (Response.chunk c ++ tail))[pre.size + i]?
      = ((Nat.toDigits 16 c.size).map (fun ch => (String.utf8EncodeChar ch).headD 0)
        ++ 13 :: 10 :: (c.data.toList ++ 13 :: 10 :: tail.data.toList))[i]? := by
    intro i
    rw [getElem?_append_front, ByteArray.data_append, Array.toList_append, toList_chunk]
    simp
  have hat : ∀ j, (pre ++ (Response.chunk c ++ tail))[pre.size + (k + j)]?
      = (13 :: 10 :: (c.data.toList ++ 13 :: 10 :: tail.data.toList))[j]? := by
    intro j
    rw [hlist, List.getElem?_append_right (by simp; omega)]
    simp [hk]
  have hcsize : c.data.toList.length = c.size := by simp
  have hcr : (pre ++ (Response.chunk c ++ tail))[pre.size + k]? = some 13 := by
    simpa using hat 0
  have hlf : (pre ++ (Response.chunk c ++ tail))[pre.size + k + 1]? = some 10 := by
    have := hat 1
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simpa [Nat.add_assoc] using this
  have hcr' : (pre ++ (Response.chunk c ++ tail))[pre.size + k + 2 + c.size]? = some 13 := by
    have := hat (c.size + 2)
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hcsize, Nat.sub_self] at this
    simpa [Nat.add_assoc, Nat.add_comm c.size 2] using this
  have hlf' : (pre ++ (Response.chunk c ++ tail))[pre.size + k + 2 + c.size + 1]? = some 10 := by
    have := hat (c.size + 1 + 2)
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hcsize, Nat.add_sub_cancel_left] at this
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    have e : pre.size + k + 2 + c.size + 1 = pre.size + (k + (c.size + 1 + 2)) := by omega
    rw [e]
    exact this
  have hhead : chunkHead (pre ++ (Response.chunk c ++ tail)) pre.size
      = .done (some (c.size, pre.size + k + 2)) := by
    unfold chunkHead
    rw [hex_chunk hc', hk]
    simp only [beq_iff_eq, show ¬ pre.size + k = pre.size by omega, ↓reduceIte,
      sizeLineEnd_of_cr hcr, crlf_of_getElem? hcr hlf]
    rfl
  have hdata : (pre ++ (Response.chunk c ++ tail)).extract (pre.size + k + 2)
      (pre.size + k + 2 + c.size) = c := by
    have hsplit : Response.chunk c
        = (String.ofList (Nat.toDigits 16 c.size) ++ "\r\n").toUTF8 ++ (c ++ "\r\n".toUTF8) := by
      rw [Response.chunk, ByteArray.append_assoc]
    have hfront : (String.ofList (Nat.toDigits 16 c.size) ++ "\r\n").toUTF8.size = k + 2 := by
      have h := congrArg List.length (toByteArray_digits (mem_toDigits_hex (n := c.size)))
      simp only [Array.length_toList, List.length_map, hk] at h
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.size_append]
      exact congrArg (· + 2) h
    have e : pre ++ (Response.chunk c ++ tail)
        = (pre ++ (String.ofList (Nat.toDigits 16 c.size) ++ "\r\n").toUTF8)
          ++ (c ++ ("\r\n".toUTF8 ++ tail)) := by
      rw [hsplit]
      simp only [ByteArray.append_assoc]
    rw [e]
    have := extract_append_front (pre ++ (String.ofList (Nat.toDigits 16 c.size) ++ "\r\n").toUTF8)
      c ("\r\n".toUTF8 ++ tail)
    rwa [ByteArray.size_append, hfront, ← Nat.add_assoc] at this
  rw [dechunk, hhead]
  simp only [show c.size ≠ 0 by omega, ↓reduceIte, crlf_of_getElem? hcr' hlf', hdata, size_chunk,
    hk]
  congr 1
  omega

private theorem dechunk_last (pre tail : ByteArray) (fuel : Nat) (body : ByteArray) :
    dechunk (pre ++ ("0\r\n\r\n".toUTF8 ++ tail)) (fuel + 1) pre.size body
      = .done (some (body, pre.size + 5)) := by
  have hlist : ∀ i, (pre ++ ("0\r\n\r\n".toUTF8 ++ tail))[pre.size + i]?
      = (48 :: 13 :: 10 :: 13 :: 10 :: tail.data.toList)[i]? := by
    intro i
    rw [getElem?_append_front, ByteArray.data_append, Array.toList_append,
      String.toUTF8_eq_toByteArray, data_toList_toByteArray]
    rfl
  have h0 := hlist 0
  have h1 := hlist 1
  have h2 := hlist 2
  have h3 := hlist 3
  have h4 := hlist 4
  simp only [Nat.add_zero, List.getElem?_cons_succ, List.getElem?_cons_zero] at h0 h1 h2 h3 h4
  have hhex : hex (pre ++ ("0\r\n\r\n".toUTF8 ++ tail)) chunkSizeDigits_max pre.size 0
      = (0, pre.size + 1) := by
    have := hex_digits (pre ++ ("0\r\n\r\n".toUTF8 ++ tail)) [0] chunkSizeDigits_max pre.size 0
      (by decide)
      (fun i hi => by
        match i, hi with
        | 0, _ =>
          rw [Nat.add_zero, h0]
          rfl)
      (fun _ => by
        rw [List.length_singleton, h1]
        rfl)
    exact this
  have hhead : chunkHead (pre ++ ("0\r\n\r\n".toUTF8 ++ tail)) pre.size
      = .done (some (0, pre.size + 3)) := by
    unfold chunkHead
    rw [hhex]
    simp only [beq_iff_eq, show ¬ pre.size + 1 = pre.size by omega, ↓reduceIte,
      sizeLineEnd_of_cr h1, crlf_of_getElem? h1 h2]
    rfl
  rw [dechunk, hhead]
  simp only [↓reduceIte, crlf_of_getElem? h3 h4]
  rfl

private def chunksWire : List ByteArray → ByteArray
  | [] => .empty
  | c :: cs => Response.chunk c ++ chunksWire cs

private theorem foldl_chunk (acc : ByteArray) (cs : List ByteArray) :
    cs.foldl (· ++ Response.chunk ·) acc = acc ++ chunksWire cs := by
  induction cs generalizing acc with
  | nil => simp [chunksWire]
  | cons c cs ih => rw [List.foldl_cons, ih, chunksWire, ByteArray.append_assoc]

private theorem dechunk_chunks :
    ∀ (cs : List ByteArray), (∀ c ∈ cs, 0 < c.size ∧ c.size < 16 ^ 16) →
    ∀ (pre tail body : ByteArray) (fuel : Nat), cs.length < fuel →
    dechunk (pre ++ (chunksWire cs ++ ("0\r\n\r\n".toUTF8 ++ tail))) fuel pre.size body
      = .done (some (body ++ cs.foldl (· ++ ·) .empty, pre.size + (chunksWire cs).size + 5))
  | [], _, pre, tail, body, fuel + 1, _ => by
    simp only [chunksWire, ByteArray.empty_append, dechunk_last, List.foldl_nil,
      ByteArray.append_empty, ByteArray.size_empty, Nat.add_zero]
  | c :: cs, h, pre, tail, body, fuel + 1, hfuel => by
    have hc := h c List.mem_cons_self
    have e : pre ++ (chunksWire (c :: cs) ++ ("0\r\n\r\n".toUTF8 ++ tail))
        = pre ++ (Response.chunk c ++ (chunksWire cs ++ ("0\r\n\r\n".toUTF8 ++ tail))) := by
      simp only [chunksWire, ByteArray.append_assoc]
    rw [e, dechunk_chunk hc.1 hc.2]
    have e' : pre ++ (Response.chunk c ++ (chunksWire cs ++ ("0\r\n\r\n".toUTF8 ++ tail)))
        = (pre ++ Response.chunk c) ++ (chunksWire cs ++ ("0\r\n\r\n".toUTF8 ++ tail)) := by
      simp only [ByteArray.append_assoc]
    have hsize : pre.size + (Response.chunk c).size = (pre ++ Response.chunk c).size :=
      ByteArray.size_append.symm
    rw [e', hsize, dechunk_chunks cs (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ _ _ _
      (by simp at hfuel; omega)]
    simp only [List.foldl_cons, ByteArray.empty_append, foldl_append_bytes c, chunksWire,
      ByteArray.size_append, ByteArray.append_assoc]
    congr 3
    omega

private theorem framing?_chunked {r : Response} (hr : r.writable = true)
    (hstatus : r.status ≠ 204 ∧ r.status ≠ 304) :
    framing? r.status (("transfer-encoding", "chunked") :: r.headers) = some .chunked := by
  simp only [Response.writable, Bool.and_eq_true] at hr
  obtain ⟨-, hkept⟩ := hr
  have hnames : ∀ field ∈ r.headers, field.1 ≠ "content-length" ∧ field.1 ≠ "transfer-encoding" :=
    fun field hfield => by
      obtain ⟨-, -, h1, h2, -⟩ := kept_iff.mp (List.all_eq_true.mp hkept field hfield)
      exact ⟨h1, h2⟩
  have hte : r.headers.filter (·.1 == "transfer-encoding") = [] :=
    List.filter_eq_nil_iff.mpr fun field hfield => by simp [(hnames field hfield).2]
  have hcl : r.headers.filter (·.1 == "content-length") = [] :=
    List.filter_eq_nil_iff.mpr fun field hfield => by simp [(hnames field hfield).1]
  have hne : ("transfer-encoding" == "content-length") = false := by decide
  have hlower : "chunked".toLower = "chunked" := by
    rw [← String.toList_inj, String.toLower, String.toList_map]
    decide
  simp only [framing?, List.filter_cons, hne, Bool.false_eq_true, ↓reduceIte, hte, hcl,
    List.map_nil, List.map_cons, beq_self_eq_true, hlower]
  simp [hstatus]

theorem readFrom_wireChunked {r : Response} (hr : r.writable = true)
    (hstatus : r.status ≠ 204 ∧ r.status ≠ 304) {chunks : List ByteArray}
    (hchunks : ∀ c ∈ chunks, 0 < c.size ∧ c.size < 16 ^ 16) (tail : ByteArray) (ended : Bool)
    (fuel : Nat) :
    readFrom (r.wireChunked chunks ++ tail) ended (fuel + 1) 0
      = .done (some ({ r with
          headers := ("transfer-encoding", "chunked") :: r.headers
          body := chunks.foldl (· ++ ·) .empty }, (r.wireChunked chunks).size)) := by
  have hlower : "Transfer-Encoding".toLower = "transfer-encoding" := by
    rw [← String.toList_inj, String.toLower, String.toList_map]
    decide
  have hfield : headerLine? "Transfer-Encoding: chunked".toList
      = some ("transfer-encoding", "chunked") := by
    have := headerLine?_line (name := "Transfer-Encoding") (value := "chunked") (by decide)
      (by decide) (by decide) (by decide)
    rwa [hlower] at this
  have hwire : r.wireChunked chunks ++ tail = r.headWire "Transfer-Encoding: chunked"
      ++ (chunksWire chunks ++ ("0\r\n\r\n".toUTF8 ++ tail)) := by
    rw [Response.wireChunked, foldl_chunk, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  obtain ⟨hend, hhead⟩ := head?_headWire hr ⟨by simp [← String.toList_inj], by decide⟩ hfield
    (chunksWire chunks ++ ("0\r\n\r\n".toUTF8 ++ tail))
  have h200 : ¬ r.status < 200 := by
    simp only [Response.writable, Bool.and_eq_true, decide_eq_true_eq] at hr
    omega
  have hlen : chunks.length ≤ (chunksWire chunks).size := by
    clear hwire hend hhead
    induction chunks with
    | nil => simp
    | cons c cs ih =>
      simp only [chunksWire, ByteArray.size_append, size_chunk, List.length_cons]
      have := ih fun x hx => hchunks x (List.mem_cons_of_mem _ hx)
      omega
  rw [hwire, readFrom, hend]
  simp only [hhead, h200, ↓reduceIte, framing?_chunked hr hstatus]
  rw [dechunk_chunks chunks hchunks _ _ _ _ (by simp only [ByteArray.size_append]; omega)]
  simp only [Reading.map, Option.map_some, ByteArray.empty_append, Response.wireChunked,
    foldl_chunk, ByteArray.size_append]
  rfl

namespace Response

/-- A response written by `wireChunked`, in chunks that are not empty and of sizes of at most
sixteen hex digits, is read back as written, with its `Transfer-Encoding`, as soon as its last
byte is there, whatever follows it and whether or not the connection has ended. -/
theorem read_wireChunked {r : Response} (hr : r.writable = true)
    (hstatus : r.status ≠ 204 ∧ r.status ≠ 304) {chunks : List ByteArray}
    (hchunks : ∀ c ∈ chunks, 0 < c.size ∧ c.size < 16 ^ 16)
    (hbody : chunks.foldl (· ++ ·) .empty = r.body) {limit : Nat}
    (hlimit : (r.wireChunked chunks).size ≤ limit) (tail : ByteArray) (ended : Bool) :
    read limit (r.wireChunked chunks ++ tail) ended
      = .done (some { r with headers := ("transfer-encoding", "chunked") :: r.headers }) := by
  unfold read
  rw [readFrom_wireChunked hr hstatus hchunks, hbody]
  simp [hlimit]

/-- Every strict start of a response written by `wireChunked` waits for more while the
connection is open, and is refused once it has ended. -/
theorem read_wireChunked_extract {r : Response} (hr : r.writable = true)
    (hstatus : r.status ≠ 204 ∧ r.status ≠ 304) {chunks : List ByteArray}
    (hchunks : ∀ c ∈ chunks, 0 < c.size ∧ c.size < 16 ^ 16) {limit : Nat}
    (hlimit : (r.wireChunked chunks).size ≤ limit) {n : Nat} (hn : n < (r.wireChunked chunks).size)
    (ended : Bool) :
    read limit ((r.wireChunked chunks).extract 0 n) ended = if ended then .done none else .more :=
  read_cut (fun ended => by simpa using readFrom_wireChunked hr hstatus hchunks .empty ended _)
    hlimit hn ended

end Response

end Lanes.Http
