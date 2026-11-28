/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Mail.Message
public import Lanes.Lib.Net.UrlSound
public import Lanes.Proof.List.Basic

/-!
A message as `Message.bytes` writes it is lines ended by CR LF, with no CR or LF in a line and
none over 998 octets (`Message.wellformed`, RFC 5322 §2.1.1 and §2.3), whatever its text; and its
header holds exactly the fields its shape names (`Message.header_fields`), so that no text given,
a subject or a name, can add a field or end the header.

Every line is printable ASCII of at most 998 characters (`Message.lines_fit`): each word of a
header is at most `raw_max` characters, written as it is only when it already is such text, or
as encoded words, which are; quoted-printable writes such text whatever the body.
-/

@[expose] public section

namespace Lanes.Mail

/-- What a line of a message is as written: CR LF after it, and neither in it, at most 998
octets. -/
def Wellformed (bytes : List UInt8) : Prop :=
  ∃ lines : List (List UInt8), bytes = (lines.map (· ++ [13, 10])).flatten ∧
    ∀ l ∈ lines, 13 ∉ l ∧ 10 ∉ l ∧ l.length ≤ 998

/-- Printable ASCII of at most `n` characters. -/
def Fits (n : Nat) (l : List Char) : Prop := (∀ c ∈ l, safe c = true) ∧ l.length ≤ n

instance (n : Nat) (l : List Char) : Decidable (Fits n l) := by unfold Fits; infer_instance

theorem Fits.mono {n m : Nat} {l : List Char} (h : Fits n l) (hnm : n ≤ m) : Fits m l :=
  ⟨h.1, Nat.le_trans h.2 hnm⟩

theorem fits_append {n m : Nat} {a b : List Char} (ha : Fits n a) (hb : Fits m b) :
    Fits (n + m) (a ++ b) := by
  refine ⟨fun c hc => ?_, by simp only [List.length_append]; have := ha.2; have := hb.2; omega⟩
  rcases List.mem_append.mp hc with h | h
  · exact ha.1 c h
  · exact hb.1 c h

theorem fits_of_all {l : List Char} {n : Nat} (h : l.all safe = true) (hl : l.length ≤ n) :
    Fits n l :=
  ⟨List.all_eq_true.mp h, hl⟩

/-! ## Packing -/

theorem pack_le (w : Nat) : ∀ (cur : List Char) (atoms : List (List Char)), cur.length ≤ w →
    (∀ a ∈ atoms, a.length ≤ w) → ∀ c ∈ pack w cur atoms, c.length ≤ w
  | cur, [], hcur, _, c, hc => by
    simp only [pack] at hc
    split at hc
    · cases hc
    · simp only [List.mem_singleton] at hc; exact hc ▸ hcur
  | cur, a :: rest, hcur, hatoms, c, hc => by
    simp only [pack] at hc
    have ha := hatoms a (List.mem_cons_self ..)
    have hrest := fun b hb => hatoms b (List.mem_cons_of_mem a hb)
    split at hc
    · exact pack_le w (cur ++ a) rest (by simp only [List.length_append]; omega) hrest c hc
    · rcases List.mem_append.mp hc with h | h
      · split at h
        · cases h
        · simp only [List.mem_singleton] at h; exact h ▸ hcur
      · exact pack_le w a rest ha hrest c h

theorem pack_chars {p : Char → Prop} (w : Nat) : ∀ (cur : List Char) (atoms : List (List Char)),
    (∀ x ∈ cur, p x) → (∀ a ∈ atoms, ∀ x ∈ a, p x) → ∀ c ∈ pack w cur atoms, ∀ x ∈ c, p x
  | cur, [], hcur, _, c, hc => by
    simp only [pack] at hc
    split at hc
    · cases hc
    · simp only [List.mem_singleton] at hc; exact hc ▸ hcur
  | cur, a :: rest, hcur, hatoms, c, hc => by
    simp only [pack] at hc
    have ha := hatoms a (List.mem_cons_self ..)
    have hrest := fun b hb => hatoms b (List.mem_cons_of_mem a hb)
    split at hc
    · refine pack_chars w (cur ++ a) rest (fun x hx => ?_) hrest c hc
      rcases List.mem_append.mp hx with h | h
      · exact hcur x h
      · exact ha x h
    · rcases List.mem_append.mp hc with h | h
      · split at h
        · cases h
        · simp only [List.mem_singleton] at h; exact h ▸ hcur
      · exact pack_chars w a rest ha hrest c h

theorem pack_fits {w : Nat} {atoms : List (List Char)} (h : ∀ a ∈ atoms, Fits w a) :
    ∀ c ∈ pack w [] atoms, Fits w c := fun c hc =>
  ⟨pack_chars (p := fun x => safe x = true) w [] atoms (by simp) (fun a ha => (h a ha).1) c hc,
    pack_le w [] atoms (by simp) (fun a ha => (h a ha).2) c hc⟩

/-! ## Characters -/

theorem safe_hexDigit : ∀ n, n < 16 → safe (Http.hexDigit n) = true := by decide

theorem fits_hexByte (b : UInt8) : Fits 3 (hexByte b) := by
  refine ⟨fun c hc => ?_, by simp [hexByte]⟩
  simp only [hexByte, List.mem_cons, List.not_mem_nil, or_false] at hc
  have h16 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
  rcases hc with rfl | rfl | rfl
  · decide
  · exact safe_hexDigit _ h16
  · exact safe_hexDigit _ (Nat.mod_lt _ (by decide))

theorem fits_flatMap_hexByte (l : List UInt8) : Fits (3 * l.length) (l.flatMap hexByte) := by
  induction l with
  | nil => exact ⟨by simp, by simp⟩
  | cons b rest ih =>
    have := fits_append (fits_hexByte b) ih
    rw [List.flatMap_cons]
    exact this.mono (by simp only [List.length_cons]; omega)

theorem safe_of_qLiteral {c : Char} (h : qLiteral c = true) : safe c = true := by
  simp only [qLiteral, asciiAlnum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  all_goals first
    | (subst h; decide)
    | (simp only [safe, Bool.and_eq_true, decide_eq_true_eq]; omega)

theorem fits_qChar (c : Char) : Fits 12 (qChar c) := by
  unfold qChar
  split
  · exact ⟨by simp only [List.mem_singleton]; rintro _ rfl; exact safe_of_qLiteral ‹_›, by simp⟩
  · split
    · exact ⟨by simp only [List.mem_singleton]; rintro _ rfl; decide, by simp⟩
    · refine (fits_flatMap_hexByte _).mono ?_
      rw [String.length_utf8EncodeChar]
      have := c.utf8Size_le_four
      omega

theorem fits_encodedWords (s : String) : ∀ w ∈ encodedWords s, Fits 75 w := by
  intro w hw
  simp only [encodedWords, List.mem_map] at hw
  obtain ⟨chunk, hc, rfl⟩ := hw
  have hchunk := pack_fits (w := 63) (atoms := s.toList.map qChar)
    (fun a ha => by
      simp only [List.mem_map] at ha
      obtain ⟨c, _, rfl⟩ := ha
      exact (fits_qChar c).mono (by decide)) chunk hc
  have hs : Fits 10 wordStart := ⟨by decide, by decide⟩
  have he : Fits 2 wordEnd := ⟨by decide, by decide⟩
  exact fits_append (fits_append hs hchunk) he

theorem fits_unstructured (s : String) : ∀ w ∈ unstructured s, Fits raw_max w := by
  unfold unstructured
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    simp only [List.mem_singleton]
    rintro _ rfl
    exact fits_of_all h.1.1 (by rw [String.length_toList]; exact h.2)
  · exact fun w hw => (fits_encodedWords s w hw).mono (by decide)

theorem safe_of_phraseChar {c : Char} (h : phraseChar c = true) : safe c = true := by
  simp only [phraseChar, visible, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with rfl | ⟨⟨h1, h2⟩, _⟩
  · decide
  · simp only [safe, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem fits_address (a : Address) : Fits 254 a.val.toList := by
  have h := a.property
  simp only [Address.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun c hc => ?_, by rw [String.length_toList]; exact h.1.1⟩
  have hv := List.all_eq_true.mp (String.all_bool_eq ▸ h.1.2) c hc
  simp only [visible, safe, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
  omega

theorem fits_bracketed (a : Address) (sep : List Char) (hsep : Fits 1 sep) :
    Fits 257 (('<' :: a.val.toList) ++ '>' :: sep) := by
  have hl : Fits 1 ['<'] := ⟨by decide, by decide⟩
  have hr : Fits 1 ['>'] := ⟨by decide, by decide⟩
  have := fits_append (fits_append hl (fits_address a)) (fits_append hr hsep)
  simpa using this

theorem fits_mailbox (sep : List Char) (hsep : Fits 1 sep) (m : Mailbox) :
    ∀ w ∈ mailbox sep m, Fits raw_max w := by
  have haddr := (fits_bracketed m.address sep hsep).mono (n := 257) (m := raw_max) (by decide)
  unfold mailbox
  split
  · simp only [List.mem_singleton]; rintro _ rfl; exact haddr
  · split
    · rename_i h
      simp only [rawName, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      simp only [List.mem_singleton]
      rintro _ rfl
      have hn : Fits name_max m.name.toList :=
        ⟨fun c hc => safe_of_phraseChar (List.all_eq_true.mp h.1.1 c hc),
          by rw [String.length_toList]; exact h.2⟩
      have hsp : Fits 1 [' '] := ⟨by decide, by decide⟩
      have := fits_append hn (fits_append hsp (fits_bracketed m.address sep hsep))
      exact this.mono (by decide)
    · intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact (fits_encodedWords _ w h).mono (by decide)
      · simp only [List.mem_singleton] at h; exact h ▸ haddr

theorem fits_mailboxes : ∀ (l : List Mailbox), ∀ w ∈ mailboxes l, Fits raw_max w
  | [] => by simp [mailboxes]
  | [m] => fits_mailbox [] ⟨by simp, by simp⟩ m
  | m :: n :: rest => by
    intro w hw
    simp only [mailboxes] at hw
    rcases List.mem_append.mp hw with h | h
    · exact fits_mailbox [','] ⟨by decide, by decide⟩ m w h
    · exact fits_mailboxes (n :: rest) w h

/-- A field whose name fits in 30 characters and whose words in `raw_max` has lines that fit. -/
theorem fits_field {name : String} (hname : Fits 30 name.toList) {words : List (List Char)}
    (h : ∀ w ∈ words, Fits raw_max w) : ∀ l ∈ field name words, Fits 998 l := by
  intro l hl
  cases words with
  | nil =>
    simp only [field, List.mem_singleton] at hl
    subst hl
    exact (fits_append hname (⟨by decide, by decide⟩ : Fits 1 [':'])).mono (by decide)
  | cons w rest =>
    simp only [field, List.mem_cons, List.mem_map] at hl
    have hsep : Fits 2 [':', ' '] := ⟨by decide, by decide⟩
    rcases hl with rfl | ⟨v, hv, rfl⟩
    · have := fits_append hname (fits_append hsep (h w (List.mem_cons_self ..)))
      simpa using this.mono (by decide)
    · have := fits_append (⟨by decide, by decide⟩ : Fits 1 [' ']) (h v (List.mem_cons_of_mem w hv))
      simpa using this.mono (by decide)

theorem fits_listField {name : String} (hname : Fits 30 name.toList) (l : List Mailbox) :
    ∀ x ∈ listField name l, Fits 998 x := by
  unfold listField
  split
  · simp
  · exact fits_field hname (fits_mailboxes l)

/-! ## The date -/

theorem fits_digits {w n : Nat} : Fits w (Digits.fixed 10 w n) := by
  refine ⟨fun c hc => ?_, by rw [Digits.length_fixed]; exact Nat.le_refl w⟩
  have := TimeFormat.mem_fixed_digit hc
  simp only [TimeFormat.isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [safe, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem fits_dayName (i : Nat) : Fits 3 (TimeFormat.dayNames.getD i "").toList := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;>
    simp only [TimeFormat.dayNames, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] <;>
    exact ⟨by decide, by decide⟩

theorem fits_monthName (i : Nat) : Fits 3 (TimeFormat.monthNames.getD i "").toList := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp only [TimeFormat.monthNames, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] <;>
    exact ⟨by decide, by decide⟩

theorem fits_char {c : Char} (h : safe c = true) : Fits 1 [c] :=
  ⟨by simpa using h, by simp⟩

theorem fits_cons {c : Char} {n : Nat} {l : List Char} (h : safe c = true) (hl : Fits n l) :
    Fits (n + 1) (c :: l) := by
  have := fits_append (fits_char h) hl
  simpa [Nat.add_comm] using this

theorem fits_clock (t : Civil.TimeOfDay) : Fits 8 (TimeFormat.clock t) := by
  have h := fits_append (fits_digits (w := 2) (n := t.hour.val))
    (fits_cons (by decide : safe ':' = true) (fits_append (fits_digits (w := 2) (n := t.minute.val))
      (fits_cons (by decide : safe ':' = true) (fits_digits (w := 2) (n := t.second.val)))))
  simpa [TimeFormat.clock, TimeFormat.d2] using h

theorem fits_dateChars (t : Civil.DateTime) : Fits raw_max (dateChars t) := by
  have sp : safe ' ' = true := by decide
  have h := fits_append (fits_dayName t.date.weekday)
    (fits_cons (by decide : safe ',' = true) (fits_cons sp
      (fits_append (fits_digits (w := 2) (n := t.date.day)) (fits_cons sp
        (fits_append (fits_monthName (t.date.month - 1)) (fits_cons sp
          (fits_append (fits_digits (w := 4) (n := t.date.year.toNat)) (fits_cons sp
            (fits_append (fits_clock t.time) (⟨by decide, by decide⟩ : Fits 6 " +0000".toList))))))))))
  simpa [dateChars, TimeFormat.d2, TimeFormat.d4] using h.mono (by decide)

/-! ## Bodies -/

theorem safe_ofNat {n : Nat} (h1 : 32 ≤ n) (h2 : n ≤ 126) : safe (Char.ofNat n) = true := by
  simp only [safe, Url.toNat_ofNat_small (by omega : n < 0xd800), Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem fits_qpByte (last : Bool) (b : UInt8) : Fits 3 (qpByte last b) := by
  unfold qpByte
  split
  · rename_i h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq, Bool.not_eq_true'] at h
    refine (fits_char (safe_ofNat ?_ ?_)).mono (by decide) <;> omega
  · exact fits_hexByte b

theorem fits_qpAtoms : ∀ (l : List UInt8), ∀ a ∈ qpAtoms l, Fits 75 a
  | [] => by simp [qpAtoms]
  | [b] => by
    simp only [qpAtoms, List.mem_singleton]
    rintro _ rfl
    exact (fits_qpByte true b).mono (by decide)
  | b :: c :: rest => by
    simp only [qpAtoms, List.mem_cons]
    rintro a (rfl | ha)
    · exact (fits_qpByte false b).mono (by decide)
    · exact fits_qpAtoms (c :: rest) a (by simpa [qpAtoms] using ha)

theorem fits_soft : ∀ (chunks : List (List Char)), (∀ c ∈ chunks, Fits 75 c) →
    ∀ l ∈ soft chunks, Fits 76 l
  | [], _ => by simp [soft]
  | [c], h => by
    simp only [soft, List.mem_singleton]
    intro l hl
    rw [hl]
    exact (h c (List.mem_singleton_self c)).mono (by decide)
  | c :: d :: rest, h => by
    simp only [soft, List.mem_cons]
    rintro l (rfl | hl)
    · exact fits_append (h c (List.mem_cons_self ..)) (fits_char (by decide))
    · exact fits_soft (d :: rest) (fun x hx => h x (List.mem_cons_of_mem c hx)) l
        (by simpa [soft] using hl)

theorem fits_qpLine (line : List Char) : ∀ l ∈ qpLine line, Fits 76 l := by
  have hc := pack_fits (w := 75) (fits_qpAtoms (line.flatMap String.utf8EncodeChar))
  unfold qpLine
  revert hc
  generalize pack 75 [] _ = chunks
  intro hc
  cases chunks with
  | nil => simp only [List.mem_singleton]; rintro _ rfl; exact ⟨by simp, by simp⟩
  | cons c rest => exact fits_soft (c :: rest) hc

theorem fits_quotedPrintable (text : String) : ∀ l ∈ quotedPrintable text, Fits 998 l := by
  intro l hl
  simp only [quotedPrintable, List.mem_flatMap] at hl
  obtain ⟨line, _, hl⟩ := hl
  exact (fits_qpLine line l hl).mono (by decide)

theorem fits_partHeader : ∀ kind ∈ ["plain", "html"], ∀ l ∈ partHeader kind, Fits 998 l := by
  decide

theorem fits_content (b : Body) : ∀ l ∈ b.content, Fits 998 l := by
  have hp := fits_partHeader "plain" (by simp)
  have hh := fits_partHeader "html" (by simp)
  have hb : Fits 998 ("--".toList ++ boundary) := ⟨by decide, by decide⟩
  have he : Fits 998 ("--".toList ++ boundary ++ "--".toList) := ⟨by decide, by decide⟩
  have hn : Fits 998 [] := ⟨by simp, by simp⟩
  cases b with
  | text t => exact fits_quotedPrintable t
  | html h => exact fits_quotedPrintable h
  | both t h =>
    simp only [Body.content, List.forall_mem_append, List.forall_mem_cons]
    exact ⟨⟨⟨⟨hb, hp⟩, hn, fits_quotedPrintable t⟩, ⟨hb, hh⟩, hn, fits_quotedPrintable h⟩, he,
      fun _ h => nomatch h⟩

theorem fits_fields (b : Body) : ∀ l ∈ b.fields, Fits 998 l := by
  cases b with
  | text t => exact fits_partHeader "plain" (by simp)
  | html h => exact fits_partHeader "html" (by simp)
  | both t h =>
    simp only [Body.fields, List.mem_singleton]
    rintro _ rfl
    exact ⟨by decide, by decide⟩

/-! ## The message -/

theorem fits_header (m : Message) : ∀ l ∈ m.header, Fits 998 l := by
  have name : ∀ n ∈ ["From", "To", "Cc", "Reply-To", "Subject", "Date", "Message-ID"],
      Fits 30 n.toList := by decide
  simp only [Message.header, List.forall_mem_append, List.forall_mem_singleton]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fits_fields _⟩
  · exact fits_field (name "From" (by simp)) (fits_mailbox [] ⟨by simp, by simp⟩ _)
  · exact fits_listField (name "To" (by simp)) _
  · exact fits_listField (name "Cc" (by simp)) _
  · exact fits_listField (name "Reply-To" (by simp)) _
  · exact fits_field (name "Subject" (by simp)) (fits_unstructured _)
  · exact fits_field (name "Date" (by simp))
      (by simp only [List.mem_singleton]; rintro _ rfl; exact fits_dateChars _)
  · exact fits_field (name "Message-ID" (by simp))
      (by
        simp only [List.mem_singleton]
        rintro _ rfl
        exact (fits_bracketed m.messageId [] ⟨by simp, by simp⟩).mono (by decide))
  · exact ⟨by decide, by decide⟩

/-- Every line of a message is printable ASCII of at most 998 characters. -/
theorem Message.lines_fit (m : Message) : ∀ l ∈ m.lines, Fits 998 l := by
  intro l hl
  simp only [Message.lines, List.mem_append, List.mem_cons] at hl
  rcases hl with hl | rfl | hl
  · exact fits_header m l hl
  · exact ⟨by simp, by simp⟩
  · exact fits_content m.body l hl

theorem lineBytes_of_fits {l : List Char} {n : Nat} (h : Fits n l) :
    13 ∉ lineBytes l ∧ 10 ∉ lineBytes l ∧ (lineBytes l).length ≤ n := by
  have byte : ∀ c ∈ l, 32 ≤ (c.toNat.toUInt8).toNat := fun c hc => by
    have := h.1 c hc
    simp only [safe, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Nat.toUInt8, UInt8.toNat_ofNat']
    omega
  refine ⟨fun hm => ?_, fun hm => ?_, by simpa [lineBytes] using h.2⟩
  all_goals
    simp only [lineBytes, List.mem_map] at hm
    obtain ⟨c, hc, he⟩ := hm
    have := byte c hc
    rw [he] at this
    simp at this

/-- What a message is as sent: lines ended by CR LF, with no CR or LF in a line and none over
998 octets. -/
theorem Message.wellformed (m : Message) : Wellformed m.bytes :=
  ⟨m.lines.map lineBytes, by simp [Message.bytes, List.map_map, Function.comp_def], by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨line, hline, rfl⟩ := hl
    exact lineBytes_of_fits (m.lines_fit line hline)⟩

theorem Message.wire_wellformed (m : Message) : Wellformed m.wire.data.toList :=
  m.wellformed

/-! ## The header's fields -/

/-- The field a line of a header starts, as a reader unfolds the header: none for a line that
starts with a space or a tab, which continues the field before it. -/
def fieldName? : List Char → Option (List Char)
  | ' ' :: _ | '\t' :: _ => none
  | l => some (l.takeWhile (· != ':'))

/-- A name of a field: no colon, and it does not start with a space or a tab. -/
def FieldName (n : List Char) : Prop := (∀ c ∈ n, c ≠ ':') ∧ n.head? ≠ some ' ' ∧ n.head? ≠ some '\t'

theorem fieldName?_start {n rest : List Char} (h : FieldName n) :
    fieldName? (n ++ ':' :: rest) = some n := by
  have hwhile : (n ++ ':' :: rest).takeWhile (· != ':') = n := by
    rw [takeWhile_append_of_forall (fun x hx => by simpa using h.1 x hx)]
    simp
  cases n with
  | nil => simp [fieldName?]
  | cons c n =>
    have h1 : c ≠ ' ' := fun e => h.2.1 (by simp [e])
    have h2 : c ≠ '\t' := fun e => h.2.2 (by simp [e])
    rw [← hwhile]
    simp only [List.cons_append, fieldName?]
    split <;> simp_all

theorem fieldNames_field {name : String} (h : FieldName name.toList) (words : List (List Char)) :
    (field name words).filterMap fieldName? = [name.toList] := by
  cases words with
  | nil => simp only [field, List.filterMap_cons, List.filterMap_nil, fieldName?_start h]
  | cons w rest =>
    simp only [field, List.filterMap_cons, fieldName?_start h, List.filterMap_map]
    simp [Function.comp_def, fieldName?]

theorem fieldName_names : ∀ n ∈ ["From", "To", "Cc", "Reply-To", "Subject", "Date", "Message-ID"],
    FieldName n.toList := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide⟩

theorem fieldNames_listField {name : String} (h : FieldName name.toList) (l : List Mailbox) :
    (listField name l).filterMap fieldName? = if l.isEmpty then [] else [name.toList] := by
  unfold listField
  split <;> simp [fieldNames_field h]

theorem fieldNames_fields (b : Body) :
    b.fields.filterMap fieldName? = match b with
      | .both .. => ["Content-Type".toList]
      | _ => ["Content-Type".toList, "Content-Transfer-Encoding".toList] := by
  cases b <;> simp only [Body.fields] <;> decide

/-- The fields of the header are exactly those the message's shape names, whatever its text:
no subject, name or address adds one. -/
theorem Message.header_fields (m : Message) :
    m.header.filterMap fieldName? = m.fieldNames.map String.toList := by
  have names := fieldName_names
  simp only [Message.header, List.filterMap_append,
    fieldNames_field (names "From" (by simp)), fieldNames_listField (names "To" (by simp)),
    fieldNames_listField (names "Cc" (by simp)), fieldNames_listField (names "Reply-To" (by simp)),
    fieldNames_field (names "Subject" (by simp)), fieldNames_field (names "Date" (by simp)),
    fieldNames_field (names "Message-ID" (by simp)), fieldNames_fields, Message.fieldNames,
    List.map_append]
  have hmime : ["MIME-Version: 1.0".toList].filterMap fieldName? = ["MIME-Version".toList] := by
    decide
  rw [hmime]
  cases m.body <;> split <;> split <;> split <;> simp_all

theorem field_ne_nil (name : String) (words : List (List Char)) :
    ∀ l ∈ field name words, l ≠ [] := by
  intro l hl
  cases words with
  | nil => simp only [field, List.mem_singleton] at hl; simp [hl]
  | cons w rest =>
    simp only [field, List.mem_cons, List.mem_map] at hl
    rcases hl with rfl | ⟨v, _, rfl⟩ <;> simp

theorem listField_ne_nil (name : String) (l : List Mailbox) : ∀ x ∈ listField name l, x ≠ [] := by
  unfold listField
  split
  · simp
  · exact field_ne_nil name _

/-- No line of the header is empty, so the header ends only at the empty line after it. -/
theorem Message.header_ne_nil (m : Message) : ∀ l ∈ m.header, l ≠ [] := by
  simp only [Message.header, List.forall_mem_append, List.forall_mem_singleton]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨field_ne_nil _ _, listField_ne_nil _ _⟩, listField_ne_nil _ _⟩,
    listField_ne_nil _ _⟩, field_ne_nil _ _⟩, field_ne_nil _ _⟩, field_ne_nil _ _⟩, by decide⟩, ?_⟩
  cases m.body <;> simp only [Body.fields] <;> decide

/-- Bcc's addresses are in no header. -/
theorem Message.header_bcc (m : Message) (bcc : List Address) : { m with bcc }.header = m.header :=
  rfl

end Lanes.Mail
