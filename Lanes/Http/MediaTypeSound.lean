/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Http.MediaType
public import Lanes.Http.UrlSound

/-!
What `Lanes.MediaType` is proved to do: `parse` reads what `format` writes, with the type, the
subtype and the names in lowercase (`parse_format`), so the case they are written in does not
matter (`parse_format_eq`), and what `parse` reads `format` writes back (`parse_print`).
-/

@[expose] public section

namespace Lanes.MediaType

open Url (lowerChar toNat_ofNat_small char_le)

/-! ### Characters -/

theorem toNat_eq {c : Char} {n : Nat} (h : c.toNat = n) (hn : n < 0xd800) : c = Char.ofNat n := by
  rw [← Char.toNat_inj, toNat_ofNat_small hn, h]

theorem isQdtext_of {c : Char} (h : isQuotable c) (h1 : c ≠ '"') (h2 : c ≠ '\\') : isQdtext c := by
  have e1 : c.toNat ≠ 34 := fun e => h1 (toNat_eq e (by decide))
  have e2 : c.toNat ≠ 92 := fun e => h2 (toNat_eq e (by decide))
  have t1 : ' '.toNat = 32 := rfl
  have t2 : '~'.toNat = 126 := rfl
  have t3 : '#'.toNat = 35 := rfl
  have t4 : '['.toNat = 91 := rfl
  have t5 : ']'.toNat = 93 := rfl
  simp only [isQuotable, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le, t1, t2] at h
  rcases h with (h | h) | h
  · simp [isQdtext, h]
  · have : c.toNat = 32 ∨ c.toNat = 33 ∨ (35 ≤ c.toNat ∧ c.toNat ≤ 91) ∨ (93 ≤ c.toNat ∧ c.toNat ≤ 126) := by
      omega
    rcases this with e | e | e | e
    · rw [toNat_eq e (by decide)]; decide
    · rw [toNat_eq e (by decide)]; decide
    · simp [isQdtext, char_le, t3, t4, e.1, e.2]
    · simp [isQdtext, char_le, t5, t2, e.1, e.2]
  · simp [isQdtext, h]

theorem isTchar_lowerChar {c : Char} (h : isTchar c) : isTchar (lowerChar c) := by
  unfold lowerChar
  split
  · rename_i hc
    have hc : 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, char_le] at hc; exact hc
    have := toNat_ofNat_small (n := c.toNat + 32) (by omega)
    simp only [isTchar, Url.isAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le, this]
    exact .inl (.inl (.inl ⟨by simp; omega, by simp; omega⟩))
  · exact h

theorem not_ws_of_tchar {c : Char} (h : isTchar c) : isWs c = false := by
  cases e : isWs c
  · rfl
  · simp only [isWs, Bool.or_eq_true, beq_iff_eq] at e
    rcases e with rfl | rfl <;> simp [isTchar, Url.isAlpha, Url.isDigit] at h

/-! ### Reading what `format` writes -/

/-- Text that ends a token: nothing, or a character that is not in one. -/
def EndsToken (r : List Char) : Prop := r = [] ∨ ∃ c r', r = c :: r' ∧ isTchar c = false

theorem token_append {t : List Char} (r : List Char) (h : ∀ c ∈ t, isTchar c) (hr : EndsToken r) :
    token (t ++ r) = (t, r) := by
  induction t with
  | nil =>
    rcases hr with rfl | ⟨c, r', rfl, hc⟩
    · rfl
    · simp [token, hc]
  | cons c t ih =>
    have hc : isTchar c := h c (by simp)
    simp [token, hc, ih (fun x hx => h x (by simp [hx]))]

theorem skipWs_of {c : Char} (h : isWs c = false) (r : List Char) : skipWs (c :: r) = c :: r := by
  simp [skipWs, h]

def esc (c : Char) : List Char := if c == '"' || c == '\\' then ['\\', c] else [c]

theorem quote_eq (v : List Char) : quote v = '"' :: v.flatMap esc ++ ['"'] := rfl

theorem quoted_esc {v : List Char} (rest : List Char) (h : ∀ c ∈ v, isQuotable c) :
    quoted (v.flatMap esc ++ '"' :: rest) = some (v, rest) := by
  induction v with
  | nil => simp [quoted]
  | cons c v ih =>
    have hc := h c (by simp)
    have ih := ih (fun x hx => h x (by simp [hx]))
    by_cases e : c == '"' || c == '\\'
    · have he : esc c = ['\\', c] := by simp [esc, e]
      simp only [List.flatMap_cons, he, List.cons_append, List.nil_append]
      rw [quoted, ih, hc]
      rfl
    · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at e
      have he : esc c = [c] := by simp [esc, e.1, e.2]
      simp only [List.flatMap_cons, he, List.cons_append, List.nil_append]
      rw [quoted, ih, isQdtext_of hc e.1 e.2]
      · rfl
      · intro e'; exact e.1 e'
      · intro _ _ e' _; exact e.2 e'
theorem tchar_ne_quote {c : Char} (h : isTchar c) : c ≠ '"' := by
  rintro rfl; simp [isTchar, Url.isAlpha, Url.isDigit] at h

theorem endsToken_of {rest : List Char} (hr : rest = [] ∨ ∃ r, rest = ';' :: r) : EndsToken rest := by
  rcases hr with rfl | ⟨r, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨';', r, rfl, by decide⟩

theorem value_valueChars {v : String} (hv : v.toList.all isQuotable) (rest : List Char)
    (hr : rest = [] ∨ ∃ r, rest = ';' :: r) : value (valueChars v ++ rest) = some (v.toList, rest) := by
  unfold valueChars
  split
  · rename_i ht
    simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at ht
    have hne : v.toList ≠ [] := by simpa using ht.1
    obtain ⟨c, cs, e⟩ := List.exists_cons_of_ne_nil hne
    have htok := token_append rest ht.2 (endsToken_of hr)
    rw [value, htok]
    · simp [hne]
    · rw [e]; intro r' e'
      simp only [List.cons_append, List.cons.injEq] at e'
      exact tchar_ne_quote (ht.2 c (by simp [e])) e'.1
  · simp only [quote_eq, List.cons_append, List.append_assoc]
    rw [value, List.nil_append, quoted_esc rest (List.all_eq_true.mp hv)]

def paramChars (p : String × String) : List Char := ';' :: ' ' :: p.1.toList ++ '=' :: valueChars p.2

theorem parseParams_chars (ps : List (String × String))
    (h : ps.all fun (n, v) => isToken n && v.toList.all isQuotable) :
    parseParams (ps.flatMap paramChars) = some (ps.map fun (n, v) => (n.toList, v.toList)) := by
  induction ps with
  | nil => rw [parseParams]; simp
  | cons p ps ih =>
    obtain ⟨n, v⟩ := p
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨⟨hn, hv⟩, hps⟩ := h
    simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hn
    have hne : n.toList ≠ [] := by simpa using hn.1
    obtain ⟨c, cs, e⟩ := List.exists_cons_of_ne_nil hne
    have hc : isTchar c := hn.2 c (by simp [e])
    have hrest : ps.flatMap paramChars = [] ∨ ∃ r, ps.flatMap paramChars = ';' :: r := by
      cases ps with
      | nil => exact .inl rfl
      | cons q qs =>
        exact .inr ⟨' ' :: (q.1.toList ++ '=' :: (valueChars q.2 ++ qs.flatMap paramChars)),
          by simp [paramChars]⟩
    have hval := value_valueChars hv _ hrest
    have htok := token_append ('=' :: (valueChars v ++ ps.flatMap paramChars)) hn.2 (.inr ⟨'=', _, rfl, by decide⟩)
    have hskip : skipWs (n.toList ++ '=' :: (valueChars v ++ ps.flatMap paramChars))
        = n.toList ++ '=' :: (valueChars v ++ ps.flatMap paramChars) := by
      rw [e, List.cons_append, skipWs_of (not_ws_of_tchar hc)]
    simp only [List.flatMap_cons, paramChars, List.cons_append, List.append_assoc]
    rw [parseParams, ite_eq_right_iff.mpr (by simp)]
    have hsemi := skipWs_of (show isWs ';' = false by decide)
      (' ' :: (n.toList ++ '=' :: (valueChars v ++ List.flatMap paramChars ps)))
    split
    · rename_i r heq
      rw [hsemi, List.cons.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      have hsp : skipWs (' ' :: (n.toList ++ '=' :: (valueChars v ++ List.flatMap paramChars ps)))
          = n.toList ++ '=' :: (valueChars v ++ List.flatMap paramChars ps) := by
        rw [skipWs]
        simp only [show isWs ' ' = true by decide, ite_true]
        exact hskip
      split
      · rename_i heq
        rw [hsp, htok] at heq
        simp only [Prod.mk.injEq] at heq
        exact absurd heq.1 hne
      · rename_i name r' heq
        rw [hsp, htok] at heq
        simp only [Prod.mk.injEq, List.cons.injEq, true_and] at heq
        obtain ⟨rfl, rfl⟩ := heq
        split
        · rename_i v' r'' heq
          rw [hval] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          rw [ih hps]
          simp
        · rename_i heq
          rw [hval] at heq
          cases heq
      · rename_i h1 h2
        rw [hsp, htok] at h1 h2
        exact (h2 _ _ rfl).elim
    · rename_i hno
      exact absurd hsemi (hno _)
theorem chars_eq (m : MediaType) :
    m.chars = m.type.toList ++ '/' :: (m.subtype.toList ++ m.params.flatMap paramChars) := by
  simp only [chars, List.append_assoc, List.cons_append]
  rfl

theorem isToken_spec {s : String} (h : isToken s) : s.toList ≠ [] ∧ ∀ c ∈ s.toList, isTchar c := by
  simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  exact ⟨by simpa using h.1, h.2⟩

theorem parseRaw_chars {m : MediaType} (h : m.valid) : parseRaw m.chars = some m.lower := by
  simp only [valid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ht, hs⟩, hp⟩, -⟩ := h
  have hp' : m.params.all fun (n, v) => isToken n && v.toList.all isQuotable := hp
  have hrest : m.params.flatMap paramChars = [] ∨ ∃ r, m.params.flatMap paramChars = ';' :: r := by
    cases m.params with
    | nil => exact .inl rfl
    | cons q qs =>
      exact .inr ⟨' ' :: (q.1.toList ++ '=' :: (valueChars q.2 ++ qs.flatMap paramChars)),
        by simp [paramChars]⟩
  have h1 := token_append ('/' :: (m.subtype.toList ++ m.params.flatMap paramChars))
    (isToken_spec ht).2 (.inr ⟨'/', _, rfl, by decide⟩)
  have h2 := token_append (m.params.flatMap paramChars) (isToken_spec hs).2 (endsToken_of hrest)
  rw [chars_eq, parseRaw, h1]
  simp only [h2, parseParams_chars _ hp', Option.map_some, List.map_map, lower]
  simp [Function.comp_def]

theorem isToken_lower {s : String} (h : isToken s) : isToken (String.ofList (Url.lower s.toList)) := by
  obtain ⟨h1, h2⟩ := isToken_spec h
  simp only [isToken, Url.lower, String.toList_ofList, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true, List.mem_map]
  refine ⟨by simpa using h1, ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  exact isTchar_lowerChar (h2 c hc)

theorem names_lower (m : MediaType) : m.lower.names = m.names := by
  simp [names, lower, Url.lower_lower, Function.comp_def]

theorem lower_valid {m : MediaType} (h : m.valid) : m.lower.valid := by
  have hn := names_lower m
  simp only [valid, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨ht, hs⟩, hp⟩, hd⟩ := h
  refine ⟨⟨⟨isToken_lower ht, isToken_lower hs⟩, ?_⟩, by rw [hn]; exact hd⟩
  simp only [lower, List.all_map, List.all_eq_true, Function.comp_def, Bool.and_eq_true] at hp ⊢
  intro x hx
  exact ⟨isToken_lower (hp x hx).1, (hp x hx).2⟩

theorem lower_lower (m : MediaType) : m.lower.lower = m.lower := by
  simp [lower, Url.lower_lower, Function.comp_def]

/-- What `format` writes, `parse` reads, with the type, subtype and names in lowercase. -/
theorem parse_format {m : MediaType} (h : m.valid) : parse m.format = some m.lower := by
  simp [parse, format, parseRaw_chars h, lower_valid h, lower_lower]

/-- Case-insensitivity (RFC 9110 §8.3.1): media types that differ only in the case of their
type, subtype and names read the same. -/
theorem parse_format_eq {m₁ m₂ : MediaType} (h₁ : m₁.valid) (h₂ : m₂.valid)
    (h : m₁.lower = m₂.lower) : parse m₁.format = parse m₂.format := by
  rw [parse_format h₁, parse_format h₂, h]

theorem valid_of_parse {s : String} {m : MediaType} (h : parse s = some m) :
    m.valid ∧ m.lower = m := by
  simp only [parse, Option.filter_eq_some_iff, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- What `parse` reads, `format` writes so that it reads back the same. -/
theorem parse_print {s : String} {m : MediaType} (h : parse s = some m) : parse m.format = some m := by
  obtain ⟨hv, hl⟩ := valid_of_parse h
  rw [parse_format hv, hl]

end Lanes.MediaType
