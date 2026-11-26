/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Json.PrinterSound

local macro "pos_order" : tactic =>
  `(tactic| ((try simp only [String.Pos.lt_iff_remainingBytes_lt,
      String.Pos.le_iff_remainingBytes_le] at *); omega))

@[expose] public section

namespace Lanes.Json

open Grammar

namespace Parser

variable {s : String}

/-- The characters from `p` to the end. -/
def rest (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

theorem rest_next (p : s.Pos) (h : p ≠ s.endPos) : rest p = p.get h :: rest (p.next h) := by
  have := (String.Pos.splits p).eq_right (p.splits_next_right h)
  simp only [rest, this, String.toList_append, String.toList_singleton, List.singleton_append]

theorem rest_eq_nil {p : s.Pos} : rest p = [] ↔ p = s.endPos := by
  rw [(String.Pos.splits p).eq_endPos_iff, rest, String.toList_eq_nil_iff]

theorem rest_inj {p q : s.Pos} (h : rest p = rest q) : p = q :=
  (String.Pos.splits p).pos_eq_of_eq_right
    ((String.Pos.splits q).of_eq rfl (String.toList_inj.mp h.symm))

theorem rest_startPos : rest s.startPos = s.toList := by
  simp [rest, String.sliceFrom_startPos]

theorem next?_cons {p : s.Pos} {c : Char} {t : List Char} (h : rest p = c :: t) :
    ∃ q, next? p = some (c, q) ∧ rest q.1 = t := by
  have hne : p ≠ s.endPos := fun e => by simp [rest_eq_nil.mpr e] at h
  rw [rest_next p hne] at h
  obtain ⟨rfl, rfl⟩ := List.cons.inj h
  exact ⟨⟨p.next hne, String.Pos.lt_next⟩, by simp [next?, hne], rfl⟩

theorem next?_nil {p : s.Pos} (h : rest p = []) : next? p = none := by
  simp [next?, rest_eq_nil.mp h]

theorem accept_cons {accepted : Char → Bool} {p : s.Pos} {c : Char} {t : List Char}
    (h : rest p = c :: t) (hc : accepted c = true) :
    ∃ q, accept accepted p = some q ∧ rest q.1 = t := by
  obtain ⟨q, hq, ht⟩ := next?_cons h
  exact ⟨q, by simp [accept, hq, hc], ht⟩

theorem accept_none {accepted : Char → Bool} {p : s.Pos}
    (h : ∀ c t, rest p = c :: t → accepted c = false) : accept accepted p = none := by
  cases hr : rest p with
  | nil => simp [accept, next?_nil hr]
  | cons c t =>
    obtain ⟨q, hq, _⟩ := next?_cons hr
    simp [accept, hq, h c t hr]

theorem acceptAll_append {p : s.Pos} {cs t : List Char} (h : rest p = cs ++ t) :
    ∃ q, acceptAll cs p = some q ∧ rest q.1 = t := by
  induction cs generalizing p with
  | nil => exact ⟨⟨p, String.Pos.le_refl p⟩, rfl, h⟩
  | cons c cs ih =>
    obtain ⟨⟨q, hq⟩, hacc, hr⟩ := accept_cons (accepted := (· == c)) h (by simp)
    obtain ⟨⟨r, hr'⟩, hall, hrest⟩ := ih hr
    exact ⟨⟨r, String.Pos.le_trans (String.Pos.le_of_lt hq) hr'⟩, by simp [acceptAll, hacc, hall],
      hrest⟩

/-- No whitespace comes first. -/
def NoWs (t : List Char) : Prop := ∀ c, t.head? = some c → ¬IsWs c

theorem skipWsFrom_ws {start p : s.Pos} {h : start ≤ p} {w t : List Char}
    (hr : rest p = w ++ t) (hw : Ws w) (ht : NoWs t) : rest (skipWsFrom start p h).1 = t := by
  induction w generalizing p with
  | nil =>
    rw [skipWsFrom]
    cases t with
    | nil => simp [next?_nil hr, hr]
    | cons c t =>
      obtain ⟨⟨q, hq⟩, hn, _⟩ := next?_cons hr
      have := ht c rfl
      simp only [IsWs, not_or] at this
      simp [hn, this, hr]
  | cons c w ih =>
    obtain ⟨⟨q, hq⟩, hn, hrq⟩ := next?_cons hr
    rw [skipWsFrom, hn]
    have hc := hw c (by simp)
    simp only [IsWs] at hc
    have : (c == ' ' || c == '\n' || c == '\r' || c == '\t') = true := by
      rcases hc with rfl | rfl | rfl | rfl <;> decide
    simp only [this, ↓reduceIte]
    exact ih hrq fun c hc => hw c (by simp [hc])

theorem skipWs_ws {p : s.Pos} {w t : List Char} (hr : rest p = w ++ t) (hw : Ws w)
    (ht : NoWs t) : rest (skipWs p).1 = t :=
  skipWsFrom_ws hr hw ht

/-! ### Strings -/

theorem lt_of_le_of_lt' {p q r : s.Pos} (h1 : p ≤ q) (h2 : q < r) : p < r := by
  simp only [String.Pos.lt_iff_remainingBytes_lt, String.Pos.le_iff_remainingBytes_le] at h1 h2 ⊢
  omega

theorem hexDigit_cons {p : s.Pos} {c : Char} {t : List Char} {x : Nat} (h : rest p = c :: t)
    (hx : hexDigit? c = some x) : ∃ q, hexDigit p = .ok (x, q) ∧ rest q.1 = t := by
  obtain ⟨q, hq, ht⟩ := next?_cons h
  exact ⟨q, by simp [hexDigit, hq, hx], ht⟩

theorem hex4_complete {p : s.Pos} {hs t : List Char} {n : Nat} (hh : Hex4 hs n)
    (h : rest p = hs ++ t) : ∃ q, hex4 p = .ok (n, q) ∧ rest q.1 = t := by
  cases hh with
  | mk ha hb hc hd =>
    obtain ⟨⟨p1, h1⟩, e1, r1⟩ := hexDigit_cons h ha
    obtain ⟨⟨p2, h2⟩, e2, r2⟩ := hexDigit_cons r1 hb
    obtain ⟨⟨p3, h3⟩, e3, r3⟩ := hexDigit_cons r2 hc
    obtain ⟨⟨p4, h4⟩, e4, r4⟩ := hexDigit_cons r3 hd
    exact ⟨⟨p4, String.Pos.lt_trans h1 (String.Pos.lt_trans h2 (String.Pos.lt_trans h3 h4))⟩,
      by simp [hex4, e1, e2, e3, e4, bind, Except.bind, pure, Except.pure], r4⟩

theorem escape_complete {p : s.Pos} {es t : List Char} {c : Char} (he : Escape es c)
    (h : rest p = es ++ t) : ∃ q, escape p = .ok (c, q) ∧ rest q.1 = t := by
  cases he
  case unicode hh hcode =>
    obtain ⟨⟨p1, h1⟩, e1, r1⟩ := next?_cons h
    obtain ⟨⟨p2, h2⟩, e2, r2⟩ := hex4_complete hh r1
    exact ⟨⟨p2, String.Pos.lt_trans h1 h2⟩, by simp [escape, e1, e2, hcode], r2⟩
  case pair hs ls high low hh hhigh hhigh' hl hlow hlow' =>
    obtain ⟨⟨p1, h1⟩, e1, r1⟩ := next?_cons h
    obtain ⟨⟨p2, h2⟩, e2, r2⟩ := hex4_complete hh (by simpa using r1)
    obtain ⟨⟨p3, h3⟩, e3, r3⟩ := acceptAll_append (cs := ['\\', 'u']) (by simpa using r2)
    obtain ⟨⟨p4, h4⟩, e4, r4⟩ := hex4_complete hl r3
    refine ⟨⟨p4, String.Pos.lt_trans h1 (String.Pos.lt_trans h2
      (lt_of_le_of_lt' h3 h4))⟩, ?_, r4⟩
    have : ¬(high < 0xD800 ∨ 0xE000 ≤ high) := by omega
    simp [escape, e1, e2, lowSurrogate, e3, e4, this, hhigh', hlow, hlow']
  all_goals
    obtain ⟨q, e, r⟩ := next?_cons h
    exact ⟨q, by simp [escape, e], r⟩

theorem strFrom_complete {start p : s.Pos} {hp : start ≤ p} {cs ds t : List Char}
    (hc : Chars cs ds) (h : rest p = cs ++ '"' :: t) (acc : String) :
    ∃ q, strFrom start p hp acc = .ok (acc ++ String.ofList ds, q) ∧ rest q.1 = t := by
  induction hc generalizing p acc with
  | nil =>
    obtain ⟨⟨q, hq⟩, e, r⟩ := next?_cons h
    exact ⟨⟨q, String.Pos.le_of_lt (lt_of_le_of_lt' hp hq)⟩, by rw [strFrom, e]; simp, r⟩
  | @plain c _ _ hu hcs ih =>
    obtain ⟨⟨q, hq⟩, e, r⟩ := next?_cons h
    obtain ⟨q', e', r'⟩ := ih (p := q) (hp := String.Pos.le_of_lt (lt_of_le_of_lt' hp hq))
      r (acc.push c)
    obtain ⟨h32, hq', hb⟩ := hu
    have h1 : (c == '"') = false := by simpa using hq'
    have h2 : (c == '\\') = false := by simpa using hb
    have h3 : ¬c.val < 0x20 := UInt32.not_lt.mpr h32
    refine ⟨q', ?_, r'⟩
    rw [strFrom, e]
    simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
    rw [e']
    simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
    apply String.toList_inj.mp
    simp [String.toList_append, String.toList_push]
  | @escape _ _ _ c hes hcs ih =>
    obtain ⟨⟨q, hq⟩, e, r⟩ := next?_cons h
    obtain ⟨⟨q2, hq2⟩, e2, r2⟩ := escape_complete hes (by simpa using r)
    obtain ⟨q', e', r'⟩ := ih (p := q2)
      (hp := String.Pos.le_of_lt (String.Pos.lt_trans (lt_of_le_of_lt' hp hq) hq2))
      r2 (acc.push c)
    refine ⟨q', ?_, r'⟩
    rw [strFrom, e]
    simp only [show ('\\' == '"') = false by decide, show ('\\' == '\\') = true by decide,
      Bool.false_eq_true, ↓reduceIte, e2]
    rw [e']
    simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
    apply String.toList_inj.mp
    simp [String.toList_append, String.toList_push]

theorem str_complete {p : s.Pos} {cs ds t : List Char} (hc : Chars cs ds)
    (h : rest p = '"' :: cs ++ '"' :: t) :
    ∃ q, str p = .ok (String.ofList ds, q) ∧ rest q.1 = t := by
  obtain ⟨⟨q, hq⟩, e, r⟩ := accept_cons (accepted := (· == '"')) (by simpa using h) (by decide)
  obtain ⟨q', e', r'⟩ := strFrom_complete (start := p) (hp := String.Pos.le_of_lt hq) hc r ""
  exact ⟨q', by simp [str, e, e'], r'⟩

/-! ### Numbers -/

/-- What may follow a number: nothing that would continue it. -/
def NumStop (t : List Char) : Prop :=
  ∀ c, t.head? = some c → ¬IsDigit c ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E'

theorem digitsFrom_complete {md : Nat} {start p : s.Pos} {hp : start ≤ p} {ds t : List Char}
    (h : rest p = ds ++ t) (hd : ∀ c ∈ ds, IsDigit c) (ht : ∀ c, t.head? = some c → ¬IsDigit c)
    (acc count : Nat) (hc : count + ds.length ≤ md) :
    ∃ q, digitsFrom md start p hp acc count =
      .ok (Nat.ofDigitChars 10 ds acc, count + ds.length, q) ∧ rest q.1 = t := by
  induction ds generalizing p acc count with
  | nil =>
    refine ⟨⟨p, hp⟩, ?_, by simpa using h⟩
    rw [digitsFrom]
    cases t with
    | nil => simp [next?_nil (by simpa using h)]
    | cons c t =>
      obtain ⟨q, e, _⟩ := next?_cons (by simpa using h)
      have := ht c rfl
      simp only [IsDigit] at this
      simp [e, this]
  | cons d ds ih =>
    obtain ⟨⟨q, hq⟩, e, r⟩ := next?_cons h
    have hdd := hd d (by simp)
    simp only [IsDigit] at hdd
    obtain ⟨q', e', r'⟩ := ih (p := q) (hp := String.Pos.le_of_lt (lt_of_le_of_lt' hp hq)) r
      (fun c hc => hd c (by simp [hc])) (10 * acc + (d.toNat - '0'.toNat)) (count + 1)
      (by simp at hc; omega)
    refine ⟨q', ?_, r'⟩
    rw [digitsFrom, e]
    simp only [hdd, and_self, ↓reduceIte, show count < md by simp at hc; omega]
    rw [e', Nat.ofDigitChars_cons]
    simp only [List.length_cons]
    congr 3
    omega

theorem whole_complete {md : Nat} {p : s.Pos} {ds t : List Char} (hi : IntPart ds)
    (h : rest p = ds ++ t) (ht : ∀ c, t.head? = some c → ¬IsDigit c) (hc : ds.length ≤ md) :
    ∃ q, whole md p = .ok (Nat.ofDigitChars 10 ds 0, ds.length, q) ∧ rest q.1 = t := by
  obtain ⟨q, e, r⟩ := digitsFrom_complete (md := md) (start := p) (hp := String.Pos.le_refl p) h
    hi.1.2 ht 0 0 (by omega)
  refine ⟨q, ?_, r⟩
  obtain ⟨d, rest', rfl⟩ : ∃ d rest', ds = d :: rest' := List.exists_cons_of_ne_nil hi.1.1
  have hz : ¬(d :: rest').length > 1 ∨ (accept (· == '0') p).isSome = false := by
    by_cases hl : (d :: rest').length > 1
    · refine .inr ?_
      rw [accept_none fun c t' hct => ?_]
      · rfl
      rw [h] at hct
      obtain ⟨rfl, -⟩ := List.cons.inj hct
      have hd : d ≠ '0' := fun hd0 => by
        have := hi.2 (by simp [hd0])
        simp [this] at hl
      simpa using hd
    · exact .inl hl
  rw [whole, e]
  simp only [Nat.zero_add, List.length_cons]
  rcases hz with hz | hz
  · simp only [List.length_cons] at hz
    simp [hz]
  · simp [hz]

theorem fraction_complete {md whole count : Nat} {p : s.Pos} {frac fd t : List Char}
    (hf : Frac frac fd) (h : rest p = frac ++ t)
    (ht : ∀ c, t.head? = some c → ¬IsDigit c ∧ c ≠ '.') (hc : count + fd.length ≤ md) :
    ∃ q, fraction md whole count p = .ok (Nat.ofDigitChars 10 fd whole, fd.length, q) ∧
      rest q.1 = t := by
  cases hf with
  | none =>
    refine ⟨⟨p, String.Pos.le_refl p⟩, ?_, by simpa using h⟩
    have : accept (· == '.') p = none := accept_none fun c t' hct => by
      rw [h, List.nil_append] at hct
      simpa using (ht c (by simp [hct])).2
    rw [fraction, this]
    simp
  | some hd =>
    obtain ⟨⟨p1, h1⟩, e1, r1⟩ := accept_cons (accepted := (· == '.')) h (by decide)
    obtain ⟨q, e, r⟩ := digitsFrom_complete (md := md) (start := p)
      (hp := String.Pos.le_of_lt h1) r1 hd.2 (fun c hc => (ht c hc).1) whole count hc
    refine ⟨q, ?_, r⟩
    rw [fraction, e1]
    simp only [e]
    simp [hd.1]

theorem exponent_complete {md : Nat} {p : s.Pos} {exp ed t : List Char} {e : Int}
    (hx : Exp exp e ed) (h : rest p = exp ++ t) (ht : NumStop t) (hl : ed.length ≤ md)
    (hv : e.natAbs ≤ md) : ∃ q, exponent md p = .ok (e, q) ∧ rest q.1 = t := by
  cases hx with
  | none =>
    have : accept (fun c => c == 'e' || c == 'E') p = none := accept_none fun c t' hct => by
      rw [h, List.nil_append] at hct
      obtain ⟨-, -, h1, h2⟩ := ht c (by simp [hct])
      simp [h1, h2]
    exact ⟨⟨p, String.Pos.le_refl p⟩, by rw [exponent, this], by simpa using h⟩
  | @some marker ds sign hmark hsign hd =>
    obtain ⟨⟨p1, h1⟩, e1, r1⟩ := accept_cons (accepted := fun c => c == 'e' || c == 'E') h
      (by rcases hmark with rfl | rfl <;> decide)
    obtain ⟨d, ds', rfl⟩ := List.exists_cons_of_ne_nil hd.1
    have hdd := hd.2 d (by simp)
    simp only [IsDigit] at hdd
    have hdt : ∀ c, t.head? = some c → ¬IsDigit c := fun c hc => (ht c hc).1
    have hnd : ∀ c, IsDigit c → (c == '-') = false ∧ (c == '-' || c == '+') = false := by
      rintro c ⟨h1, -⟩
      have : c ≠ '-' := by rintro rfl; exact absurd h1 (by decide)
      have : c ≠ '+' := by rintro rfl; exact absurd h1 (by decide)
      simp [*]
    rcases hsign with rfl | rfl | rfl
    · have hn : accept (· == '-') p1 = none := accept_none fun c t' hct => by
        rw [r1] at hct; simp at hct; rw [← hct.1]; exact (hnd d (hd.2 d (by simp))).1
      have hs : accept (fun c => c == '-' || c == '+') p1 = none := accept_none fun c t' hct => by
        rw [r1] at hct; simp at hct; rw [← hct.1]; exact (hnd d (hd.2 d (by simp))).2
      obtain ⟨q, eq, rq⟩ := digitsFrom_complete (md := md) (start := p) (p := p1)
        (hp := String.Pos.le_of_lt h1) (by simpa using r1) hd.2 hdt 0 0 (by simpa using hl)
      refine ⟨q, ?_, rq⟩
      simp only [exponent, e1, hn, hs]
      rw [eq]
      have : ¬Nat.ofDigitChars 10 (d :: ds') 0 > md := by simp at hv; omega
      simp [this]
    · have hn : accept (· == '-') p1 = none := accept_none fun c t' hct => by
        rw [r1] at hct; simp at hct; rw [← hct.1]; decide
      obtain ⟨⟨p2, h2⟩, hs, r2⟩ := accept_cons (accepted := fun c => c == '-' || c == '+') r1
        (by decide)
      obtain ⟨q, eq, rq⟩ := digitsFrom_complete (md := md) (start := p) (p := p2)
        (hp := String.Pos.le_of_lt (String.Pos.lt_trans h1 h2)) (by simpa using r2) hd.2 hdt 0 0
        (by simpa using hl)
      refine ⟨q, ?_, rq⟩
      simp only [exponent, e1, hn, hs]
      rw [eq]
      have : ¬Nat.ofDigitChars 10 (d :: ds') 0 > md := by simp at hv; omega
      simp [this]
    · obtain ⟨⟨p2, h2⟩, hn, r2⟩ := accept_cons (accepted := (· == '-')) r1 (by decide)
      obtain ⟨⟨p2', h2'⟩, hs, r2'⟩ := accept_cons (accepted := fun c => c == '-' || c == '+') r1
        (by decide)
      obtain rfl : p2' = p2 := rest_inj (r2'.trans r2.symm)
      obtain ⟨q, eq, rq⟩ := digitsFrom_complete (md := md) (start := p) (p := p2')
        (hp := String.Pos.le_of_lt (String.Pos.lt_trans h1 h2)) (by simpa using r2) hd.2 hdt 0 0
        (by simpa using hl)
      refine ⟨q, ?_, rq⟩
      simp only [exponent, e1, hn, hs]
      rw [eq]
      have : ¬Nat.ofDigitChars 10 (d :: ds') 0 > md := by simp at hv; omega
      simp [this]

theorem not_digit_e {c : Char} (h : c = 'e' ∨ c = 'E') : ¬IsDigit c ∧ c ≠ '.' := by
  rcases h with rfl | rfl <;> decide

theorem num_complete {md : Nat} {p : s.Pos} {cs t : List Char} {n : JsonNumber}
    (hn : Number md cs n) (h : rest p = cs ++ t) (ht : NumStop t) :
    ∃ q, num md p = .ok (n, q) ∧ rest q.1 = t := by
  cases hn with
  | @mk int frac fd exp ed e negative hi hf hx h1 h2 h3 =>
    have hexp : ∀ c, (exp ++ t).head? = some c → ¬IsDigit c ∧ c ≠ '.' := by
      cases hx with
      | none => exact fun c hc => ⟨(ht c (by simpa using hc)).1, (ht c (by simpa using hc)).2.1⟩
      | some sign hmark _ _ => intro c hc; simp at hc; exact hc ▸ not_digit_e hmark
    have hfrac : ∀ c, (frac ++ exp ++ t).head? = some c → ¬IsDigit c := by
      cases hf with
      | none => exact fun c hc => (hexp c (by simpa using hc)).1
      | some _ => intro c hc; simp at hc; rw [← hc]; decide
    obtain ⟨d, int', hint⟩ := List.exists_cons_of_ne_nil hi.1.1
    have hdd := hi.1.2 d (by simp [hint])
    have hnm : (d == '-') = false := by
      have : d ≠ '-' := by rintro rfl; exact absurd hdd.1 (by decide)
      simpa using this
    have hsplit : ∃ p1 : s.Pos, ∃ hp1 : p ≤ p1, rest p1 = int ++ (frac ++ exp ++ t) ∧
        num md p = unsigned md negative p p1 hp1 := by
      cases negative
      · have hacc : accept (· == '-') p = none := accept_none fun c t' hct => by
          rw [h, hint] at hct; simp at hct; rw [← hct.1]; exact hnm
        exact ⟨p, String.Pos.le_refl p, by simpa using h, by rw [num, hacc]⟩
      · obtain ⟨⟨p1, hp1⟩, hacc, r1⟩ := accept_cons (accepted := (· == '-')) h (by decide)
        exact ⟨p1, String.Pos.le_of_lt hp1, by simpa using r1, by rw [num, hacc]⟩
    obtain ⟨p1, hp1, r1, hnum⟩ := hsplit
    obtain ⟨⟨p2, h2'⟩, ew, rw'⟩ := whole_complete (md := md) hi r1 hfrac (by simp at h1; omega)
    obtain ⟨⟨p3, h3'⟩, ef, rf⟩ := fraction_complete (md := md) (whole := Nat.ofDigitChars 10 int 0)
      (count := int.length) hf (by simpa using rw') hexp (by simpa using h1)
    obtain ⟨⟨p4, h4'⟩, ee, re⟩ := exponent_complete (md := md) hx rf ht h2 h3
    refine ⟨⟨p4, String.Pos.le_trans hp1 (String.Pos.le_trans h2' (String.Pos.le_trans h3' h4'))⟩,
      ?_, re⟩
    rw [hnum, unsigned, ew]
    simp only [ef, ee, Nat.ofDigitChars_append]

end Parser

end Lanes.Json
