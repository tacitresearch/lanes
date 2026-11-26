/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Civil
public import Lanes.Data.Digits
public import Lanes.Data.List.Basic

/-!
Timestamps as text: RFC 3339 §5.6 (`2006-01-02T15:04:05.999999999-07:00`) and the HTTP date of
RFC 9110 §5.6.7, written as IMF-fixdate (`Sun, 06 Nov 1994 08:49:37 GMT`) and read in that form
and the two obsolete ones (RFC 850 and asctime). Each reads back what it writes
(`parseRfc3339_print`, `parseHttpDate_print`), and what is read is a valid date and time: no
30 February, no hour 24.

Choices where a reader could differ (`docs/decisions/new-differential-tests-against-go.md`): a
leap second (`:60`) is refused, since POSIX time has no place for it; RFC 3339's lowercase `t`
and `z` are read; digits of a fraction past the ninth are dropped, as Go does; an HTTP date whose
day name is not its date's is refused; an RFC 850 two-digit year is the latest year with those
digits at most 50 years after `nowYear` (RFC 9110 §5.6.7).
-/

@[expose] public section

namespace Lanes.TimeFormat

open Civil Digits

def isDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

theorem isDigit_char {d : Nat} (h : d < 10) : isDigit (char d) = true := by
  have : ∀ d, d < 10 → isDigit (char d) = true := by decide
  exact this d h

/-- A fixed number of decimal digits; the callers give the length. -/
def num? (cs : List Char) : Option Nat := ofChars? 10 cs

/-- An offset from UTC in minutes, less than a day either way. -/
abbrev Offset := {m : Int // -1440 < m ∧ m < 1440}

structure Timestamp where
  dateTime : DateTime
  nanos : Fin 1000000000
  offset : Offset
  deriving DecidableEq

/-- Seconds since the epoch of the instant; `nanos` are after it. -/
def Timestamp.toUnix (t : Timestamp) : Int := t.dateTime.toUnix - t.offset.val * 60

def d2 (n : Nat) : List Char := fixed 10 2 n

def d4 (n : Nat) : List Char := fixed 10 4 n

def clock (t : TimeOfDay) : List Char :=
  d2 t.hour.val ++ ':' :: d2 t.minute.val ++ ':' :: d2 t.second.val

def trimZeros (l : List Char) : List Char := (l.reverse.dropWhile (· == '0')).reverse

def fractionChars (n : Nat) : List Char := if n = 0 then [] else '.' :: trimZeros (fixed 10 9 n)

def offsetChars (o : Int) : List Char :=
  if o = 0 then ['Z']
  else (if o < 0 then '-' else '+') :: d2 (o.natAbs / 60) ++ ':' :: d2 (o.natAbs % 60)

def rfc3339Chars (t : Timestamp) : List Char :=
  d4 t.dateTime.date.year.toNat ++ '-' :: d2 t.dateTime.date.month ++ '-' :: d2 t.dateTime.date.day
    ++ 'T' :: clock t.dateTime.time ++ fractionChars t.nanos.val ++ offsetChars t.offset.val

def InRange (d : Date) : Prop := 0 ≤ d.year ∧ d.year ≤ 9999

instance (d : Date) : Decidable (InRange d) := by unfold InRange; infer_instance

/-- RFC 3339 with as few fraction digits as the nanoseconds need, and `Z` for UTC; `none` for a
year that four digits cannot write. -/
def printRfc3339? (t : Timestamp) : Option String :=
  if InRange t.dateTime.date then some (String.ofList (rfc3339Chars t)) else none

def clock? (h1 h2 m1 m2 s1 s2 : Char) : Option TimeOfDay := do
  let h ← num? [h1, h2]
  let m ← num? [m1, m2]
  let s ← num? [s1, s2]
  if hb : h < 24 ∧ m < 60 ∧ s < 60 then some ⟨⟨h, hb.1⟩, ⟨m, hb.2.1⟩, ⟨s, hb.2.2⟩⟩ else none

def fraction? : List Char → Option (Nat × List Char)
  | '.' :: rest =>
    if rest.takeWhile isDigit = [] then none
    else (num? ((rest.takeWhile isDigit ++ List.replicate 9 '0').take 9)).map
      fun n => (n, rest.dropWhile isDigit)
  | rest => some (0, rest)

def offset? : List Char → Option Offset
  | ['Z'] | ['z'] => some ⟨0, by decide⟩
  | [s, h1, h2, ':', m1, m2] => do
    let h ← num? [h1, h2]
    let m ← num? [m1, m2]
    if hb : h < 24 ∧ m < 60 then
      if s = '+' then some ⟨(h * 60 + m : Nat), by omega⟩
      else if s = '-' then some ⟨-((h * 60 + m : Nat) : Int), by omega⟩
      else none
    else none
  | _ => none

def parseRfc3339 (s : String) : Option Timestamp :=
  match s.toList with
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: e1 :: e2 :: t :: h1 :: h2 :: ':' :: n1 :: n2
      :: ':' :: s1 :: s2 :: rest => do
    if t ≠ 'T' ∧ t ≠ 't' then none
    let date ← Date.mk? (← num? [y1, y2, y3, y4]) (← num? [m1, m2]) (← num? [e1, e2])
    let time ← clock? h1 h2 n1 n2 s1 s2
    let (nanos, rest) ← fraction? rest
    let offset ← offset? rest
    if h : nanos < 1000000000 then some ⟨⟨date, time⟩, ⟨nanos, h⟩, offset⟩ else none
  | _ => none

/-! ### HTTP dates -/

def dayNames : List String := ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]

def longDayNames : List String :=
  ["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]

def monthNames : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def nameOf? (names : List String) (cs : List Char) : Option Nat :=
  (List.range names.length).find? fun i => (names.getD i "").toList == cs

def imfChars (t : DateTime) : List Char :=
  (dayNames.getD t.date.weekday "").toList ++ ',' :: ' ' :: d2 t.date.day ++ ' '
    :: (monthNames.getD (t.date.month - 1) "").toList ++ ' ' :: d4 t.date.year.toNat ++ ' '
    :: clock t.time ++ [' ', 'G', 'M', 'T']

/-- IMF-fixdate, the form RFC 9110 says to send. -/
def printHttpDate? (t : DateTime) : Option String :=
  if InRange t.date then some (String.ofList (imfChars t)) else none

def checked (weekday : Nat) (year : Int) (month day : Nat) (time : TimeOfDay) : Option DateTime := do
  let date ← Date.mk? year month day
  if date.weekday = weekday then some ⟨date, time⟩ else none

def imf? : List Char → Option DateTime
  | w1 :: w2 :: w3 :: ',' :: ' ' :: e1 :: e2 :: ' ' :: m1 :: m2 :: m3 :: ' ' :: y1 :: y2 :: y3 :: y4
      :: ' ' :: h1 :: h2 :: ':' :: n1 :: n2 :: ':' :: s1 :: s2 :: [' ', 'G', 'M', 'T'] => do
    checked (← nameOf? dayNames [w1, w2, w3]) (← num? [y1, y2, y3, y4])
      ((← nameOf? monthNames [m1, m2, m3]) + 1) (← num? [e1, e2]) (← clock? h1 h2 n1 n2 s1 s2)
  | _ => none

/-- RFC 9110: a two-digit year more than 50 years ahead is the century before. -/
def fullYear (nowYear : Int) (yy : Nat) : Int := nowYear + 50 - (nowYear + 50 - yy) % 100

def rfc850? (nowYear : Int) (cs : List Char) : Option DateTime :=
  match cs.dropWhile (· != ',') with
  | ',' :: ' ' :: e1 :: e2 :: '-' :: m1 :: m2 :: m3 :: '-' :: y1 :: y2 :: ' ' :: h1 :: h2 :: ':'
      :: n1 :: n2 :: ':' :: s1 :: s2 :: [' ', 'G', 'M', 'T'] => do
    checked (← nameOf? longDayNames (cs.takeWhile (· != ','))) (fullYear nowYear (← num? [y1, y2]))
      ((← nameOf? monthNames [m1, m2, m3]) + 1) (← num? [e1, e2]) (← clock? h1 h2 n1 n2 s1 s2)
  | _ => none

def asctime? : List Char → Option DateTime
  | w1 :: w2 :: w3 :: ' ' :: m1 :: m2 :: m3 :: ' ' :: e1 :: e2 :: ' ' :: h1 :: h2 :: ':' :: n1 :: n2
      :: ':' :: s1 :: s2 :: [' ', y1, y2, y3, y4] => do
    checked (← nameOf? dayNames [w1, w2, w3]) (← num? [y1, y2, y3, y4])
      ((← nameOf? monthNames [m1, m2, m3]) + 1) (← if e1 = ' ' then num? [e2] else num? [e1, e2])
      (← clock? h1 h2 n1 n2 s1 s2)
  | _ => none

/-- `nowYear` places a two-digit year (RFC 850 form); the other forms do not use it. -/
def parseHttpDate (nowYear : Int) (s : String) : Option DateTime :=
  (imf? s.toList).orElse fun _ => (rfc850? nowYear s.toList).orElse fun _ => asctime? s.toList

/-! ### Reading back -/

theorem fixed_two (n : Nat) : ∃ a b, d2 n = [a, b] ∧ num? [a, b] = some (n % 100) := by
  have hv : num? (d2 n) = some (n % 100) := ofChars?_fixed (b := 10) (by omega) (by omega) 2 n
  have hl : (d2 n).length = 2 := length_fixed 10 2 n
  generalize d2 n = l at hv hl
  match l, hl with
  | [a, b], _ => exact ⟨a, b, rfl, hv⟩

theorem fixed_four (n : Nat) :
    ∃ a b c e, d4 n = [a, b, c, e] ∧ num? [a, b, c, e] = some (n % 10000) := by
  have hv : num? (d4 n) = some (n % 10000) := ofChars?_fixed (b := 10) (by omega) (by omega) 4 n
  have hl : (d4 n).length = 4 := length_fixed 10 4 n
  generalize d4 n = l at hv hl
  match l, hl with
  | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl, hv⟩

theorem clock_spec (t : TimeOfDay) : ∃ h1 h2 m1 m2 s1 s2, clock t = [h1, h2, ':', m1, m2, ':', s1, s2]
    ∧ clock? h1 h2 m1 m2 s1 s2 = some t := by
  obtain ⟨h1, h2, hh, vh⟩ := fixed_two t.hour.val
  obtain ⟨m1, m2, hm, vm⟩ := fixed_two t.minute.val
  obtain ⟨s1, s2, hs, vs⟩ := fixed_two t.second.val
  refine ⟨h1, h2, m1, m2, s1, s2, by simp [clock, hh, hm, hs], ?_⟩
  have := t.hour.isLt; have := t.minute.isLt; have := t.second.isLt
  rw [Nat.mod_eq_of_lt (by omega)] at vh vm vs
  simp only [clock?, vh, vm, vs, Option.bind_eq_bind, Option.bind_some]
  rw [dite_eq_left ⟨t.hour.isLt, t.minute.isLt, t.second.isLt⟩]

theorem date_mk? (d : Date) : Date.mk? d.year d.month d.day = some d := by
  simp [Date.mk?, d.valid]

theorem trimZeros_append (l : List Char) :
    trimZeros l ++ List.replicate (l.length - (trimZeros l).length) '0' = l := by
  have h := List.takeWhile_append_dropWhile (p := (· == '0')) (l := l.reverse)
  rw [takeWhile_beq_eq_replicate] at h
  have hl := congrArg List.reverse h
  rw [List.reverse_append, List.reverse_replicate, List.reverse_reverse] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_append, List.length_reverse, List.length_replicate] at hlen
  rw [trimZeros, show l.length - (l.reverse.dropWhile (· == '0')).reverse.length
    = (l.reverse.takeWhile (· == '0')).length by simp only [List.length_reverse]; omega]
  exact hl

theorem mem_fixed_digit {w n : Nat} {c : Char} (h : c ∈ fixed 10 w n) : isDigit c = true := by
  simp only [fixed, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  exact isDigit_char (lt_of_mem_split (by omega) hd)

theorem mem_trimZeros {l : List Char} {c : Char} (h : c ∈ trimZeros l) : c ∈ l := by
  rw [← trimZeros_append l]; exact List.mem_append_left _ h

theorem split_zero (b k : Nat) : split b k 0 = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [split, Nat.zero_div, ih, Nat.zero_mod, List.replicate_succ']

theorem ofChars?_zeros (k : Nat) : ofChars? 10 (List.replicate k '0') = some 0 := by
  have := ofChars?_fixed (b := 10) (by omega) (by omega) k 0
  rwa [fixed, split_zero, List.map_replicate, show char 0 = '0' by rfl, Nat.zero_mod] at this

theorem take_trimZeros {l : List Char} (hl : l.length = 9) :
    (trimZeros l ++ List.replicate 9 '0').take 9 = l := by
  have htrim := trimZeros_append l
  have hlen : (trimZeros l).length ≤ 9 := by
    have := congrArg List.length htrim
    simp only [List.length_append, List.length_replicate] at this; omega
  rw [hl] at htrim
  rw [List.take_append, List.take_of_length_le hlen, List.take_replicate,
    Nat.min_eq_left (Nat.sub_le _ _)]
  exact htrim

theorem trimZeros_ne_nil {n : Nat} (hn : n < 1000000000) (h0 : n ≠ 0) :
    trimZeros (fixed 10 9 n) ≠ [] := by
  intro h
  have htrim := trimZeros_append (fixed 10 9 n)
  rw [h, List.nil_append, List.length_nil, Nat.sub_zero, length_fixed] at htrim
  have hv := ofChars?_fixed (b := 10) (by omega) (by omega) 9 n
  rw [← htrim, Nat.mod_eq_of_lt (by omega), ofChars?_zeros] at hv
  exact h0 (Option.some.inj hv).symm

theorem fraction?_chars {n : Nat} (hn : n < 1000000000) {rest : List Char}
    (hr : ∀ c ∈ rest.head?, isDigit c = false) (hdot : rest.head? ≠ some '.') :
    fraction? (fractionChars n ++ rest) = some (n, rest) := by
  have hnil : rest.takeWhile isDigit = [] := by
    cases rest with
    | nil => rfl
    | cons c rest => simp [hr c rfl]
  have hdrop : rest.dropWhile isDigit = rest := by
    cases rest with
    | nil => rfl
    | cons c rest => simp [hr c rfl]
  unfold fractionChars
  split
  · rename_i h0
    subst h0
    cases rest with
    | nil => rfl
    | cons c rest => simp only [List.nil_append]; unfold fraction?; split <;> simp_all
  · rename_i h0
    have hall : ∀ c ∈ trimZeros (fixed 10 9 n), isDigit c = true :=
      fun c hc => mem_fixed_digit (mem_trimZeros hc)
    simp only [List.cons_append, fraction?, takeWhile_append_of_forall hall, hnil, List.append_nil,
      dropWhile_append_of_forall hall, hdrop, trimZeros_ne_nil hn h0, ite_false,
      take_trimZeros (length_fixed 10 9 n)]
    simp [num?, ofChars?_fixed (b := 10) (by omega) (by omega), Nat.mod_eq_of_lt hn]

theorem offset?_chars (o : Offset) : offset? (offsetChars o.val) = some o := by
  obtain ⟨o, h1, h2⟩ := o
  unfold offsetChars
  split
  · rename_i h0
    simp only at h0
    subst h0; rfl
  · rename_i h0
    obtain ⟨a, b, ha, va⟩ := fixed_two (o.natAbs / 60)
    obtain ⟨c, e, hc, vc⟩ := fixed_two (o.natAbs % 60)
    rw [Nat.mod_eq_of_lt (by omega)] at va vc
    rw [ha, hc]
    simp only [List.cons_append, List.nil_append, offset?, va, vc, Option.bind_eq_bind, Option.bind_some]
    rw [dite_eq_left ⟨by omega, by omega⟩]
    by_cases hneg : o < 0
    · simp only [hneg, ite_true, show ('-' : Char) ≠ '+' by decide, ite_false, Option.some.injEq]
      apply Subtype.ext; simp only; omega
    · simp only [hneg, ite_false, ite_true, Option.some.injEq]
      apply Subtype.ext; simp only; omega

theorem head_offsetChars (o : Int) :
    (∀ c ∈ (offsetChars o).head?, isDigit c = false) ∧ (offsetChars o).head? ≠ some '.' := by
  unfold offsetChars
  split
  · decide
  · split <;> simp [isDigit]

theorem parseRfc3339_print {t : Timestamp} {s : String} (h : printRfc3339? t = some s) :
    parseRfc3339 s = some t := by
  unfold printRfc3339? at h
  split at h
  · rename_i hr
    cases h
    obtain ⟨⟨d, time⟩, nanos, offset⟩ := t
    obtain ⟨y1, y2, y3, y4, hy, vy⟩ := fixed_four d.year.toNat
    obtain ⟨m1, m2, hm, vm⟩ := fixed_two d.month
    obtain ⟨e1, e2, he, ve⟩ := fixed_two d.day
    obtain ⟨h1, h2, n1, n2, s1, s2, hc, vc⟩ := clock_spec time
    have hyear : ((d.year.toNat % 10000 : Nat) : Int) = d.year := by
      simp only [InRange] at hr; omega
    have hmonth : d.month % 100 = d.month := Nat.mod_eq_of_lt (by have := d.valid; simp [Valid] at this; omega)
    have hday : d.day % 100 = d.day := Nat.mod_eq_of_lt (by
      have := d.valid; simp only [Valid, daysInMonth] at this; split at this <;> try split at this
      all_goals omega)
    obtain ⟨hdig, hdot⟩ := head_offsetChars offset.val
    simp only [rfc3339Chars, hy, hm, he, hc, String.toList_ofList, List.cons_append, List.nil_append,
      parseRfc3339]
    simp only [ne_eq, not_true_eq_false, false_and, ite_false, vy, vm, ve, hmonth, hday, hyear,
      date_mk?, vc, Option.bind_eq_bind, Option.bind_some, fraction?_chars nanos.isLt hdig hdot,
      offset?_chars]
    rw [dite_eq_left nanos.isLt]
  · cases h

theorem dayName_spec {i : Nat} (h : i < 7) :
    ∃ a b c, (dayNames.getD i "").toList = [a, b, c] ∧ nameOf? dayNames [a, b, c] = some i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by decide⟩

theorem monthName_spec {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    ∃ a b c, (monthNames.getD (m - 1) "").toList = [a, b, c] ∧
      nameOf? monthNames [a, b, c] = some (m - 1) := by
  rcases cases12 (show m - 1 ≤ 11 by omega) with h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] <;> exact ⟨_, _, _, rfl, by decide⟩

theorem weekday_lt (d : Date) : d.weekday < 7 := by
  simp only [Date.weekday]; omega

theorem parseHttpDate_print (nowYear : Int) {t : DateTime} {s : String}
    (h : printHttpDate? t = some s) : parseHttpDate nowYear s = some t := by
  unfold printHttpDate? at h
  split at h
  · rename_i hr
    cases h
    obtain ⟨d, time⟩ := t
    have hv := d.valid
    simp only [Valid] at hv
    obtain ⟨w1, w2, w3, hw, vw⟩ := dayName_spec (weekday_lt d)
    obtain ⟨m1, m2, m3, hm, vm⟩ := monthName_spec hv.1 hv.2.1
    obtain ⟨y1, y2, y3, y4, hy, vy⟩ := fixed_four d.year.toNat
    obtain ⟨e1, e2, he, ve⟩ := fixed_two d.day
    obtain ⟨h1, h2, n1, n2, s1, s2, hc, vc⟩ := clock_spec time
    have hyear : ((d.year.toNat % 10000 : Nat) : Int) = d.year := by
      simp only [InRange] at hr; omega
    have hday : d.day % 100 = d.day := Nat.mod_eq_of_lt (by
      have := hv.2.2.2; simp only [daysInMonth] at this; split at this <;> try split at this
      all_goals omega)
    have hmonth : d.month - 1 + 1 = d.month := by omega
    have himf : imf? (imfChars ⟨d, time⟩) = some ⟨d, time⟩ := by
      simp only [imfChars, hw, hm, hy, he, hc, List.cons_append, List.nil_append, imf?]
      simp only [vw, vm, vy, ve, vc, hyear, hday, hmonth, Option.bind_eq_bind, Option.bind_some,
        checked, date_mk?, ite_true]
    simp [parseHttpDate, himf]
  · cases h

end Lanes.TimeFormat
