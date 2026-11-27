/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Civil dates and times in the proleptic Gregorian calendar, and their day numbers (days since
1970-01-01): `Date.ofDays` and `Date.toDays` are inverse (`ofDays_toDays`, `toDays_ofDays`), and
so are `DateTime.ofUnix` and `DateTime.toUnix` on seconds. The conversions are Howard Hinnant's
`days_from_civil` and `civil_from_days`, with the year of a 400-year era found century by
century, then by four-year cycle, then by year, so that each step divides once.
-/

@[expose] public section

namespace Lanes.Civil

def isLeap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

theorem isLeap_iff (y : Int) : isLeap y = true ↔ y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) := by
  simp [isLeap]

def daysInMonth (y : Int) (m : Nat) : Nat :=
  if m = 2 then (if isLeap y then 29 else 28)
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30
  else 31

def Valid (y : Int) (m d : Nat) : Prop := 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m

instance (y : Int) (m d : Nat) : Decidable (Valid y m d) := by unfold Valid; infer_instance

@[ext] structure Date where
  year : Int
  month : Nat
  day : Nat
  valid : Valid year month day
  deriving DecidableEq

def Date.mk? (y : Int) (m d : Nat) : Option Date := if h : Valid y m d then some ⟨y, m, d, h⟩ else none

/-- Months counted from March, so that February, whose length varies, comes last. -/
def marchMonth (m : Nat) : Nat := (m + 9) % 12

def ofMarchMonth (mp : Nat) : Nat := if mp < 10 then mp + 3 else mp - 9

def daysBefore (mp : Nat) : Nat := (153 * mp + 2) / 5

def marchLength (mp : Nat) : Nat :=
  if mp = 11 then 29 else if mp = 1 ∨ mp = 3 ∨ mp = 6 ∨ mp = 8 then 30 else 31

/-- The day of a 400-year era that starts on 1 March of a year divisible by 400. -/
def dayOfEra (yoe doy : Nat) : Nat := 365 * yoe + yoe / 4 - yoe / 100 + doy

def daysFrom (year : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then year - 1 else year
  y / 400 * 146097 + dayOfEra (y % 400).toNat (daysBefore (marchMonth m) + d - 1) - 719468

def Date.toDays (d : Date) : Int := daysFrom d.year d.month d.day

/-- The year of the era and the day of that year (from 1 March). -/
def yearOfEra (doe : Nat) : Nat × Nat :=
  let c := min (doe / 36524) 3
  let doc := doe - 36524 * c
  let q := doc / 1461
  let doq := doc - 1461 * q
  let r := min (doq / 365) 3
  (100 * c + 4 * q + r, doq - 365 * r)

def civilOf (era : Int) (yd : Nat × Nat) : Int × Nat × Nat :=
  let mp := (5 * yd.2 + 2) / 153
  let m := ofMarchMonth mp
  (era * 400 + yd.1 + (if m ≤ 2 then 1 else 0), m, yd.2 - daysBefore mp + 1)

def civil (z : Int) : Int × Nat × Nat :=
  civilOf ((z + 719468) / 146097) (yearOfEra ((z + 719468) % 146097).toNat)

/-! ### The arithmetic -/

theorem cases12 {mp : Nat} (h : mp ≤ 11) : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨
    mp = 6 ∨ mp = 7 ∨ mp = 8 ∨ mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega

theorem month_of_day (doy : Nat) (h : doy ≤ 365) :
    (5 * doy + 2) / 153 ≤ 11 ∧ daysBefore ((5 * doy + 2) / 153) ≤ doy ∧
    doy - daysBefore ((5 * doy + 2) / 153) + 1 ≤ marchLength ((5 * doy + 2) / 153) := by
  have hm : (5 * doy + 2) / 153 ≤ 11 := by omega
  refine ⟨hm, ?_⟩
  generalize hmp : (5 * doy + 2) / 153 = mp at *
  rcases cases12 hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [marchLength, daysBefore] <;> omega

theorem day_of_month (mp d : Nat) (hm : mp ≤ 11) (hd : 1 ≤ d) (hl : d ≤ marchLength mp) :
    (5 * (daysBefore mp + d - 1) + 2) / 153 = mp ∧ daysBefore mp + d - 1 ≤ 365 := by
  rcases cases12 hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [marchLength, daysBefore] at hl ⊢ <;> omega

theorem marchMonth_ofMarchMonth {mp : Nat} (h : mp ≤ 11) : marchMonth (ofMarchMonth mp) = mp := by
  simp only [marchMonth, ofMarchMonth]; split <;> omega

theorem ofMarchMonth_marchMonth {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    ofMarchMonth (marchMonth m) = m := by
  simp only [marchMonth, ofMarchMonth]
  by_cases h : (m + 9) % 12 < 10 <;> simp [h] <;> omega

theorem daysInMonth_ofMarchMonth (y : Int) {mp : Nat} (h : mp ≤ 10) :
    daysInMonth y (ofMarchMonth mp) = marchLength mp := by
  rcases cases12 (show mp ≤ 11 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> first | omega | rfl

theorem quarters {c q r : Nat} (hq : q ≤ 24) (hr : r ≤ 3) :
    (100 * c + 4 * q + r) / 4 = 25 * c + q ∧ (100 * c + 4 * q + r) / 100 = c
      ∧ (100 * c + 4 * q + r) % 4 = r ∧ (100 * c + 4 * q + r) % 100 = 4 * q + r := by
  omega

/-- The last day of a year of the era, the 366th, is there when the February it ends with is
in a leap year. -/
def LongYear (yoe : Nat) : Prop := yoe % 4 = 3 ∧ (yoe % 100 ≠ 99 ∨ yoe = 399)

theorem yearOfEra_spec (doe : Nat) (h : doe ≤ 146096) :
    (yearOfEra doe).1 ≤ 399 ∧ (yearOfEra doe).2 ≤ 365 ∧
      ((yearOfEra doe).2 = 365 → LongYear (yearOfEra doe).1) ∧
      dayOfEra (yearOfEra doe).1 (yearOfEra doe).2 = doe := by
  simp only [yearOfEra, dayOfEra, LongYear]
  generalize hc : min (doe / 36524) 3 = c
  have hc1 : c ≤ 3 ∧ 36524 * c ≤ doe ∧ (c < 3 → doe < 36524 * (c + 1)) := by omega
  generalize hq : (doe - 36524 * c) / 1461 = q
  have hq1 : 1461 * q ≤ doe - 36524 * c ∧ doe - 36524 * c < 1461 * (q + 1) := by omega
  generalize hr : min ((doe - 36524 * c - 1461 * q) / 365) 3 = r
  have hr1 : r ≤ 3 ∧ 365 * r ≤ doe - 36524 * c - 1461 * q
      ∧ (r < 3 → doe - 36524 * c - 1461 * q < 365 * (r + 1)) := by omega
  obtain ⟨h4, h100, m4, m100⟩ := quarters (c := c) (show q ≤ 24 by omega) hr1.1
  rw [h4, h100, m4, m100]
  omega

theorem yearOfEra_dayOfEra {yoe doy : Nat} (hy : yoe ≤ 399) (hd : doy ≤ 365)
    (hl : doy = 365 → LongYear yoe) : yearOfEra (dayOfEra yoe doy) = (yoe, doy) := by
  obtain ⟨c, q, r, rfl, hq, hr, hc⟩ : ∃ c q r, yoe = 100 * c + 4 * q + r ∧ q ≤ 24 ∧ r ≤ 3 ∧ c ≤ 3 :=
    ⟨yoe / 100, yoe % 100 / 4, yoe % 4, by omega, by omega, by omega, by omega⟩
  obtain ⟨h4, h100, m4, m100⟩ := quarters (c := c) hq hr
  simp only [LongYear] at hl
  rw [m4, m100] at hl
  have e : dayOfEra (100 * c + 4 * q + r) doy = 36524 * c + 1461 * q + 365 * r + doy := by
    simp only [dayOfEra]; rw [h4, h100]; omega
  rw [e]
  simp only [yearOfEra, Prod.mk.injEq]
  have hc' : min ((36524 * c + 1461 * q + 365 * r + doy) / 36524) 3 = c := by omega
  rw [hc']
  have hq' : (36524 * c + 1461 * q + 365 * r + doy - 36524 * c) / 1461 = q := by omega
  rw [hq']
  have hr' : min ((36524 * c + 1461 * q + 365 * r + doy - 36524 * c - 1461 * q) / 365) 3 = r := by
    omega
  rw [hr']
  omega

theorem dayOfEra_le {yoe doy : Nat} (hy : yoe ≤ 399) (hd : doy ≤ 365)
    (hl : doy = 365 → LongYear yoe) : dayOfEra yoe doy ≤ 146096 := by
  obtain ⟨c, q, r, rfl, hq, hr, hc⟩ : ∃ c q r, yoe = 100 * c + 4 * q + r ∧ q ≤ 24 ∧ r ≤ 3 ∧ c ≤ 3 :=
    ⟨yoe / 100, yoe % 100 / 4, yoe % 4, by omega, by omega, by omega, by omega⟩
  obtain ⟨h4, h100, m4, m100⟩ := quarters (c := c) hq hr
  simp only [LongYear] at hl
  rw [m4, m100] at hl
  simp only [dayOfEra]; rw [h4, h100]; omega

/-- February has a 29th exactly when the year it is in, the one after the era's year, is leap. -/
theorem longYear_iff (era : Int) {yoe : Nat} (hy : yoe ≤ 399) :
    LongYear yoe ↔ isLeap (era * 400 + yoe + 1) = true := by
  rw [isLeap_iff, LongYear]; omega

/-! ### Day numbers -/

theorem era_parts (z : Int) : ((z + 719468) % 146097).toNat ≤ 146096 ∧
    (z + 719468) / 146097 * 146097 + ((z + 719468) % 146097).toNat - 719468 = z := by
  omega

theorem civilOf_spec (era : Int) {yoe doy : Nat} (hy : yoe ≤ 399) (hd : doy ≤ 365)
    (hl : doy = 365 → LongYear yoe) :
    Valid (civilOf era (yoe, doy)).1 (civilOf era (yoe, doy)).2.1 (civilOf era (yoe, doy)).2.2 ∧
      daysFrom (civilOf era (yoe, doy)).1 (civilOf era (yoe, doy)).2.1 (civilOf era (yoe, doy)).2.2
        = era * 146097 + dayOfEra yoe doy - 719468 := by
  obtain ⟨hm, hb, hlen⟩ := month_of_day doy hd
  obtain ⟨mp, hmp⟩ : ∃ mp, (5 * doy + 2) / 153 = mp := ⟨_, rfl⟩
  simp only [civilOf, daysFrom, hmp] at hm hb hlen ⊢
  have hmm := marchMonth_ofMarchMonth hm
  have hy' : (if ofMarchMonth mp ≤ 2 then era * 400 + yoe + (if ofMarchMonth mp ≤ 2 then (1 : Int) else 0) - 1
      else era * 400 + yoe + (if ofMarchMonth mp ≤ 2 then (1 : Int) else 0)) = era * 400 + yoe := by
    by_cases h : ofMarchMonth mp ≤ 2 <;> simp [h]
  rw [hmm, hy', show (era * 400 + yoe) / 400 = era by omega,
    show ((era * 400 + (yoe : Int)) % 400).toNat = yoe by omega,
    show daysBefore mp + (doy - daysBefore mp + 1) - 1 = doy by omega]
  refine ⟨⟨?_, ?_, by omega, ?_⟩, rfl⟩
  · simp only [ofMarchMonth]; split <;> omega
  · simp only [ofMarchMonth]; split <;> omega
  · by_cases hfeb : mp = 11
    · subst hfeb
      have h2 : ofMarchMonth 11 = 2 := rfl
      have h337 : daysBefore 11 = 337 := rfl
      rw [h2]
      simp [h337, daysInMonth, marchLength] at hlen ⊢
      by_cases hleap : isLeap (era * 400 + ↑yoe + 1) = true
      · simp [hleap]; omega
      · have : doy ≠ 365 := fun h => hleap ((longYear_iff era hy).mp (hl h))
        simp [hleap]; omega
    · rw [daysInMonth_ofMarchMonth _ (by omega)]
      omega

theorem civil_spec (z : Int) : Valid (civil z).1 (civil z).2.1 (civil z).2.2 ∧
    daysFrom (civil z).1 (civil z).2.1 (civil z).2.2 = z := by
  obtain ⟨hle, hz⟩ := era_parts z
  unfold civil
  generalize ((z + 719468) % 146097).toNat = doe at *
  generalize (z + 719468) / 146097 = era at *
  obtain ⟨hy, hd, hl, hdoe⟩ := yearOfEra_spec doe hle
  generalize yearOfEra doe = yd at *
  obtain ⟨yoe, doy⟩ := yd
  obtain ⟨hv, hdays⟩ := civilOf_spec era hy hd hl
  exact ⟨hv, by rw [hdays, hdoe]; exact hz⟩

def Date.ofDays (z : Int) : Date := ⟨(civil z).1, (civil z).2.1, (civil z).2.2, (civil_spec z).1⟩

/-- 1970-01-01 was a Thursday; Sunday is 0. -/
def Date.weekday (d : Date) : Nat := ((d.toDays + 4) % 7).toNat

theorem toDays_ofDays (z : Int) : (Date.ofDays z).toDays = z := (civil_spec z).2

/-- A valid date read as an era, a year of the era and a day of that year. -/
theorem daysFrom_parts {y : Int} {m d : Nat} (h : Valid y m d) :
    ∃ era yoe doy, yoe ≤ 399 ∧ doy ≤ 365 ∧ (doy = 365 → LongYear yoe) ∧
      civilOf era (yoe, doy) = (y, m, d) ∧ daysFrom y m d = era * 146097 + dayOfEra yoe doy - 719468 := by
  obtain ⟨hm1, hm2, hd1, hd2⟩ := h
  have hmp : marchMonth m ≤ 11 := by simp [marchMonth]; omega
  have hlen : d ≤ marchLength (marchMonth m) := by
    by_cases hf : m = 2
    · subst hf; simp [daysInMonth, marchMonth, marchLength] at hd2 ⊢; split at hd2 <;> omega
    · have : marchMonth m ≤ 10 := by simp [marchMonth]; omega
      rw [← daysInMonth_ofMarchMonth y this, ofMarchMonth_marchMonth hm1 hm2]; exact hd2
  obtain ⟨hback, hdoy⟩ := day_of_month (marchMonth m) d hmp hd1 hlen
  generalize hy' : (if m ≤ 2 then y - 1 else y) = y'
  have hyy : y = y' + (if m ≤ 2 then 1 else 0) := by
    by_cases h : m ≤ 2 <;> simp [h] at hy' ⊢ <;> omega
  refine ⟨y' / 400, (y' % 400).toNat, daysBefore (marchMonth m) + d - 1, by omega, hdoy, ?_, ?_, ?_⟩
  · intro h365
    have hf : marchMonth m = 11 := by
      rcases cases12 hmp with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp only [h, daysBefore, marchLength] at h365 hlen ⊢ <;> simp at hlen <;> omega
    have hm : m = 2 := by simp [marchMonth] at hf; omega
    subst hm
    simp only [daysInMonth, ite_true] at hd2
    split at hd2
    · rename_i hleap
      rw [longYear_iff (y' / 400) (by omega)]
      rw [show y' / 400 * 400 + ↑(y' % 400).toNat + 1 = y by simp at hyy; omega]
      exact hleap
    · simp only [hf, daysBefore] at h365; omega
  · simp only [civilOf, hback, ofMarchMonth_marchMonth hm1 hm2, Prod.mk.injEq]
    refine ⟨?_, trivial, by omega⟩
    by_cases h : m ≤ 2 <;> simp [h] at hyy ⊢ <;> omega
  · simp only [daysFrom, hy']

theorem ofDays_toDays (d : Date) : Date.ofDays d.toDays = d := by
  obtain ⟨era, yoe, doy, hy, hd, hl, hciv, hdays⟩ := daysFrom_parts d.valid
  have hdoe := dayOfEra_le hy hd hl
  have hc : civil d.toDays = (d.year, d.month, d.day) := by
    unfold civil
    rw [Date.toDays, hdays, show (era * 146097 + ↑(dayOfEra yoe doy) - 719468 + 719468) / 146097 = era by omega,
      show ((era * 146097 + ↑(dayOfEra yoe doy) - 719468 + 719468) % 146097).toNat = dayOfEra yoe doy by omega,
      yearOfEra_dayOfEra hy hd hl, hciv]
  ext <;> simp [Date.ofDays, hc]

/-! ### Times of day and seconds since the epoch -/

structure TimeOfDay where
  hour : Fin 24
  minute : Fin 60
  second : Fin 60
  deriving DecidableEq

structure DateTime where
  date : Date
  time : TimeOfDay
  deriving DecidableEq

def TimeOfDay.seconds (t : TimeOfDay) : Nat := t.hour.val * 3600 + t.minute.val * 60 + t.second.val

def TimeOfDay.ofSeconds (s : Nat) : TimeOfDay :=
  ⟨⟨s / 3600 % 24, Nat.mod_lt _ (by decide)⟩, ⟨s / 60 % 60, Nat.mod_lt _ (by decide)⟩,
    ⟨s % 60, Nat.mod_lt _ (by decide)⟩⟩

/-- Seconds since 1970-01-01T00:00:00, leap seconds not counted (POSIX time). -/
def DateTime.toUnix (t : DateTime) : Int := t.date.toDays * 86400 + t.time.seconds

def DateTime.ofUnix (s : Int) : DateTime :=
  ⟨Date.ofDays (s / 86400), TimeOfDay.ofSeconds (s % 86400).toNat⟩

theorem toUnix_ofUnix (s : Int) : (DateTime.ofUnix s).toUnix = s := by
  simp only [DateTime.ofUnix, DateTime.toUnix, toDays_ofDays, TimeOfDay.seconds, TimeOfDay.ofSeconds]
  omega

theorem ofUnix_toUnix (t : DateTime) : DateTime.ofUnix t.toUnix = t := by
  obtain ⟨d, h, m, s⟩ := t
  simp only [DateTime.ofUnix, DateTime.toUnix, TimeOfDay.seconds, TimeOfDay.ofSeconds,
    DateTime.mk.injEq, TimeOfDay.mk.injEq]
  have := h.isLt; have := m.isLt; have := s.isLt
  refine ⟨?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · rw [show (d.toDays * 86400 + ↑(↑h * 3600 + ↑m * 60 + ↑s : Nat)) / 86400 = d.toDays by omega,
      ofDays_toDays]
  all_goals simp only; omega

end Lanes.Civil
