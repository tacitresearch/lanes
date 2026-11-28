/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Csv

/-!
What `Lanes.Csv` is proved to do: `parse` reads back what `write` writes, for every table whose
records each have a field and which is within the reader's limits, in every dialect
(`Csv.parse_write`).
-/

@[expose] public section

namespace Lanes.Csv

/-! ### What `write` writes, as characters -/

def quotedBody (d : Dialect) (cs : List Char) : List Char :=
  cs.flatMap fun c => if c = d.quote then [c, c] else [c]

def quotedChars (d : Dialect) (cs : List Char) : List Char :=
  d.quote :: quotedBody d cs ++ [d.quote]

def fieldChars (d : Dialect) (lone : Bool) (f : String) : List Char :=
  if needsQuotes d f || (lone && f.isEmpty) then quotedChars d f.toList else f.toList

def fieldsChars (d : Dialect) (lone : Bool) : List String → List Char
  | [] => []
  | [f] => fieldChars d lone f
  | f :: rest => fieldChars d false f ++ d.delimiter :: fieldsChars d false rest

theorem toList_writeQuoted (d : Dialect) (out f : String) :
    (writeQuoted d out f).toList = out.toList ++ quotedChars d f.toList := by
  have : ∀ (cs : List Char) (o : String),
      (cs.foldl (fun out c => if c = d.quote then (out.push c).push c else out.push c) o).toList
        = o.toList ++ quotedBody d cs := by
    intro cs
    induction cs with
    | nil => simp [quotedBody]
    | cons c cs ih =>
      intro o
      simp only [List.foldl_cons, ih, quotedBody, List.flatMap_cons]
      split <;> simp [String.toList_push]
  simp [writeQuoted, String.foldl_eq_foldl_toList, this, quotedChars, String.toList_push]

theorem toList_writeField (d : Dialect) (lone : Bool) (out f : String) :
    (writeField d lone out f).toList = out.toList ++ fieldChars d lone f := by
  unfold writeField fieldChars
  split
  · exact toList_writeQuoted d out f
  · simp

theorem toList_writeFields (d : Dialect) (fs : List String) :
    ∀ (lone : Bool) (out : String),
      (writeFields d lone out fs).toList = out.toList ++ fieldsChars d lone fs := by
  induction fs with
  | nil => intro lone out; simp [writeFields, fieldsChars]
  | cons f rest ih =>
    intro lone out
    cases rest with
    | nil => simp [writeFields, fieldsChars, toList_writeField]
    | cons g rest' =>
      rw [writeFields.eq_3, ih]
      · simp [fieldsChars, toList_writeField, String.toList_push]
      · simp

def recordChars (d : Dialect) (r : Array String) : List Char :=
  fieldsChars d true r.toList ++ (lineEnd d).toList

theorem toList_write (d : Dialect) (t : Array (Array String)) :
    (write t d).toList = t.toList.flatMap (recordChars d) := by
  have : ∀ (rs : List (Array String)) (o : String),
      (rs.foldl (writeRecord d) o).toList = o.toList ++ rs.flatMap (recordChars d) := by
    intro rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
      intro o
      simp [ih, writeRecord, toList_writeFields, recordChars]
  simp [write, ← Array.foldl_toList, this]

/-- A character that a field holds without quotes. -/
def Plain (d : Dialect) (c : Char) : Prop :=
  c ≠ d.delimiter ∧ c ≠ d.quote ∧ c ≠ '\r' ∧ c ≠ '\n'

theorem plain_of_needsQuotes {d : Dialect} {f : String} (h : needsQuotes d f = false) :
    ∀ c ∈ f.toList, Plain d c := by
  have key : ∀ (cs : List Char) (b : Bool),
      cs.foldl (fun b c => b || special d c) b = (b || cs.any (special d)) := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih => intro b; simp [ih, Bool.or_assoc]
  simp only [needsQuotes, String.foldl_eq_foldl_toList, key, Bool.false_or, List.any_eq_false] at h
  intro c hc
  have := h c hc
  simp only [special, Bool.or_eq_true, beq_iff_eq, not_or] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-! ### What the reader does with it -/

variable (l : Limits) (d : Dialect)

/-- A state with no error and the field `f`. -/
def at_ (m : Mode) (f : List Char) (row : Array String) (recs : Array (Array String)) (ln : Nat) :
    State :=
  { mode := m, field := String.ofList f, fieldChars := f.length, record := row, records := recs,
    line := ln, error := none }

section
variable {m : Mode} {f : List Char} {row : Array String} {recs : Array (Array String)} {ln : Nat}
@[simp] theorem mode_at : (at_ m f row recs ln).mode = m := rfl
@[simp] theorem error_at : (at_ m f row recs ln).error = none := rfl
@[simp] theorem field_at : (at_ m f row recs ln).field = String.ofList f := rfl
@[simp] theorem fieldChars_at : (at_ m f row recs ln).fieldChars = f.length := rfl
@[simp] theorem record_at : (at_ m f row recs ln).record = row := rfl
@[simp] theorem records_at : (at_ m f row recs ln).records = recs := rfl
@[simp] theorem line_at : (at_ m f row recs ln).line = ln := rfl
@[simp] theorem mk_at :
    ({ mode := m, field := String.ofList f, fieldChars := f.length, record := row,
       records := recs, line := ln, error := none } : State) = at_ m f row recs ln := rfl
@[simp] theorem with_mode_at {m' : Mode} :
    ({ at_ m f row recs ln with mode := m' } : State) = at_ m' f row recs ln := rfl
end

theorem ofList_push (f : List Char) (c : Char) :
    (String.ofList f).push c = String.ofList (f ++ [c]) := by
  rw [← String.toList_inj]
  simp only [String.toList_push, String.toList_ofList]

variable {l d}

theorem addChar_at {m m' : Mode} {f : List Char} {row recs ln} {c : Char}
    (h : f.length < l.maxFieldChars) :
    State.addChar l (at_ m f row recs ln) c m' = at_ m' (f ++ [c]) row recs ln := by
  simp only [State.addChar, fieldChars_at, h, ite_true, field_at, ofList_push, record_at, records_at,
    line_at, error_at]
  simp [at_, -mk_at]

theorem endField_at {m : Mode} {f : List Char} {row recs ln} (h : row.size < l.maxFields) :
    State.endField l (at_ m f row recs ln) = at_ .fieldStart [] (row.push (String.ofList f)) recs ln := by
  simp [State.endField, at_, h, -mk_at]

theorem endRecord_at {m : Mode} {f : List Char} {row recs ln} (h : row.size < l.maxFields)
    (hr : recs.size < l.maxRecords) :
    State.endRecord l (at_ m f row recs ln)
      = at_ .recordStart [] #[] (recs.push (row.push (String.ofList f))) ln := by
  simp only [State.endRecord, endField_at h]
  simp [at_, hr, -mk_at]

theorem step_at {m : Mode} {f : List Char} {row recs ln} {c : Char} (hc : c ≠ '\n') :
    State.step l d (at_ m f row recs ln) c = State.stepMode l d (at_ m f row recs ln) c := by
  simp [State.step, hc]

theorem step_at_lf {m : Mode} {f : List Char} {row recs ln} :
    State.step l d (at_ m f row recs ln) '\n'
      = let s := State.stepMode l d (at_ m f row recs ln) '\n'; { s with line := s.line + 1 } := by
  simp [State.step]

/-- The characters of a field without quotes, read from inside it. -/
theorem foldl_plain {cs : List Char} (hp : ∀ c ∈ cs, Plain d c) :
    ∀ {f : List Char} {row recs ln}, f.length + cs.length ≤ l.maxFieldChars →
      cs.foldl (State.step l d) (at_ .plain f row recs ln) = at_ .plain (f ++ cs) row recs ln := by
  induction cs with
  | nil => intros; simp
  | cons c cs ih =>
    intro f row recs ln hlen
    have ⟨h1, h2, h3, h4⟩ := hp c (by simp)
    simp only [List.foldl_cons, step_at h4]
    simp [State.stepMode, State.plainStep, h1, h2, h3, h4]
    rw [addChar_at (by simp at hlen; omega), ih (fun c hc => hp c (by simp [hc])) (by simp at hlen ⊢; omega)]
    simp

theorem foldl_quotedBody {cs : List Char} :
    ∀ {f : List Char} {row recs ln}, f.length + cs.length ≤ l.maxFieldChars →
      ∃ ln', (quotedBody d cs).foldl (State.step l d) (at_ .quoted f row recs ln)
        = at_ .quoted (f ++ cs) row recs ln' := by
  induction cs with
  | nil => intro f row recs ln _; exact ⟨ln, by simp [quotedBody]⟩
  | cons c cs ih =>
    intro f row recs ln hlen
    simp only [List.length_cons] at hlen
    have hq := d.valid
    by_cases hc : c = d.quote
    · subst hc
      have hn : d.quote ≠ '\n' := hq.2.2.2.2
      have e : (quotedBody d (d.quote :: cs)) = d.quote :: d.quote :: quotedBody d cs := by
        simp [quotedBody]
      rw [e, List.foldl_cons, List.foldl_cons, step_at hn]
      simp [State.stepMode]
      rw [step_at hn]
      simp [State.stepMode, State.afterQuote]
      rw [addChar_at (by omega)]
      obtain ⟨ln', h⟩ := ih (f := f ++ [d.quote]) (row := row) (recs := recs) (ln := ln) (by simp; omega)
      exact ⟨ln', by rw [h]; simp⟩
    · have e : (quotedBody d (c :: cs)) = c :: quotedBody d cs := by simp [quotedBody, hc]
      rw [e, List.foldl_cons]
      have hstep : State.step l d (at_ .quoted f row recs ln) c
          = at_ .quoted (f ++ [c]) row recs (if c = '\n' then ln + 1 else ln) := by
        have ha := addChar_at (l := l) (m := .quoted) (m' := .quoted) (f := f) (row := row)
          (recs := recs) (ln := ln) (c := c) (by omega)
        by_cases hn : c = '\n'
        · subst hn
          rw [step_at_lf]
          simp only [State.stepMode, mode_at, hc, ite_false, ha]
          simp [at_, -mk_at]
        · rw [step_at hn]
          simp only [State.stepMode, mode_at, hc, ite_false, ha, hn]
      rw [hstep]
      obtain ⟨ln', h⟩ := ih (f := f ++ [c]) (row := row) (recs := recs)
        (ln := if c = '\n' then ln + 1 else ln) (by simp; omega)
      exact ⟨ln', by rw [h]; simp⟩

/-- The start of a field: after a delimiter, or at the start of a record. -/
def Start (m : Mode) : Prop := m = .recordStart ∨ m = .fieldStart

theorem stepMode_start {m : Mode} (hm : Start m) {row recs ln} {c : Char} (hc : c ≠ '\n')
    (hr : c ≠ '\r') :
    State.stepMode l d (at_ m [] row recs ln) c = State.plainStep l d (at_ m [] row recs ln) c true := by
  rcases hm with rfl | rfl <;> simp [State.stepMode, at_, hc, hr]

/-- A field as `write` writes it, read from the start of a field: the field, and the mode it
ends in. -/
theorem foldl_field {m : Mode} (hm : Start m) {lone : Bool}
    {f : String} (hf : f.length ≤ l.maxFieldChars) {row recs ln} :
    ∃ m' ln', (fieldChars d lone f).foldl (State.step l d) (at_ m [] row recs ln)
      = at_ m' f.toList row recs ln'
      ∧ (m' = .plain ∨ m' = .quoteSeen ∨ (m' = m ∧ lone = false)) := by
  have hv := d.valid
  unfold fieldChars
  split
  · rename_i hq
    simp only [quotedChars, List.foldl_cons, List.foldl_append]
    rw [step_at hv.2.2.2.2, stepMode_start hm hv.2.2.2.2 hv.2.2.2.1]
    have e : State.plainStep l d (at_ m [] row recs ln) d.quote true = at_ .quoted [] row recs ln := by
      simp [State.plainStep, at_]
    rw [e]
    obtain ⟨ln', h⟩ := foldl_quotedBody (l := l) (d := d) (cs := f.toList) (f := []) (row := row)
      (recs := recs) (ln := ln) (by simpa [String.length_toList] using hf)
    rw [h]
    refine ⟨.quoteSeen, ln', ?_, .inr (.inl rfl)⟩
    simp only [List.nil_append, List.foldl_nil]
    rw [step_at hv.2.2.2.2]
    simp [State.stepMode, at_]
  · rename_i hq
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hq
    have hp := plain_of_needsQuotes hq.1
    cases e : f.toList with
    | nil =>
      have hl : lone = false := by
        cases lone
        · rfl
        · have : f = "" := by rw [← String.toList_inj, e]; rfl
          simp [this] at hq
      exact ⟨m, ln, by simp, .inr (.inr ⟨rfl, hl⟩)⟩
    | cons c cs =>
      rw [e] at hp
      have ⟨h1, h2, h3, h4⟩ := hp c (by simp)
      rw [List.foldl_cons, step_at h4, stepMode_start hm h4 h3]
      have hlen : (c :: cs).length ≤ l.maxFieldChars := by
        rw [← e, String.length_toList]; exact hf
      have e2 : State.plainStep l d (at_ m [] row recs ln) c true = at_ .plain [c] row recs ln := by
        simp only [State.plainStep, h1, h2, h3, h4, ite_false]
        rw [addChar_at (by simp at hlen ⊢; omega)]
        rfl
      rw [e2, foldl_plain (fun c' hc' => hp c' (by simp [hc'])) (by simp at hlen ⊢; omega)]
      exact ⟨.plain, ln, by simp, .inl rfl⟩

/-- Where a field may end. -/
def Ends (m : Mode) : Prop := m = .plain ∨ m = .quoteSeen ∨ m = .fieldStart

theorem step_delimiter {m : Mode} (hm : Ends m ∨ m = .recordStart) {f : List Char} {row recs ln}
    (h : row.size < l.maxFields) :
    State.step l d (at_ m f row recs ln) d.delimiter
      = at_ .fieldStart [] (row.push (String.ofList f)) recs ln := by
  have hv := d.valid
  rw [step_at hv.2.2.1]
  rcases hm with (rfl | rfl | rfl) | rfl
  all_goals
    simp only [State.stepMode, State.plainStep, State.afterQuote, hv.1, hv.2.1, hv.2.2.1, ite_false,
      ite_true]
  all_goals first
    | exact endField_at h
    | (rw [show ∀ s : State, s = s from fun _ => rfl]; exact endField_at h)

theorem foldl_lineEnd {m : Mode} (hm : Ends m) {f : List Char} {row recs ln}
    (h : row.size < l.maxFields) (hr : recs.size < l.maxRecords) :
    ∃ ln', (lineEnd d).toList.foldl (State.step l d) (at_ m f row recs ln)
      = at_ .recordStart [] #[] (recs.push (row.push (String.ofList f))) ln' := by
  have hv := d.valid
  have hlf : ∀ {m' : Mode}, (m' = .plain ∨ m' = .fieldStart ∨ m' = .quoteSeen ∨ m' = .cr false
      ∨ m' = .crQuoted) → ∀ {ln},
      State.step l d (at_ m' f row recs ln) '\n'
        = at_ .recordStart [] #[] (recs.push (row.push (String.ofList f))) (ln + 1) := by
    intro m' hm' ln
    rw [step_at_lf]
    rcases hm' with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [State.stepMode, State.plainStep, State.afterQuote, hv.2.2.2.2.symm, hv.2.2.1.symm,
        ite_false, ite_true]
    all_goals
      first
      | (rw [endRecord_at h hr]; rfl)
      | (simp only [Ne, show ('\n' : Char) ≠ d.quote from fun e => hv.2.2.2.2 e.symm, ite_false,
          show ('\n' : Char) ≠ d.delimiter from fun e => hv.2.2.1 e.symm]
         rw [endRecord_at h hr]; rfl)
  unfold lineEnd
  split
  · rw [show "\r\n".toList = ['\r', '\n'] by decide]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [step_at (by decide)]
    have hcr : ∃ m', (m' = .cr false ∨ m' = .crQuoted)
        ∧ State.stepMode l d (at_ m f row recs ln) '\r' = at_ m' f row recs ln := by
      rcases hm with rfl | rfl | rfl
      · exact ⟨.cr false, .inl rfl, by
          simp [State.stepMode, State.plainStep, hv.2.2.2.1.symm, hv.2.1.symm]⟩
      · exact ⟨.crQuoted, .inr rfl, by
          simp [State.stepMode, State.afterQuote, hv.2.2.2.1.symm, hv.2.1.symm]⟩
      · exact ⟨.cr false, .inl rfl, by
          simp [State.stepMode, State.plainStep, hv.2.2.2.1.symm, hv.2.1.symm]⟩
    obtain ⟨m', hm', e⟩ := hcr
    rw [e]
    exact ⟨ln + 1, hlf (by rcases hm' with rfl | rfl <;> simp)⟩
  · rw [show "\n".toList = ['\n'] by decide]
    simp only [List.foldl_cons, List.foldl_nil]
    exact ⟨ln + 1, hlf (by rcases hm with rfl | rfl | rfl <;> simp)⟩

/-- A record's fields as `write` writes them, and its line end. -/
theorem foldl_fields {fs : List String} (hne : fs ≠ [])
    (hfs : ∀ f ∈ fs, f.length ≤ l.maxFieldChars) :
    ∀ {m : Mode} {lone : Bool} {row recs ln}, Start m → (m = .recordStart → lone = true) →
      row.size + fs.length ≤ l.maxFields → recs.size < l.maxRecords →
      ∃ ln', (fieldsChars d lone fs ++ (lineEnd d).toList).foldl (State.step l d)
          (at_ m [] row recs ln)
        = at_ .recordStart [] #[] (recs.push (row ++ fs.toArray)) ln' := by
  induction fs with
  | nil => exact absurd rfl hne
  | cons f rest ih =>
    intro m lone row recs ln hm hlone hsize hr
    cases rest with
    | nil =>
      simp only [fieldsChars, List.foldl_append]
      obtain ⟨m', ln', e, hm'⟩ := foldl_field (l := l) (d := d) (lone := lone) hm (hfs f (by simp))
        (row := row) (recs := recs) (ln := ln)
      rw [e]
      have hends : Ends m' := by
        rcases hm' with rfl | rfl | ⟨rfl, hl⟩
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · rcases hm with rfl | rfl
          · exact absurd (hlone rfl) (by simp [hl])
          · exact .inr (.inr rfl)
      obtain ⟨ln'', e2⟩ := foldl_lineEnd (l := l) (d := d) hends (f := f.toList) (row := row)
        (recs := recs) (ln := ln') (by simp at hsize; omega) hr
      exact ⟨ln'', by rw [e2]; simp [String.ofList_toList]⟩
    | cons g rest' =>
      simp only [fieldsChars, List.append_assoc, List.cons_append, List.foldl_append,
        List.foldl_cons]
      obtain ⟨m', ln', e, hm'⟩ := foldl_field (l := l) (d := d) (lone := false) hm
        (hfs f (by simp)) (row := row) (recs := recs) (ln := ln)
      rw [e]
      have hd : Ends m' ∨ m' = .recordStart := by
        rcases hm' with rfl | rfl | ⟨rfl, _⟩
        · exact .inl (.inl rfl)
        · exact .inl (.inr (.inl rfl))
        · rcases hm with rfl | rfl
          · exact .inr rfl
          · exact .inl (.inr (.inr rfl))
      rw [step_delimiter hd (by simp at hsize; omega)]
      obtain ⟨ln'', e2⟩ := ih (by simp) (fun f' hf' => hfs f' (by simp [hf']))
        (m := .fieldStart) (lone := false) (row := row.push (String.ofList f.toList)) (recs := recs)
        (ln := ln') (.inr rfl) (by simp) (by simp at hsize ⊢; omega) hr
      refine ⟨ln'', ?_⟩
      rw [List.foldl_append] at e2
      rw [e2]
      simp [String.ofList_toList]

theorem foldl_records {rs : List (Array String)}
    (h : ∀ r ∈ rs, 0 < r.size ∧ r.size ≤ l.maxFields ∧ ∀ f ∈ r, f.length ≤ l.maxFieldChars) :
    ∀ {recs ln}, recs.size + rs.length ≤ l.maxRecords →
      ∃ ln', (rs.flatMap (recordChars d)).foldl (State.step l d) (at_ .recordStart [] #[] recs ln)
        = at_ .recordStart [] #[] (recs ++ rs.toArray) ln' := by
  induction rs with
  | nil => intro recs ln _; exact ⟨ln, by simp⟩
  | cons r rs ih =>
    intro recs ln hsize
    have ⟨h1, h2, h3⟩ := h r (by simp)
    simp only [List.flatMap_cons, recordChars]
    obtain ⟨ln', e⟩ := foldl_fields (l := l) (d := d) (fs := r.toList)
      (by intro e; have : r.toList.length = 0 := by rw [e]; rfl
          rw [Array.length_toList] at this; omega)
      (fun f hf => h3 f (by simpa using hf)) (m := .recordStart) (lone := true) (row := #[])
      (recs := recs) (ln := ln) (.inl rfl) (fun _ => rfl) (by simpa using h2)
      (by simp at hsize; omega)
    rw [List.foldl_append, e]
    obtain ⟨ln'', e2⟩ := ih (fun r' hr' => h r' (by simp [hr'])) (recs := recs.push r) (ln := ln')
      (by simp at hsize ⊢; omega)
    refine ⟨ln'', ?_⟩
    have er : (#[] : Array String) ++ r.toList.toArray = r := by simp
    rw [er, e2]
    simp

/-- A table `parse` reads back: each record has a field, and it is within the limits. -/
def Fits (l : Limits) (t : Array (Array String)) : Prop :=
  t.size ≤ l.maxRecords
    ∧ ∀ r ∈ t, 0 < r.size ∧ r.size ≤ l.maxFields ∧ ∀ f ∈ r, f.length ≤ l.maxFieldChars

/-- `parse` reads back what `write` writes, in every dialect. -/
theorem parse_write {t : Array (Array String)} (h : Fits l t) : parse (write t d) d l = .ok t := by
  have e0 : ({} : State) = at_ .recordStart [] #[] #[] 1 := by simp [at_, -mk_at]
  obtain ⟨ln, e⟩ := foldl_records (l := l) (d := d) (rs := t.toList) (fun r hr => h.2 r (by simpa using hr))
    (recs := #[]) (ln := 1) (by simpa using h.1)
  simp only [parse, Reader.feed, Reader.finish, String.foldl_eq_foldl_toList, toList_write, e0, e]
  simp [State.finish, State.result]

end Lanes.Csv
