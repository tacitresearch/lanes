/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
CSV as RFC 4180 writes it, with the common dialects: another delimiter (`;`, a tab), another
quote, and records ended by CRLF or LF. A field is quoted when it holds the delimiter, the quote,
CR or LF, and a quote inside a quoted field is doubled.

`Reader` is a state machine fed one character at a time, so a file can be read in pieces
(`Reader.feed`) and its records taken as they come (`Reader.drain`); `parse` reads a whole text.
It is strict, as Go's `encoding/csv` is by default: a quote inside an unquoted field, or anything
but a delimiter or the end of the line after a closing quote, is an error. A record ends at LF or
CRLF; a CR followed by anything else is part of the field, and a blank line is skipped. Three
limits bound what a text can cost (rule 2.6): the fields of a record, the characters of a field,
and the records held at once. `write` writes a table that `parse` reads back as it was
(`Csv.parse_write`, in `Lanes/Lib/Encoding/CsvSound.lean`).

Go's reader turns a CRLF inside a quoted field into LF; this one keeps the field as written.
-/

@[expose] public section

namespace Lanes.Csv

/-- The delimiter and the quote differ, and neither ends a line. -/
structure Dialect where
  delimiter : Char := ','
  quote : Char := '"'
  /-- Whether `write` ends a record with CRLF, as RFC 4180 does, or LF; `parse` reads both. -/
  crlf : Bool := true
  valid : delimiter ≠ quote ∧ delimiter ≠ '\r' ∧ delimiter ≠ '\n' ∧ quote ≠ '\r' ∧ quote ≠ '\n' := by
    decide

structure Limits where
  maxFields : Nat := 4096
  maxFieldChars : Nat := 1 <<< 20
  /-- Records read and not yet taken by `Reader.drain`. -/
  maxRecords : Nat := 1 <<< 20

inductive Problem where
  | bareQuote
  | afterQuote
  | unclosedQuote
  | tooManyFields
  | fieldTooLong
  | tooManyRecords
  /-- A record, counted from 1 with the header, whose fields are not as many as the header's. -/
  | ragged (record : Nat)
  deriving DecidableEq, Repr

structure Error where
  /-- From 1: the line the reader was on; 0 for `ragged`, found after reading. -/
  line : Nat
  problem : Problem
  deriving DecidableEq, Repr

instance : ToString Error where
  toString e :=
    let what := match e.problem with
      | .bareQuote => "a quote in an unquoted field"
      | .afterQuote => "a character after a closing quote"
      | .unclosedQuote => "a quoted field not closed"
      | .tooManyFields => "a record of too many fields"
      | .fieldTooLong => "a field too long"
      | .tooManyRecords => "too many records"
      | .ragged n => s!"record {n} not as wide as the header"
    if e.line = 0 then s!"CSV: {what}" else s!"CSV line {e.line}: {what}"

inductive Mode where
  /-- Nothing of a record read. -/
  | recordStart
  /-- After a delimiter. -/
  | fieldStart
  | plain
  | quoted
  /-- A quote in a quoted field: its end, or the first of two. -/
  | quoteSeen
  /-- A CR in an unquoted field, or at the start of a record (`blank`): the end of the line if
  LF follows, else part of the field. -/
  | cr (blank : Bool)
  /-- A CR after a closing quote, which only LF may follow. -/
  | crQuoted
  deriving DecidableEq, Repr

structure State where
  mode : Mode := .recordStart
  field : String := ""
  fieldChars : Nat := 0
  record : Array String := #[]
  records : Array (Array String) := #[]
  line : Nat := 1
  error : Option Problem := none

namespace State

variable (l : Limits)

def fail (s : State) (p : Problem) : State := { s with error := some p }

def addChar (s : State) (c : Char) (m : Mode) : State :=
  if s.fieldChars < l.maxFieldChars then
    { s with field := s.field.push c, fieldChars := s.fieldChars + 1, mode := m }
  else s.fail .fieldTooLong

def endField (s : State) : State :=
  if s.record.size < l.maxFields then
    { s with record := s.record.push s.field, field := "", fieldChars := 0, mode := .fieldStart }
  else s.fail .tooManyFields

def endRecord (s : State) : State :=
  let s := endField l s
  if s.error.isSome then s
  else if s.records.size < l.maxRecords then
    { s with records := s.records.push s.record, record := #[], mode := .recordStart }
  else s.fail .tooManyRecords

/-- What a character does in an unquoted field, or at the start of one. -/
def plainStep (d : Dialect) (s : State) (c : Char) (atStart : Bool) : State :=
  if c = d.quote then
    if atStart then { s with mode := .quoted } else s.fail .bareQuote
  else if c = d.delimiter then endField l s
  else if c = '\n' then endRecord l s
  else if c = '\r' then { s with mode := .cr false }
  else addChar l s c .plain

def afterQuote (d : Dialect) (s : State) (c : Char) : State :=
  if c = d.quote then addChar l s c .quoted
  else if c = d.delimiter then endField l s
  else if c = '\n' then endRecord l s
  else if c = '\r' then { s with mode := .crQuoted }
  else s.fail .afterQuote

def stepMode (d : Dialect) (s : State) (c : Char) : State :=
  match s.mode with
  | .recordStart =>
    if c = '\n' then s
    else if c = '\r' then { s with mode := .cr true }
    else plainStep l d s c true
  | .fieldStart => plainStep l d s c true
  | .plain => plainStep l d s c false
  | .quoted => if c = d.quote then { s with mode := .quoteSeen } else addChar l s c .quoted
  | .quoteSeen => afterQuote l d s c
  | .cr blank =>
    if c = '\n' then (if blank then { s with mode := .recordStart } else endRecord l s)
    else
      let s := addChar l s '\r' .plain
      if s.error.isSome then s else plainStep l d s c false
  | .crQuoted => if c = '\n' then endRecord l s else s.fail .afterQuote

def step (d : Dialect) (s : State) (c : Char) : State :=
  if s.error.isSome then s
  else
    let s := stepMode l d s c
    if c = '\n' then { s with line := s.line + 1 } else s

/-- The end of the text. -/
def finish (s : State) : State :=
  if s.error.isSome then s
  else match s.mode with
    | .recordStart | .cr true => s
    | .quoted => s.fail .unclosedQuote
    | _ => endRecord l s

def result (s : State) : Except Error (Array (Array String)) :=
  match s.error with
  | some p => .error ⟨s.line, p⟩
  | none => .ok s.records

end State

/-- A reader fed text in pieces. -/
structure Reader where
  dialect : Dialect := {}
  limits : Limits := {}
  state : State := {}

namespace Reader

def feed (r : Reader) (text : String) : Reader :=
  { r with state := text.foldl (State.step r.limits r.dialect) r.state }

def error? (r : Reader) : Option Error := r.state.error.map (⟨r.state.line, ·⟩)

/-- The records read so far, which the reader no longer holds. -/
def drain (r : Reader) : Array (Array String) × Reader :=
  (r.state.records, { r with state := { r.state with records := #[] } })

/-- The records not yet drained, with the last one if the text ended without a line end. -/
def finish (r : Reader) : Except Error (Array (Array String)) :=
  (r.state.finish r.limits).result

end Reader

def parse (s : String) (d : Dialect := {}) (l : Limits := {}) : Except Error (Array (Array String)) :=
  ({ dialect := d, limits := l } : Reader).feed s |>.finish

/-- The first record, and the others, each with as many fields as it has. -/
def parseHeader (s : String) (d : Dialect := {}) (l : Limits := {}) :
    Except Error (Array String × Array (Array String)) := do
  let records ← parse s d l
  match records[0]? with
  | none => .ok (#[], #[])
  | some header =>
    let rows := records.extract 1
    match rows.findIdx? (·.size != header.size) with
    | some i => .error ⟨0, .ragged (i + 2)⟩
    | none => .ok (header, rows)

/-! ### Writing -/

def special (d : Dialect) (c : Char) : Bool :=
  c == d.delimiter || c == d.quote || c == '\r' || c == '\n'

def needsQuotes (d : Dialect) (f : String) : Bool :=
  f.foldl (fun b c => b || special d c) false

def writeQuoted (d : Dialect) (out f : String) : String :=
  (f.foldl (fun out c => if c = d.quote then (out.push c).push c else out.push c) (out.push d.quote)).push
    d.quote

/-- A lone empty field is quoted, since a blank line is skipped. -/
def writeField (d : Dialect) (lone : Bool) (out f : String) : String :=
  if needsQuotes d f || (lone && f.isEmpty) then writeQuoted d out f else out ++ f

def writeFields (d : Dialect) (lone : Bool) (out : String) : List String → String
  | [] => out
  | [f] => writeField d lone out f
  | f :: rest => writeFields d false ((writeField d false out f).push d.delimiter) rest

def lineEnd (d : Dialect) : String := if d.crlf then "\r\n" else "\n"

def writeRecord (d : Dialect) (out : String) (r : Array String) : String :=
  writeFields d true out r.toList ++ lineEnd d

/-- Each record ends with a line end. A record of no fields is a blank line, which `parse`
skips. -/
def write (t : Array (Array String)) (d : Dialect := {}) : String :=
  t.foldl (writeRecord d) ""

def writeHeader (header : Array String) (rows : Array (Array String)) (d : Dialect := {}) : String :=
  write (#[header] ++ rows) d

end Lanes.Csv
