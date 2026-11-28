/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic
import Lanes.Lib.Encoding.Csv

/-! `Lanes.Csv` against RFC 4180's examples and against Go's `encoding/csv`. -/

namespace Tests.Oracle.Csv

open Lanes Lanes.Csv

def table (rows : List (List String)) : Array (Array String) := (rows.map List.toArray).toArray

def semicolon : Dialect := { delimiter := ';' }
def tab : Dialect := { delimiter := '\t', crlf := false }

def problem (s : String) (d : Dialect := {}) (l : Limits := {}) : Option Problem :=
  match parse s d l with
  | .error e => some e.problem
  | .ok _ => none

instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def pieces (n : Nat) (cs : List Char) : Nat → List String
  | 0 => []
  | fuel + 1 => if cs.isEmpty then [] else String.ofList (cs.take n) :: pieces n (cs.drop n) fuel

/-- The text fed to a reader in pieces of `n` characters, its records drained after each. -/
def inPieces (s : String) (n : Nat) : Except Error (Array (Array String)) :=
  let (r, out) := (pieces n s.toList s.length).foldl (init := (({} : Reader), #[]))
    fun (r, out) piece =>
      let (taken, r) := (r.feed piece).drain
      (r, out ++ taken)
  r.finish.map (out ++ ·)

def tests : List (String × Bool) :=
  [ ("csv: RFC 4180 §2: CRLF, a last record without it, quotes doubled, CRLF in a quoted field",
      parse "aaa,bbb,ccc\r\nzzz,yyy,xxx" == .ok (table [["aaa", "bbb", "ccc"], ["zzz", "yyy", "xxx"]])
        && parse "\"aaa\",\"b\r\nbb\",\"ccc\"\r\n" == .ok (table [["aaa", "b\r\nbb", "ccc"]])
        && parse "\"aaa\",\"b\"\"bb\",\"ccc\"" == .ok (table [["aaa", "b\"bb", "ccc"]])),
    ("csv: LF ends a record too, a lone CR is data, a blank line is skipped, empty fields kept",
      parse "a,b\n\nc,\n,d\r\n\r\n" == .ok (table [["a", "b"], ["c", ""], ["", "d"]])
        && parse "a\rb,c\r" == .ok (table [["a\rb", "c"]])
        && parse "" == .ok #[] && parse "\n\r\n" == .ok #[] && parse "\"\"" == .ok (table [[""]])),
    ("csv: refused: a bare quote, a character after a closing quote, an unclosed quote",
      problem "a\"b" == some .bareQuote && problem "\"a\"b" == some .afterQuote
        && problem "\"a\"\rb" == some .afterQuote && problem "\"a" == some .unclosedQuote
        && problem " \"a\"" == some .bareQuote),
    ("csv: the limits: fields of a record, characters of a field, records held",
      problem "a,b,c" (l := { maxFields := 2 }) == some .tooManyFields
        && problem "abc" (l := { maxFieldChars := 2 }) == some .fieldTooLong
        && problem "\"abc\"" (l := { maxFieldChars := 2 }) == some .fieldTooLong
        && problem "a\nb\nc" (l := { maxRecords := 2 }) == some .tooManyRecords
        && parse "a,b\nc,d" {} { maxFields := 2, maxFieldChars := 1, maxRecords := 2 }
          == .ok (table [["a", "b"], ["c", "d"]])),
    ("csv: an error names its line",
      (match parse "a\n\"b\nc\nd\"e" with | .error e => e.line == 4 | .ok _ => false)),
    ("csv: dialects: a semicolon, a tab, another quote",
      parse "a;\"b;c\"\n" semicolon == .ok (table [["a", "b;c"]])
        && write (table [["a", "b\tc"], ["d"]]) tab == "a\t\"b\tc\"\nd\n"
        && parse "'a''b',c" { quote := '\'' } == .ok (table [["a'b", "c"]])),
    ("csv: write quotes what needs it, and a lone empty field",
      write (table [["a", "b,c", "d\"e", "f\ng", ""], [""], ["", ""]])
        == "a,\"b,c\",\"d\"\"e\",\"f\ng\",\r\n\"\"\r\n,\r\n"),
    ("csv: a text read in pieces, its records drained as they come, reads as a whole",
      let s := "a,\"b\r\nc\",d\r\n\"e\"\"f\"\r\n\ng,h\r"
      [1, 2, 3, 5, 100].all fun n => inPieces s n == parse s),
    ("csv: a header and rows as wide as it",
      parseHeader "x,y\r\n1,2\r\n3,4\r\n" == .ok (#["x", "y"], table [["1", "2"], ["3", "4"]])
        && (match parseHeader "x,y\n1\n" with | .error e => e.problem == .ragged 2 | .ok _ => false)
        && parseHeader (writeHeader #["x"] (table [["1"]])) == .ok (#["x"], table [["1"]])) ]

def recordsJson (t : Array (Array String)) : Json :=
  .arr (t.map fun r => .arr (r.map .str))

def answer (c : Case) : Answer :=
  let read (d : Dialect) : Answer :=
    match String.fromUTF8? c.input with
    | some s => (parse s d).toOption.map recordsJson
    | none => none
  match c.op with
  | "read" => read {}
  | "read-semicolon" => read semicolon
  | "read-tab" => read { delimiter := '\t' }
  | _ => none

def unCrLf : List Char → List Char
  | '\r' :: '\n' :: rest => '\n' :: unCrLf rest
  | c :: rest => c :: unCrLf rest
  | [] => []

/-- Go turns CRLF into LF everywhere, inside quoted fields too, where we keep the field as
written (RFC 4180 §2.6). -/
def known (c : Case) (go : Answer) : Option String :=
  match answer c, go with
  | some ours, some theirs =>
    match ours with
    | .arr rows =>
      let lf := Json.arr (rows.map fun r => match r with
        | .arr fs => .arr (fs.map fun f => match f with
          | .str s => .str (String.ofList (unCrLf s.toList))
          | j => j)
        | j => j)
      if lf == theirs then some "Go reads CRLF in a quoted field as LF" else none
    | _ => none
  | _, _ => none

def alphabet : List Char := "ab ,;\t\"\r\n\r\né".toList

def fieldGen : Gen String := do
  let n ← Gen.below 5
  return String.ofList (← Gen.list n (Gen.pick ("abc,;\t\"\r\n é".toList)))

def tableGen : Gen (Array (Array String)) := do
  let rows ← Gen.list (← Gen.below 5) do
    return (← Gen.list (1 + (← Gen.below 4)) fieldGen).toArray
  return rows.toArray

def case : Gen Case := do
  let op ← Gen.pick ["read", "read", "read", "read-semicolon", "read-tab"]
  let d : Dialect := match op with
    | "read-semicolon" => semicolon
    | "read-tab" => { delimiter := '\t' }
    | _ => {}
  let written := write (← tableGen) { d with crlf := ← Gen.chance 50 }
  let s ← match ← Gen.below 10 with
    | 0 | 1 | 2 => Gen.mutate alphabet written
    | 3 | 4 => Gen.text alphabet 16
    | _ => pure written
  return text s op

def edges : List Case :=
  ["a,b\r\nc,d", "\"a\"\"b\",c\n", "\"a\r\nb\"", "a\"b", "\"a\"b", "\"a", "", "\n", "\r", "a\r",
    "\"a\"\r", "\"\"", ",", "a,\n", "\r\"a\""].map (text · "read")

def package : Package where
  name := "csv"
  edges
  case
  answer
  known

end Tests.Oracle.Csv
