/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-! `Lanes.Civil` and `Lanes.TimeFormat` against RFC 3339's and RFC 9110's examples and against
Go's `time` and `net/http`. -/

namespace Tests.Oracle.Time

open Lanes Lanes.Civil Lanes.TimeFormat

/-- Go's `http.ParseTime` places two-digit years as if it were 2018 (69 and later are 19xx). -/
def goNowYear : Int := 2018

def fieldsOf (t : DateTime) : List (String × Json) :=
  [("year", (t.date.year : Json)), ("month", (t.date.month : Json)), ("day", (t.date.day : Json)),
    ("hour", (t.time.hour.val : Json)), ("minute", (t.time.minute.val : Json)),
    ("second", (t.time.second.val : Json))]

def stampJson (t : Timestamp) : Json :=
  Json.mkObj (fieldsOf t.dateTime ++ [("nanos", (t.nanos.val : Json)),
    ("offset", ((t.offset.val * 60 : Int) : Json)), ("unix", (t.toUnix : Json))])

def utcJson (t : DateTime) : Json := Json.mkObj (fieldsOf t ++ [("unix", (t.toUnix : Json))])

def ints (s : String) : List Int := (s.splitOn " ").filterMap String.toInt?

def dateTime? (y m d h mi s : Int) : Option DateTime := do
  let date ← Date.mk? y m.toNat d.toNat
  if hb : h.toNat < 24 ∧ mi.toNat < 60 ∧ s.toNat < 60 then
    some ⟨date, ⟨⟨h.toNat, hb.1⟩, ⟨mi.toNat, hb.2.1⟩, ⟨s.toNat, hb.2.2⟩⟩⟩
  else none

def stamp? (fields : List Int) : Option Timestamp :=
  match fields with
  | [y, m, d, h, mi, s, ns, off] => do
    let dt ← dateTime? y m d h mi s
    if hb : ns.toNat < 1000000000 ∧ -1440 < off ∧ off < 1440 then
      some ⟨dt, ⟨ns.toNat, hb.1⟩, ⟨off, hb.2⟩⟩
    else none
  | _ => none

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "rfc3339", some s => (parseRfc3339 s).map stampJson
  | "rfc3339-format", some s => (stamp? (ints s)).bind printRfc3339? |>.map Json.str
  | "unix", some s => s.toInt?.map fun n => utcJson (DateTime.ofUnix n)
  | "days", some s =>
    match ints s with
    | [y, m, d] => (Date.mk? y m.toNat d.toNat).map fun date => (date.toDays : Json)
    | _ => none
  | "http", some s => (parseHttpDate goNowYear s).map utcJson
  | "http-format", some s =>
    match ints s with
    | [y, m, d, h, mi, sec] => (dateTime? y m d h mi sec).bind printHttpDate? |>.map Json.str
    | _ => none
  | _, _ => none

def rfcTests : List (String × Bool) :=
  let read (s : String) := (parseRfc3339 s).map stampJson
  let canonical (s : String) := (parseRfc3339 s).bind printRfc3339?
  [ ("time: RFC 3339 §5.8 examples read, and are written back in canonical form",
      canonical "1985-04-12T23:20:50.52Z" == some "1985-04-12T23:20:50.52Z"
        && canonical "1996-12-19T16:39:57-08:00" == some "1996-12-19T16:39:57-08:00"
        && canonical "1937-01-01T12:00:27.87+00:20" == some "1937-01-01T12:00:27.87+00:20"
        && canonical "1990-12-31T15:59:59-00:00" == some "1990-12-31T15:59:59Z"
        && canonical "2006-01-02t15:04:05.100000000z" == some "2006-01-02T15:04:05.1Z"),
    ("time: RFC 3339 instants",
      ((parseRfc3339 "1996-12-19T16:39:57-08:00").map (·.toUnix)) == some 851042397
        && ((parseRfc3339 "1970-01-01T00:00:00Z").map (·.toUnix)) == some 0),
    ("time: refused: 30 February, 29 February 2100, hour 24, a leap second, a bad offset",
      ["2024-02-30T00:00:00Z", "2100-02-29T00:00:00Z", "2006-01-02T24:00:00Z",
        "1990-12-31T23:59:60Z", "2006-01-02T15:04:05+24:00", "2006-01-02T15:04:05",
        "2006-01-02T15:04:05.Z", "2006-01-02T5:04:05Z", "2006-01-02 15:04:05Z"].all
        fun s => (read s).isNone),
    ("time: 29 February 2000 and 2024 are dates",
      (read "2000-02-29T00:00:00Z").isSome && (read "2024-02-29T00:00:00Z").isSome) ]

def httpTests : List (String × Bool) :=
  let read (s : String) := (parseHttpDate 2026 s).bind printHttpDate?
  [ ("time: RFC 9110 §5.6.7's three forms read as one",
      ["Sun, 06 Nov 1994 08:49:37 GMT", "Sunday, 06-Nov-94 08:49:37 GMT",
        "Sun Nov  6 08:49:37 1994"].all fun s => read s == some "Sun, 06 Nov 1994 08:49:37 GMT"),
    ("time: refused: a wrong day name, lowercase, another zone",
      ["Mon, 06 Nov 1994 08:49:37 GMT", "sun, 06 Nov 1994 08:49:37 GMT",
        "Sun, 06 Nov 1994 08:49:37 UTC", "Sun, 6 Nov 1994 08:49:37 GMT"].all
        fun s => (read s).isNone),
    ("time: a two-digit year is at most 50 years ahead",
      ((parseHttpDate 2026 "Wednesday, 01-Jan-76 00:00:00 GMT").map (·.date.year)) == some 2076
        && ((parseHttpDate 2026 "Saturday, 01-Jan-77 00:00:00 GMT").map (·.date.year)) == some 1977) ]

def tests : List (String × Bool) :=
  rfcTests ++ httpTests ++
  [ ("time: days from 1970-01-01, both ways, over 800 years at both ends",
      ((List.range 146097).all fun k =>
        let z := (k : Int) - 73048
        (Date.ofDays z).toDays == z) &&
      ((List.range 2000).all fun k =>
        let z := (k : Int) * 1000003 - 1000000000
        (Date.ofDays z).toDays == z)) ]

def year : Gen Int := do
  match ← Gen.below 10 with
  | 0 => return ((← Gen.below 10000 : Nat) : Int)
  | 1 => return [0, 1, 99, 100, 400, 1600, 1900, 2000, 2100, 2400, 9999].getD (← Gen.below 11) 0
  | _ => return 1900 + ((← Gen.below 250 : Nat) : Int)

def date : Gen (Int × Nat × Nat) := do
  let y ← year
  let m := 1 + (← Gen.below 12)
  let d := 1 + (← Gen.below (daysInMonth y m))
  return (y, m, d)

def nanos : Gen Nat := do
  match ← Gen.below 4 with
  | 0 => return 0
  | 1 => return (← Gen.below 1000) * 1000000
  | _ => return ← Gen.below 1000000000

def offset : Gen Int := do
  match ← Gen.below 4 with
  | 0 => return 0
  | 1 => return ((← Gen.below 96 : Nat) : Int) * 15 - 720
  | _ => return ((← Gen.below 2879 : Nat) : Int) - 1439

def stampText : Gen (Option Timestamp) := do
  let (y, m, d) ← date
  return stamp? [y, m, d, ← Gen.below 24, ← Gen.below 60, ← Gen.below 60, ← nanos, ← offset]

def rfcAlphabet : List Char := "0123456789-:T.Zz+ ,t".toList

def twoDigits (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

def variant (s : String) : Gen String := do
  match ← Gen.below 14 with
  | 0 => return s.replace "T" "t"
  | 1 => return s.replace "Z" "z"
  | 2 => return s.replace "Z" "+00:00"
  | 3 => return s.replace "Z" "-00:00"
  | 4 => return (s.splitOn "Z").headD s ++ ".1234567891234Z"
  | 5 => return s.replace "." ","
  | 6 => return s.replace "T0" "T"
  | 7 => return s.replace "-02-28" "-02-29"
  | 8 => return s.replace "-30T" "-31T"
  | 9 => Gen.mutate rfcAlphabet s
  | 10 => Gen.mutate rfcAlphabet s
  | 11 => return s.replace ":00Z" ":60Z"
  | 12 => return s.replace "T2" "T24"
  | _ => return s

def rfcCase : Gen Case := do
  let t ← stampText
  let s := (t.bind printRfc3339?).getD ""
  match ← Gen.below 6 with
  | 0 => match t with
    | some t => return text s!"{t.dateTime.date.year} {t.dateTime.date.month} {t.dateTime.date.day} {t.dateTime.time.hour.val} {t.dateTime.time.minute.val} {t.dateTime.time.second.val} {t.nanos.val} {t.offset.val}" "rfc3339-format"
    | none => return text s "rfc3339"
  | 1 => return text s "rfc3339"
  | 2 => do
    let hour := twoDigits (← Gen.below 26)
    let day := twoDigits (← Gen.below 33)
    let oh := twoDigits (← Gen.below 26)
    let om := twoDigits (← Gen.below 62)
    let off := if ← Gen.chance 50 then "Z" else s!"+{oh}:{om}"
    return text s!"{← year}-{twoDigits (← Gen.below 14)}-{day}T{hour}:{twoDigits (← Gen.below 61)}:{twoDigits (← Gen.below 61)}{off}" "rfc3339"
  | _ => return text (← variant s) "rfc3339"

def httpAlphabet : List Char := "0123456789 :,-GMTSunMonNovJaFebDec".toList

def httpCase : Gen Case := do
  let (y, m, d) ← date
  let (h, mi, sec) := (← Gen.below 24, ← Gen.below 60, ← Gen.below 60)
  let dt := dateTime? y m d h mi sec
  let s := (dt.bind printHttpDate?).getD ""
  if ← Gen.chance 15 then return text s!"{y} {m} {d} {h} {mi} {sec}" "http-format"
  let w := match dt with
    | some dt => dt.date.weekday
    | none => 0
  let long := longDayNames.getD w ""
  let short := dayNames.getD w ""
  let mon := monthNames.getD (m - 1) ""
  let clockText := s!"{twoDigits h}:{twoDigits mi}:{twoDigits sec}"
  let yy := twoDigits (y.toNat % 100)
  let day := if d < 10 then s!" {d}" else toString d
  match ← Gen.below 12 with
  | 0 => return text s!"{long}, {twoDigits d}-{mon}-{yy} {clockText} GMT" "http"
  | 1 => return text s!"{short} {mon} {day} {clockText} {y}" "http"
  | 2 => return text (s.replace "GMT" "UTC") "http"
  | 3 => return text (s.toLower) "http"
  | 4 => return text (s.replace (short ++ ",") (dayNames.getD ((w + 1) % 7) "" ++ ",")) "http"
  | 5 => return text (s.replace " 0" " ") "http"
  | 6 | 7 => return text (← Gen.mutate httpAlphabet s) "http"
  | 8 => return text s!"{short} {mon} {twoDigits d} {clockText} {y}" "http"
  | _ => return text s "http"

def case : Gen Case := do
  match ← Gen.below 10 with
  | 0 => return text (toString (((← Gen.below 20000000000000 : Nat) : Int) - 10000000000000)) "unix"
  | 1 => do
    let y : Int := ((← Gen.below 2000000 : Nat) : Int) - 1000000
    let m := 1 + (← Gen.below 12)
    return text s!"{y} {m} {1 + (← Gen.below (daysInMonth y m))}" "days"
  | 2 | 3 | 4 => httpCase
  | _ => rfcCase

/-- Go reads an hour of one digit; we read RFC 3339's and RFC 9110's two. -/
def padHour (s : String) : String :=
  let cs := s.toList
  let fixed := (List.range cs.length).foldr (init := []) fun i acc =>
    let c := cs.getD i ' '
    if isDigit c && cs.getD (i + 1) ' ' == ':' && (i == 0 || !isDigit (cs.getD (i - 1) ' '))
      && cs.getD (i + 4) ' ' == ':' then '0' :: c :: acc else c :: acc
  String.ofList fixed

/-- Go reads day and month names in any case; RFC 9110 names them case-sensitively. -/
def nameCase (s : String) : String :=
  let names := dayNames ++ longDayNames ++ monthNames
  let words := s.splitOn " "
  " ".intercalate (words.map fun w =>
    let (core, tail) := if w.endsWith "," then (w.dropEnd 1 |>.toString, ",") else (w, "")
    let parts := core.splitOn "-"
    "-".intercalate (parts.map fun p => (names.find? (·.toLower == p.toLower)).getD p) ++ tail)

/-- Go does not check that the day name is the date's. -/
def rightWeekday (s : String) (go : Answer) : String :=
  match go with
  | some j =>
    match (j.getObjValD "year").getInt?, (j.getObjValD "month").getNat?, (j.getObjValD "day").getNat? with
    | .ok y, .ok m, .ok d =>
      match Date.mk? y m d with
      | some date =>
        let w := date.weekday
        let words := s.splitOn " "
        match words with
        | first :: rest =>
          let fixed := if first.endsWith "," then
              (if first.length > 4 then longDayNames.getD w "" else dayNames.getD w "") ++ ","
            else dayNames.getD w ""
          " ".intercalate (fixed :: rest)
        | [] => s
      | none => s
    | _, _, _ => s
  | none => s

def collapse : List Char → List Char
  | ' ' :: tl@(' ' :: _) => collapse tl
  | c :: rest => c :: collapse rest
  | [] => []

/-- Go reads a run of spaces where its layout has one, and asctime's day of one digit after a
single space. -/
def oneSpace (s : String) : String :=
  let cs := collapse s.toList
  let asctime := cs.getD 3 'x' == ' ' && cs.getD 7 'x' == ' ' && isDigit (cs.getD 8 'x')
    && cs.getD 9 'x' == ' '
  String.ofList (if asctime then cs.take 8 ++ ' ' :: cs.drop 8 else cs)

def fixes : List (String × (Case → Answer → Case)) :=
  [ ("Go reads an hour of one digit", fun c _ =>
      match String.fromUTF8? c.input with
      | some s => text (padHour s) c.op
      | none => c),
    ("Go reads a comma before the fraction", fun c _ =>
      if c.op == "rfc3339" then ⟨c.op, ⟨c.input.data.map fun b => if b == 44 then 46 else b⟩⟩ else c),
    ("Go reads names in any case", fun c _ =>
      match c.op, String.fromUTF8? c.input with
      | "http", some s => text (nameCase s) c.op
      | _, _ => c),
    ("Go reads a run of spaces as one", fun c _ =>
      match c.op, String.fromUTF8? c.input with
      | "http", some s => text (oneSpace s) c.op
      | _, _ => c),
    ("Go does not check the day name", fun c go =>
      match c.op, String.fromUTF8? c.input with
      | "http", some s => text (rightWeekday s go) c.op
      | _, _ => c) ]

/-- Go's fallback parser, taken when the strict one fails (on a one-digit hour, say), reads an
offset of hour 24 or more and minute 60 or more. -/
def offsetOutOfRange (c : Case) (go : Answer) : Bool :=
  let cs := c.input.data.toList.reverse.map fun b => Char.ofNat b.toNat
  let digit (i : Nat) := (cs.getD i 'x').toNat - 48
  c.op == "rfc3339" && go.isSome && (answer c).isNone && cs.getD 2 'x' == ':'
    && [0, 1, 3, 4].all (isDigit <| cs.getD · 'x')
    && (digit 4 * 10 + digit 3 ≥ 24 || digit 1 * 10 + digit 0 ≥ 60)

def lowercaseTZ (c : Case) (go : Answer) : Bool :=
  c.op == "rfc3339" && go.isNone && (answer c).isSome
    && (c.input.data.contains 't'.toUInt8 || c.input.data.contains 'z'.toUInt8)

def known (c : Case) (go : Answer) : Option String :=
  if lowercaseTZ c go then some "RFC 3339 §5.6 allows a lowercase t and z; Go refuses them"
  else if offsetOutOfRange c go then some "Go's fallback parser reads an offset out of range"
  else
    let (fixed, reasons) := fixes.foldl (init := (c, [])) fun (c, reasons) (reason, fix) =>
      let c' := fix c go
      if c'.input.data == c.input.data then (c, reasons) else (c', reasons ++ [reason])
    if !reasons.isEmpty && answer fixed == go then some ("; ".intercalate reasons) else none

def package : Package where
  name := "time"
  edges := ["1985-04-12T23:20:50.52Z", "1996-12-19T16:39:57-08:00", "1990-12-31T23:59:60Z",
      "2024-02-30T00:00:00Z", "2006-01-02t15:04:05z"].map (text · "rfc3339")
    ++ ["Sun, 06 Nov 1994 08:49:37 GMT", "Sunday, 06-Nov-94 08:49:37 GMT",
      "Sun Nov  6 08:49:37 1994", "Mon, 06 Nov 1994 08:49:37 GMT"].map (text · "http")
  case := case
  answer := answer
  known := known

end Tests.Oracle.Time
