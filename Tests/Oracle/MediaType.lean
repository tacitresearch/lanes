/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-! `Lanes.MediaType` against RFC 9110's examples and against Go's `mime.ParseMediaType`. -/

namespace Tests.Oracle.MediaType

open Lanes Lanes.MediaType
open Lanes.Url (cut)

def sorted (m : MediaType) : MediaType :=
  { m with params := m.params.mergeSort fun a b => decide (a.1 ≤ b.1) }

def mediaJson (m : MediaType) : Json :=
  Json.mkObj [("type", .str s!"{m.type}/{m.subtype}"),
    ("params", Json.mkObj (m.params.map fun (n, v) => (n, .str v))),
    ("format", .str (sorted m).format)]

def answer (c : Case) : Answer :=
  match c.op, String.fromUTF8? c.input with
  | "parse", some s => (parse s).map mediaJson
  | _, _ => none

def tests : List (String × Bool) :=
  [ ("media type: RFC 9110 §8.3.1: these are equivalent",
      ["text/html;charset=utf-8", "text/html;charset=UTF-8", "Text/HTML;Charset=\"utf-8\"",
        "text/html; charset=\"utf-8\""].all fun s =>
        ((parse s).map fun m => (m.type, m.subtype, m.params.map fun (n, v) => (n, v.toLower)))
          == some ("text", "html", [("charset", "utf-8")])),
    ("media type: quoted strings and empty parameters",
      (parse "a/b;c=\"x\\\"y\\\\z\";;d=e;").map (·.params) == some [("c", "x\"y\\z"), ("d", "e")]
        && (parse "a/b; c=\"\"").map (·.params) == some [("c", "")]),
    ("media type: refused: no subtype, spaces at the ends or around =, a duplicate, an empty value",
      ["text", "text/", "/html", " text/html", "text/html ", "a/b; c = d", "a/b; c=d; C=e", "a/b; c=",
        "a/b; c", "a/b; c=\"d", "a/b c", "a/b; c=d e"].all fun s => (parse s).isNone),
    ("media type: format quotes what is not a token",
      (MediaType.mk "a" "b" [("c", "d e"), ("f", "g\"h")]).format == "a/b; c=\"d e\"; f=\"g\\\"h\"") ]

def tokenChars : List Char := "abcxyzABCXYZ019!#$%&'*+-.^_`|~".toList

def alphabet : List Char :=
  tokenChars ++ "/;= \t\"\\(),:@[]?{}".toList ++ ['é', '\x00', '\x7f', '\n', '\r', '\x0b']

def tokenGen : Gen String := do
  match ← Gen.below 6 with
  | 0 => Gen.pick ["text", "html", "plain", "charset", "boundary", "application", "json", "UTF-8"]
  | _ => return String.ofList (← Gen.list (1 + (← Gen.below 6)) (Gen.pick tokenChars))

def quotedGen : Gen String := do
  let parts ← Gen.list (← Gen.below 6) do
    match ← Gen.below 8 with
    | 0 => Gen.pick ["\\\"", "\\\\", "\\a", "\\;", "é", "\t"]
    | _ => return String.ofList [← Gen.pick ("abc XYZ019;=/,()<>@:?[]{}".toList)]
  return "\"" ++ String.join parts ++ "\""

def paramGen : Gen String := do
  let ws ← Gen.pick ["", "", " ", "  ", "\t"]
  let value ← if ← Gen.chance 40 then quotedGen else tokenGen
  let name ← tokenGen
  match ← Gen.below 20 with
  | 0 => return ws
  | 1 => return s!"{ws}{name} = {value}"
  | 2 => return s!"{ws}{name}*={value}"
  | _ => return s!"{ws}{name}={value}"

def mediaGen : Gen String := do
  let ps ← Gen.list (← Gen.below 4) paramGen
  let seps ← ps.mapM fun p => do return (← Gen.pick [";", ";", " ;", "; "]) ++ p
  return s!"{← tokenGen}/{← tokenGen}" ++ String.join seps ++ (← Gen.pick ["", "", "", ";", " "])

def case : Gen Case := do
  let s ← mediaGen
  let s ← match ← Gen.below 10 with
    | 0 | 1 | 2 => Gen.mutate alphabet s
    | 3 => Gen.text alphabet 14
    | _ => pure s
  return text s "parse"

/-- Characters outside quoted strings mapped by `f`, those inside kept, with what each is. -/
def outside (f : Char → List Char) : Bool → List Char → List Char
  | false, '"' :: rest => '"' :: outside f true rest
  | true, '\\' :: c :: rest => '\\' :: c :: outside f true rest
  | true, '"' :: rest => '"' :: outside f false rest
  | true, c :: rest => c :: outside f true rest
  | false, c :: rest => f c ++ outside f false rest
  | _, [] => []

def goSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

def trimGo (cs : List Char) : List Char := ((cs.dropWhile goSpace).reverse.dropWhile goSpace).reverse

/-- Go reads `\x` in a quoted string as `\x` when `x` is not one of its "tspecials". -/
def literalBackslash : Bool → List Char → List Char
  | false, '"' :: rest => '"' :: literalBackslash true rest
  | true, '\\' :: c :: rest =>
    if "()<>@,;:\\\"/[]?=".toList.contains c then '\\' :: c :: literalBackslash true rest
    else '\\' :: '\\' :: c :: literalBackslash true rest
  | true, '"' :: rest => '"' :: literalBackslash false rest
  | b, c :: rest => c :: literalBackslash b rest
  | _, [] => []

def afterEquals : Bool → List Char → List Char
  | true, c :: rest => if goSpace c then afterEquals true rest else c :: afterEquals (c == '=') rest
  | false, c :: rest => c :: afterEquals (c == '=') rest
  | _, [] => []

/-- The text up to the end of the quoted string it is in, and the rest. -/
def inQuotes : List Char → List Char × List Char
  | '\\' :: c :: rest => ('\\' :: c :: (inQuotes rest).1, (inQuotes rest).2)
  | '"' :: rest => (['"'], rest)
  | c :: rest => (c :: (inQuotes rest).1, (inQuotes rest).2)
  | [] => ([], [])

/-- `f` applied to each stretch of the text outside quoted strings. -/
def outsideRuns (f : List Char → List Char) : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    match cs.span (· != '"') with
    | (run, '"' :: rest) => f run ++ '"' :: (inQuotes rest).1 ++ outsideRuns f fuel (inQuotes rest).2
    | (run, _) => f run

/-- The input without whitespace on either side of an `=` outside quoted strings. -/
def aroundEquals (cs : List Char) : List Char :=
  outsideRuns (fun run => (afterEquals false (afterEquals false run).reverse).reverse) cs.length cs

def fixes : List (String × (List Char → List Char)) :=
  [ ("Go trims any whitespace at the ends and reads \\n, \\r, \\v and \\f as OWS",
      fun cs => outside (fun c => if goSpace c then [' '] else [c]) false (trimGo cs)),
    ("Go allows whitespace around =", fun cs => outside (fun c => [c]) false (aroundEquals cs)),
    ("Go keeps a backslash before a character that is not a tspecial, as MSIE writes paths",
      literalBackslash false) ]

/-- Whether a `;` follows another with only whitespace between, outside quoted strings. -/
def emptyParam : Bool → Bool → List Char → Bool
  | false, _, '"' :: rest => emptyParam true false rest
  | true, _, '\\' :: _ :: rest => emptyParam true false rest
  | true, _, '"' :: rest => emptyParam false false rest
  | true, _, _ :: rest => emptyParam true false rest
  | false, a, ';' :: rest => a || emptyParam false true rest
  | false, a, c :: rest => if goSpace c then emptyParam false a rest else emptyParam false false rest
  | _, _, [] => false

def fieldText (go : Answer) (key : String) : Option Json :=
  go.map (·.getObjValD key)

def rfc2231Format (go : Answer) : Bool :=
  (fieldText go "format").any fun f => match f with
    | .str f => (f.splitOn "*=utf-8''").length > 1
    | _ => false

/-- The same answer, or one whose only difference is Go's RFC 2231 form for a value. -/
def goFormat (m : MediaType) : String :=
  let goToken (v : String) := !v.isEmpty && v.toList.all fun c => Http.tokenChar c || c == '{' || c == '}'
  String.ofList ((sorted m).type.toList ++ '/' :: (sorted m).subtype.toList
    ++ (sorted m).params.flatMap fun (n, v) =>
      ';' :: ' ' :: n.toList ++ '=' :: if goToken v then v.toList else quote v.toList)

def sameValue (ours go : Answer) (fixed : Option MediaType) : Option (List String) :=
  if ours == go then some []
  else if ours.isSome && go.isSome && ours.map (·.getObjValD "type") == go.map (·.getObjValD "type")
      && ours.map (·.getObjValD "params") == go.map (·.getObjValD "params")
      && fixed.any (fun m => fieldText go "format" == some (.str (goFormat m))) then
    some ["Go's tokens allow { and }, which RFC 9110 §5.6.2 excludes, so it writes them unquoted"]
  else if ours.isSome && go.isSome && ours.map (·.getObjValD "type") == go.map (·.getObjValD "type")
      && ours.map (·.getObjValD "params") == go.map (·.getObjValD "params") && rfc2231Format go then
    some ["Go writes values that are not ASCII in RFC 2231 form; ours as a quoted string (obs-text)"]
  else none

def braces : Bool → List Char → Bool
  | false, '"' :: rest => braces true rest
  | true, '\\' :: _ :: rest => braces true rest
  | true, '"' :: rest => braces false rest
  | false, c :: rest => c == '{' || c == '}' || braces false rest
  | true, _ :: rest => braces true rest
  | _, [] => false

/-- Go accepts a name repeated with the same value. -/
def withoutRepeats (cs : List Char) : Option MediaType := do
  let m ← parseRaw cs
  let m' := { m with params := m.params.foldl (fun ps p => if ps.contains p then ps else ps ++ [p]) [] }
  if m'.params.length < m.params.length && m'.valid then some m' else none

def known (c : Case) (go : Answer) : Option String :=
  let ours := answer c
  match String.fromUTF8? c.input with
  | none => if go.isSome && ours.isNone then some "Go reads bytes that are not UTF-8; ours reads text" else none
  | some s =>
    let cs := s.toList
    if ours.isNone && (fieldText go "type").any (fun t => match t with | .str t => !t.contains '/' | _ => false) then
      some "Go accepts a type without a subtype (a disposition)"
    else if go.isNone && ours.isSome && emptyParam false false cs then
      some "RFC 9110 §5.6.6 allows empty parameters; Go only one trailing ;"
    else if go != ours && ((cs.splitOn ';').drop 1).any (fun p => ((cut '=' p).1).contains '*') then
      some "Go decodes RFC 2231 names (name*, name*0); RFC 9110 media types have none"
    else if ours.isNone && go.isSome && braces false cs then
      some "Go's tokens allow { and }, which RFC 9110 §5.6.2 excludes"
    else
      let (fixed, reasons) := fixes.foldl (init := (cs, [])) fun (cs, reasons) (reason, fix) =>
        let cs' := fix cs
        if cs' == cs then (cs, reasons) else (cs', reasons ++ [reason])
      match sameValue (if reasons.isEmpty then ours else answer (text (String.ofList fixed) "parse")) go
          (parse (String.ofList fixed)) with
      | some more => if (reasons ++ more).isEmpty then none else some ("; ".intercalate (reasons ++ more))
      | none =>
        let repeated := if ours.isNone then (withoutRepeats fixed).bind fun m =>
            (sameValue (some (mediaJson m)) go (some m)).map fun more => "; ".intercalate
              (reasons ++ ["Go accepts a name repeated with the same value; RFC 6838 §4.3 a name once"] ++ more)
          else none
        repeated.or <|
          if ours.isNone && go.isSome && cs.any (fun c => c.toNat < 32 && c != '\t' || c.toNat == 127) then
            some "Go accepts controls in a quoted string; RFC 9110 §5.6.4 does not"
          else none

def package : Package where
  name := "mime"
  edges := ["text/html;charset=utf-8", "Text/HTML;Charset=\"utf-8\"", "text/html; charset=\"utf-8\"",
      "a/b;;c=d", "text", "a/b; c = d", "a/b;c=\"\\a\"", "a/b; c=\"é\"", "a/b; title*=us-ascii'en'x"].map
    (text · "parse")
  case := case
  answer := answer
  known := known

end Tests.Oracle.MediaType
