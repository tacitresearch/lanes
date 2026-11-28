/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
`Lanes.Multipart.parse` against Go's `mime/multipart` `Reader`, on bodies `write` writes, as
browsers send them, and edited a byte at a time.
-/

namespace Tests.Oracle.Multipart

open Lanes Lanes.Multipart

/-- Limits that Go does not have, set beyond any case. -/
def limits : Limits := { bytes_max := 1 <<< 30, parts_max := 1 <<< 20, headers_max := 1 <<< 20 }

def sortPairs (l : List (String × String)) : List (String × String) :=
  l.mergeSort fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

def partJson (p : Part) : Json :=
  Json.mkObj [("headers", .arr ((sortPairs p.headers).map fun (n, v) =>
      Json.arr #[.str n, .str v]).toArray),
    ("body", .str (Bytes.hex p.body))]

def answer (c : Case) : Answer :=
  if c.op.startsWith "parse-" then
    match parse limits (c.op.drop 6).toString c.input with
    | .ok parts => some (.arr (parts.map partJson).toArray)
    | .error _ => none
  else none

def boundaryChars : List Char :=
  "abcXYZ0129'()+_,-./:=?".toList

def nameGen : Gen String :=
  Gen.pick ["title", "photo", "a", "my field", "café", "q\"x", "back\\slash", "--"]

def valueGen : Gen ByteArray := do
  match ← Gen.below 4 with
  | 0 => Gen.bytes 20
  | 1 => return (← Gen.text "ab\r\n- B".toList 24).toUTF8
  | _ => return (← Gen.text "abc xyz 019é".toList 12).toUTF8

def partGen : Gen Part := do
  let name ← nameGen
  let body ← valueGen
  match ← Gen.below 4 with
  | 0 =>
    let filename ← Gen.pick ["a.txt", "café.png", "x y\".bin", ""]
    let type ← Gen.pick ["text/plain", "image/png", "application/octet-stream"]
    return Part.file name filename type body
  | 1 =>
    let extra ← Gen.pick ["x-a", "content-type", "content-transfer-encoding"]
    let value ← Gen.pick ["", "b", "binary", "text/plain; charset=utf-8"]
    return { headers := [("content-disposition", "form-data; name=" ++ name), (extra, value)], body }
  | 2 => return { body }
  | _ => return Part.field name (String.fromUTF8? body |>.getD "v")

def byteAlphabet : List Char := "-\r\n \t:aB".toList

def mutate (b : ByteArray) : Gen ByteArray := do
  let at_ ← Gen.below (b.size + 1)
  let c := (← Gen.pick byteAlphabet).toNat.toUInt8
  let l := b.data.toList
  match ← Gen.below 3 with
  | 0 => return ⟨(l.eraseIdx at_).toArray⟩
  | 1 => return ⟨(l.insertIdx at_ c).toArray⟩
  | _ => return ⟨(l.set at_ c).toArray⟩

def boundaryGen : Gen String := do
  if ← Gen.chance 25 then
    Gen.pick ["B", "----WebKitFormBoundaryx7Gq2gNTjDo4Ah0S", "a'b(c)+_,-./:=?"]
  else
    let chars ← Gen.list (1 + (← Gen.below 12)) (Gen.pick boundaryChars)
    return String.ofList chars

def case : Gen Case := do
  let boundary ← boundaryGen
  let parts ← Gen.list (← Gen.below 4) partGen
  let body := write boundary parts
  let body ← if ← Gen.chance 30 then pure ("preamble\r\n".toUTF8 ++ body ++ "epilogue".toUTF8)
    else pure body
  let body ← match ← Gen.below 3 with
    | 0 => pure body
    | 1 => mutate body
    | _ => do mutate (← mutate body)
  return ⟨s!"parse-{boundary}", body⟩

/-- Go reads a delimiter line that ends in a bare line feed as one that ends in CR LF, and a
header line likewise; RFC 2046 has CR LF. -/
def bareLf (c : Case) : Bool :=
  (List.range c.input.size).any fun i => c.input[i]! == 10 && (i == 0 || c.input[i - 1]! != 13)

/-- Whether the delimiter is somewhere not on a line of its own: RFC 2046 forbids it in a part,
so ours refuses the body, and Go reads it as part of the part, or of the preamble. -/
def strayDelimiter (c : Case) : Bool :=
  let data := crlf ++ c.input
  let delim := delimiter (c.op.drop 6).toString
  (List.range data.size).any fun i =>
    let e := i + delim.size
    matchesAt data delim i && !(matchesAt data dashes e && ends data (e + 2)) && !ends data e

/-- The header lines of Go's answer. -/
def goHeaders (go : Answer) : List (String × String) :=
  match go with
  | some (.arr parts) => parts.toList.flatMap fun p =>
    match p.getObjValD "headers" with
    | .arr hs => hs.toList.filterMap fun h =>
      match h with
      | .arr #[.str n, .str v] => some (n, v)
      | _ => none
    | _ => []
  | _ => []

/-- A line break and a blank: a header line folded, as RFC 5322 no longer allows. -/
def folded (c : Case) : Bool :=
  (List.range c.input.size).any fun i =>
    c.input[i]! == 13 && c.input[i + 1]? == some 10
      && (c.input[i + 2]? == some 32 || c.input[i + 2]? == some 9)

/-- The body with its last delimiter made the last one RFC 2046 has, `--` after it: what Go
reads when a body ends after a delimiter, without its parts, with no `--`. -/
def closedAtLast (c : Case) : Option Case :=
  let data := crlf ++ c.input
  let delim := delimiter (c.op.drop 6).toString
  match ((List.range data.size).filter fun i => matchesAt data delim i).getLast? with
  | some i =>
    let closed := data.extract 0 i ++ delim ++ dashes ++ crlf
    some ⟨c.op, closed.extract 2 closed.size⟩
  | none => none

def edges : List Case :=
  [ ⟨"parse-B", "--B--\r\n".toUTF8⟩,
    ⟨"parse-B", "--B\r\n\r\n\r\n--B--".toUTF8⟩,
    ⟨"parse-B", "pre\r\n--B  \r\ncontent-type: a/b\r\n\r\nx\r\n--B--\r\nepi".toUTF8⟩,
    ⟨"parse-B", "--B\r\n\r\nx\r\n".toUTF8⟩,
    ⟨"parse-B", "--B\r\nno colon\r\n\r\nx\r\n--B--".toUTF8⟩,
    ⟨"parse-B", "--B\r\n\r\nx\r\n--B \t\r\nh: v\r\n".toUTF8⟩,
    ⟨"parse-B", "--B\t\r\n\r\n--B--\r\n".toUTF8⟩,
    ⟨"parse-B", "--B\r\n--B--\r\n".toUTF8⟩,
    -- CI's seed 46140667000: the body ends after a delimiter and its blanks.
    ⟨"parse-(aXYZ-ba?", (Bytes.unhex? ("2d2d286158595a2d62613f0d0a636f6e74656e742d646973706f736974696f6e3a20666f726d2d646174613b20"
      ++ "6e616d653d6261636b5c736c6173680d0a636f6e74656e742d7472616e736665722d656e636f64696e673a2062"
      ++ "0d0a0d0aece9f15582866235e21c0286f499c59026999b250d0a2d2d286158595a2d62613f0d0a636f6e74656e"
      ++ "742d646973706f736974696f6e3a20666f726d2d646174613b206e616d653d22636166c3a9223b2066696c656e"
      ++ "616d653d612e7478740d0a636f6e74656e742d747970653a20696d6167652f706e670d0a0d0addf79e72a89b33"
      ++ "4592dc6f381255caffeb0d0a2d2d286158595a2d62613f0d0a636f6e74656e742d646973706f736974696f6e3a"
      ++ "20666f726d2d646174613b206e616d653d2d2d0d0a0d0a3030312039317863c3a90d0a2d2d286158595a2d6261"
      ++ "3f20090d0a")).getD .empty⟩,
    ⟨"parse-B", ("--B\r\n\r\n".toUTF8 ++ ⟨#[0, 255, 13, 10, 45, 45, 66, 66]⟩
      ++ "\r\n--B--\r\n".toUTF8)⟩ ]

def package : Package where
  name := "multipart"
  edges := edges
  case := case
  answer := answer
  shrinks := false
  recorded := 500
  known c go :=
    if bareLf c then some "Go also takes a bare line feed for CR LF"
    else if answer c = none && go = some (.arr #[]) then
      some "Go reads a body with no delimiter as no parts; ours refuses it"
    else if answer c = none && go.isSome then
      if strayDelimiter c then
        some "Go reads a delimiter not on a line of its own as part of a part; RFC 2046 forbids it there"
      else if (goHeaders go).any fun (n, _) => !MediaType.isToken n then
        some "Go takes a header name that is no token; ours refuses it"
      else if (goHeaders go).any fun (_, v) => v.contains '\uFFFD' then
        some "Go takes a header that is not UTF-8; ours refuses it"
      else if folded c then some "Go unfolds a header line folded onto the next; ours refuses it"
      else if (closedAtLast c).any fun d => answer d = go then
        some "Go reads a body that ends after a delimiter, with no last delimiter, as the parts before it; RFC 2046 requires the last delimiter, so ours refuses it"
      else none
    else none

end Tests.Oracle.Multipart
