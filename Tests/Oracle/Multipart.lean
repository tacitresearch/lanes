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

def edges : List Case :=
  [ ⟨"parse-B", "--B--\r\n".toUTF8⟩,
    ⟨"parse-B", "--B\r\n\r\n\r\n--B--".toUTF8⟩,
    ⟨"parse-B", "pre\r\n--B  \r\ncontent-type: a/b\r\n\r\nx\r\n--B--\r\nepi".toUTF8⟩,
    ⟨"parse-B", "--B\r\n\r\nx\r\n".toUTF8⟩,
    ⟨"parse-B", "--B\r\nno colon\r\n\r\nx\r\n--B--".toUTF8⟩,
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
      else none
    else none

end Tests.Oracle.Multipart
