/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.MediaType

/-!
# Multipart bodies

`multipart/form-data` (RFC 7578) in the syntax of RFC 2046 §5.1: parts between delimiters, each a
line of `--` and the boundary, with a last delimiter followed by `--`. A part is header lines,
an empty line and its bytes. `parse` reads a body within explicit limits (`Limits`): its size,
its number of parts and each part's number of header lines. What comes before the first
delimiter and after the line of the last is ignored, as RFC 2046 says, and so are blanks after a
delimiter.
Header names are kept in lowercase. `write` writes parts.

Proved, in `Lanes/Web/Http/MultipartSound.lean`: `parse` reads back what `write` writes, for
parts whose header names are lowercase tokens, whose values are plain text with no blank at
either end, and whose bytes do not hold the delimiter (`Multipart.parse_write`); and `parse`
refuses what is over its limits: a body over `bytes_max` (`Multipart.parse_tooLarge`), and it
accepts no more than `parts_max` parts (`Multipart.length_le_of_parse`) and no part with more
than `headers_max` header lines (`Multipart.headers_le_of_parse`).

A form's field is a part whose `content-disposition` is `form-data` with a `name` parameter and,
for a file, a `filename`, read as the parameters of a media type are.
-/

@[expose] public section

namespace Lanes.Multipart

open Http (tokenChar plain trimOws)

structure Part where
  /-- Names in lowercase, in order. -/
  headers : List (String × String) := []
  body : ByteArray := .empty
  deriving DecidableEq

/-- Every limit is explicit (rule 2.6). -/
structure Limits where
  /-- A larger body is refused. -/
  bytes_max : Nat := 33554432
  parts_max : Nat := 1000
  /-- Header lines in one part. -/
  headers_max : Nat := 100

inductive Error where
  | tooLarge
  | tooManyParts
  | tooManyHeaders
  | malformed
  deriving DecidableEq, Repr

def crlf : ByteArray := ⟨#[13, 10]⟩

def dashes : ByteArray := ⟨#[45, 45]⟩

/-- What ends a part: a line break, `--` and the boundary. -/
def delimiter (boundary : String) : ByteArray :=
  crlf ++ dashes ++ boundary.toUTF8

/-- Whether `needle` is in `hay` at `i`. Most places differ in the first byte, which is looked
at before any copy is made. -/
def matchesAt (hay needle : ByteArray) (i : Nat) : Bool :=
  hay[i]? == needle[0]? && hay.extract i (i + needle.size) == needle

/-- The first place from `i` where `needle` is in `hay`. -/
def find (hay needle : ByteArray) (i : Nat) : Option Nat :=
  if _h : i < hay.size ∧ i + needle.size ≤ hay.size then
    if matchesAt hay needle i then some i else find hay needle (i + 1)
  else none
termination_by hay.size - i

/-- Past the blanks at `i`: the transport padding RFC 2046 allows after a delimiter. -/
def skipBlanks (data : ByteArray) (i : Nat) : Nat :=
  if h : i < data.size then
    if data[i] == 32 || data[i] == 9 then skipBlanks data (i + 1) else i
  else i
termination_by data.size - i

/-- Whether a line ends at `i`, after blanks: at a line break or at the end of the body. -/
def ends (data : ByteArray) (i : Nat) : Bool :=
  skipBlanks data i == data.size || matchesAt data crlf (skipBlanks data i)

/-- A header line: a name that is a token, `:`, and a value of plain text with the blanks
around it dropped. -/
def field? (line : List Char) : Option (String × String) :=
  match line.dropWhile (· != ':') with
  | ':' :: value =>
    let name := line.takeWhile (· != ':')
    if name ≠ [] ∧ name.all tokenChar ∧ value.all plain then
      some (String.ofList (Url.lower name), String.ofList (trimOws value))
    else none
  | _ => none

/-- The header lines of a part from `pos`, and where its bytes begin, after the empty line. -/
def headers (data : ByteArray) : (fuel : Nat) → (pos : Nat) →
    Except Error (List (String × String) × Nat)
  | fuel, pos =>
    match find data crlf pos with
    | none => .error .malformed
    | some e =>
      if e = pos then .ok ([], pos + 2)
      else
        match fuel with
        | 0 => .error .tooManyHeaders
        | fuel + 1 =>
          match (String.fromUTF8? (data.extract pos e)).bind (field? ·.toList) with
          | none => .error .malformed
          | some h => (headers data fuel (e + 2)).map fun (hs, start) => (h :: hs, start)

/-- A part from its bytes. No bytes at all is a part with no header and no body: RFC 2046's
`body-part` is header lines and, only if there is a body, the empty line and the body. -/
def part (limits : Limits) (bytes : ByteArray) : Except Error Part :=
  if bytes.size = 0 then .ok {}
  else
    (headers bytes limits.headers_max 0).map fun (headers, start) =>
      { headers, body := bytes.extract start bytes.size }

/-- The parts after a delimiter that ends at `pos`, at most `fuel` of them. -/
def parts (limits : Limits) (delim data : ByteArray) : (fuel : Nat) → (pos : Nat) →
    Except Error (List Part)
  | fuel, pos =>
    if matchesAt data dashes pos then
      if ends data (pos + 2) then .ok [] else .error .malformed
    else
      let start := skipBlanks data pos
      if !matchesAt data crlf start then .error .malformed
      else
        match find data delim (start + 2) with
        | none => .error .malformed
        | some e =>
          match fuel with
          | 0 => .error .tooManyParts
          | fuel + 1 =>
            match part limits (data.extract (start + 2) e) with
            | .error err => .error err
            | .ok p => (parts limits delim data fuel (e + delim.size)).map (p :: ·)

/-- The parts of a body whose boundary is `boundary`. -/
def parse (limits : Limits) (boundary : String) (body : ByteArray) : Except Error (List Part) :=
  if limits.bytes_max < body.size then .error .tooLarge
  else
    let data := crlf ++ body
    let delim := delimiter boundary
    match find data delim 0 with
    | none => .error .malformed
    | some p => parts limits delim data limits.parts_max (p + delim.size)

/-! ## Writing -/

def headerText (headers : List (String × String)) : String :=
  String.join (headers.map fun (n, v) => n ++ ": " ++ v ++ "\r\n")

/-- A part as it stands between two delimiters, after the line break that ends the first. -/
def Part.bytes (p : Part) : ByteArray :=
  (headerText p.headers).toUTF8 ++ crlf ++ p.body

def write (boundary : String) (parts : List Part) : ByteArray :=
  let open_ := dashes ++ boundary.toUTF8
  parts.foldl (fun acc p => acc ++ open_ ++ crlf ++ p.bytes ++ crlf) .empty
    ++ open_ ++ dashes ++ crlf

/-- Whether `parse` can read `p` back: its header names are lowercase tokens and its values plain
text with no blank at either end. -/
def Part.valid (p : Part) : Bool :=
  p.headers.all fun (n, v) =>
    MediaType.isToken n && Url.lower n.toList == n.toList && v.toList.all plain
      && trimOws v.toList == v.toList

/-- Whether the delimiter of `boundary` is nowhere in the part, not even as its end and the
start of the delimiter after it: then `parse` finds where the part ends. -/
def clear (boundary : String) (p : Part) : Bool :=
  go (p.bytes ++ delimiter boundary) (delimiter boundary) p.bytes.size
where
  go (hay needle : ByteArray) : Nat → Bool
    | 0 => true
    | k + 1 => !matchesAt hay needle k && go hay needle k

/-! ## Forms -/

/-- The disposition of a part, `form-data` for a form's field, in lowercase, and its parameters,
names in lowercase. -/
def Part.disposition? (p : Part) : Option (String × List (String × String)) := do
  let v ← p.headers.lookup "content-disposition"
  let (kind, rest) := MediaType.token v.toList
  let params ← MediaType.parseParams rest
  return (String.ofList (Url.lower kind),
    params.map fun (n, v) => (String.ofList (Url.lower n), String.ofList v))

def Part.name? (p : Part) : Option String := do
  let (kind, params) ← p.disposition?
  if kind == "form-data" then params.lookup "name" else none

def Part.filename? (p : Part) : Option String := do
  let (kind, params) ← p.disposition?
  if kind == "form-data" then params.lookup "filename" else none

def Part.contentType? (p : Part) : Option String :=
  p.headers.lookup "content-type"

/-- A value as a parameter: a token as it is, anything else quoted. -/
def param (name value : String) : String :=
  "; " ++ name ++ "=" ++ String.ofList (MediaType.valueChars value)

/-- A form's text field. -/
def Part.field (name value : String) : Part where
  headers := [("content-disposition", "form-data" ++ param "name" name)]
  body := value.toUTF8

/-- A form's file. -/
def Part.file (name filename contentType : String) (body : ByteArray) : Part where
  headers := [("content-disposition", "form-data" ++ param "name" name ++ param "filename" filename),
    ("content-type", contentType)]
  body

/-- The text fields of a form, in order: the parts with a name and no file name whose bytes are
UTF-8. -/
def fields (parts : List Part) : List (String × String) :=
  parts.filterMap fun p =>
    if p.filename?.isSome then none
    else do return (← p.name?, ← String.fromUTF8? p.body)

/-- The file of a form under `name`, the first if several. -/
def file? (parts : List Part) (name : String) : Option Part :=
  parts.find? fun p => p.name? == some name && p.filename?.isSome

end Lanes.Multipart
