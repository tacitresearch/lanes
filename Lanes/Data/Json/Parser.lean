/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Ported from Lean 4 core (`Lean.Data.Json.Parser`), Copyright (c) 2019 Gabriel Ebner, Microsoft
Corporation and Lean FRO, Apache 2.0.
Authors: Gabriel Ebner, Marc Huisinga
-/
module

public import Lanes.Data.Json.Basic

/-!
# JSON parser

`Json.parse` reads one JSON document (RFC 8259) from a string. It is strict: no trailing commas,
no leading zeros, no raw control characters in strings, no unpaired `\u` surrogates, and nothing
but whitespace after the value. An object is built by `Json.mkObj`, so a key given twice keeps its
last value, as in Go's `encoding/json` and JavaScript's `JSON.parse`: RFC 8259 allows the text,
and the JSON test suite counts it as valid.

Every function here is total. The original is written in `Std.Internal.Parsec`, whose loops are
`partial`: a `Parsec` result does not say that the position moved forward, so nothing shows the
recursion ends. This parser works on the positions of one fixed string (`s.Pos`) instead, and each
function returns, with its value, a proof that it stopped at or after the position it started
from. Recursion is then justified by the number of bytes left to read.

Two limits bound what a document can cost (rule 2.6), and input beyond either is rejected:

- `maxDepth`: the nesting of arrays and objects, which is also the depth of the parser's stack;
- `maxDigits`: the number of digits in a number, and the size of its exponent. Reading a number
  takes time quadratic in its digits, and `1e1000000000` would be stored as an integer of a
  billion digits.

Apart from long numbers, parsing takes time linear in the input, or `n log n` for an object of
`n` fields.
-/

local macro "pos_order" : tactic =>
  `(tactic| ((try simp only [String.Pos.lt_iff_remainingBytes_lt,
      String.Pos.le_iff_remainingBytes_le] at *); omega))

@[expose] public section

namespace Lanes.Json

namespace Parser

variable {s : String}

def fail {α : Type} (p : s.Pos) (message : String) : Except String α :=
  .error s!"offset {p.offset.byteIdx}: {message}"

@[inline] def next? (p : s.Pos) : Option (Char × { q : s.Pos // p < q }) :=
  if h : p = s.endPos then none else some (p.get h, ⟨p.next h, String.Pos.lt_next⟩)

@[inline] def accept (accepted : Char → Bool) (p : s.Pos) : Option { q : s.Pos // p < q } :=
  match next? p with
  | some (c, q) => if accepted c then some q else none
  | none => none

/-- `start` is where the caller began, so that the result is known to be at or after it. -/
def skipWsFrom (start p : s.Pos) (h : start ≤ p) : { q : s.Pos // start ≤ q } :=
  match next? p with
  | some (c, ⟨q, hq⟩) =>
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then skipWsFrom start q (by pos_order)
    else ⟨p, h⟩
  | none => ⟨p, h⟩
termination_by p.remainingBytes
decreasing_by pos_order

@[inline] def skipWs (p : s.Pos) : { q : s.Pos // p ≤ q } :=
  skipWsFrom p p (String.Pos.le_refl p)

def acceptAll : (expected : List Char) → (p : s.Pos) → Option { q : s.Pos // p ≤ q }
  | [], p => some ⟨p, String.Pos.le_refl p⟩
  | c :: rest, p =>
    match accept (· == c) p with
    | some ⟨q, hq⟩ =>
      match acceptAll rest q with
      | some ⟨r, hr⟩ => some ⟨r, by pos_order⟩
      | none => none
    | none => none

/-! ### Strings -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexDigit (p : s.Pos) : Except String (Nat × { q : s.Pos // p < q }) :=
  match next? p with
  | some (c, q) =>
    match hexDigit? c with
    | some digit => .ok (digit, q)
    | none => fail p "hexadecimal digit expected"
  | none => fail p "unexpected end of input"

def hex4 (p : s.Pos) : Except String (Nat × { q : s.Pos // p < q }) := do
  let (a, ⟨p1, h1⟩) ← hexDigit p
  let (b, ⟨p2, h2⟩) ← hexDigit p1
  let (c, ⟨p3, h3⟩) ← hexDigit p2
  let (d, ⟨p4, h4⟩) ← hexDigit p3
  return (4096 * a + 256 * b + 16 * c + d, ⟨p4, by pos_order⟩)

def lowSurrogate (high : Nat) (p : s.Pos) : Except String (Char × { q : s.Pos // p < q }) :=
  match acceptAll ['\\', 'u'] p with
  | some ⟨p1, h1⟩ =>
    match hex4 p1 with
    | .ok (low, ⟨p2, h2⟩) =>
      if 0xDC00 ≤ low ∧ low < 0xE000 then
        .ok (Char.ofNat (0x10000 + (high - 0xD800) * 0x400 + (low - 0xDC00)), ⟨p2, by pos_order⟩)
      else fail p "high surrogate not followed by a low surrogate"
    | .error e => .error e
  | none => fail p "high surrogate not followed by a low surrogate"

def escape (p : s.Pos) : Except String (Char × { q : s.Pos // p < q }) :=
  match next? p with
  | some ('"', q) => .ok ('"', q)
  | some ('\\', q) => .ok ('\\', q)
  | some ('/', q) => .ok ('/', q)
  | some ('b', q) => .ok ('\x08', q)
  | some ('f', q) => .ok ('\x0c', q)
  | some ('n', q) => .ok ('\n', q)
  | some ('r', q) => .ok ('\r', q)
  | some ('t', q) => .ok ('\t', q)
  | some ('u', ⟨p1, h1⟩) =>
    match hex4 p1 with
    | .ok (code, ⟨p2, h2⟩) =>
      if code < 0xD800 ∨ 0xE000 ≤ code then .ok (Char.ofNat code, ⟨p2, by pos_order⟩)
      else if code < 0xDC00 then
        match lowSurrogate code p2 with
        | .ok (c, ⟨p3, h3⟩) => .ok (c, ⟨p3, by pos_order⟩)
        | .error e => .error e
      else fail p "low surrogate without a high surrogate"
    | .error e => .error e
  | some _ => fail p "invalid escape sequence"
  | none => fail p "unexpected end of input"

def strFrom (start p : s.Pos) (h : start ≤ p) (acc : String) :
    Except String (String × { q : s.Pos // start ≤ q }) :=
  match next? p with
  | some (c, ⟨q, hq⟩) =>
    if c == '"' then .ok (acc, ⟨q, by pos_order⟩)
    else if c == '\\' then
      match escape q with
      | .ok (c, ⟨r, hr⟩) => strFrom start r (by pos_order) (acc.push c)
      | .error e => .error e
    else if c.val < 0x20 then fail p "control character in string"
    else strFrom start q (by pos_order) (acc.push c)
  | none => fail p "unterminated string"
termination_by p.remainingBytes
decreasing_by all_goals pos_order

def str (p : s.Pos) : Except String (String × { q : s.Pos // p ≤ q }) :=
  match accept (· == '"') p with
  | some ⟨q, hq⟩ => strFrom p q (by pos_order) ""
  | none => fail p "string expected"

/-! ### Numbers -/

/--
The run of decimal digits at `p`. Returns `acc` extended by those digits, `count` plus how many
there were, and the position after them; fails if that would be more than `maxDigits` digits.
`start` is where the caller began.
-/
def digitsFrom (maxDigits : Nat) (start p : s.Pos) (h : start ≤ p) (acc count : Nat) :
    Except String (Nat × Nat × { q : s.Pos // start ≤ q }) :=
  match next? p with
  | some (c, ⟨q, hq⟩) =>
    if '0' ≤ c ∧ c ≤ '9' then
      if count < maxDigits then
        digitsFrom maxDigits start q (by pos_order) (10 * acc + (c.toNat - '0'.toNat)) (count + 1)
      else fail p s!"number longer than {maxDigits} digits"
    else .ok (acc, count, ⟨p, h⟩)
  | none => .ok (acc, count, ⟨p, h⟩)
termination_by p.remainingBytes
decreasing_by pos_order

def whole (maxDigits : Nat) (p : s.Pos) : Except String (Nat × Nat × { q : s.Pos // p ≤ q }) :=
  match digitsFrom maxDigits p p (String.Pos.le_refl p) 0 0 with
  | .ok (_, 0, _) => fail p "digit expected"
  | .ok (n, count, q) =>
    if count > 1 ∧ (accept (· == '0') p).isSome then fail p "leading zeros are not allowed"
    else .ok (n, count, q)
  | .error e => .error e

/--
An optional fraction at `p`, after an integer part of `count` digits with value `whole`. Returns
the digits of both as one number, the number of fraction digits, and the position after them.
-/
def fraction (maxDigits whole count : Nat) (p : s.Pos) :
    Except String (Nat × Nat × { q : s.Pos // p ≤ q }) :=
  match accept (· == '.') p with
  | some ⟨p1, h1⟩ =>
    match digitsFrom maxDigits p p1 (by pos_order) whole count with
    | .ok (digits, total, q) =>
      if total = count then fail p1 "digit expected after the decimal point"
      else .ok (digits, total - count, q)
    | .error e => .error e
  | none => .ok (whole, 0, ⟨p, String.Pos.le_refl p⟩)

/-- The digits of an exponent at `p2`, after its marker at `p1` and its sign. -/
def exponentDigits (maxDigits : Nat) (negative : Bool) (p p1 p2 : s.Pos) (h : p ≤ p2) :
    Except String (Int × { q : s.Pos // p ≤ q }) :=
  match digitsFrom maxDigits p p2 h 0 0 with
  | .ok (_, 0, _) => fail p2 "digit expected in the exponent"
  | .ok (n, _, q) =>
    if n > maxDigits then fail p1 s!"exponent larger than {maxDigits}"
    else .ok (if negative then -(n : Int) else n, q)
  | .error e => .error e

def exponent (maxDigits : Nat) (p : s.Pos) : Except String (Int × { q : s.Pos // p ≤ q }) :=
  match accept (fun c => c == 'e' || c == 'E') p with
  | some ⟨p1, h1⟩ =>
    match accept (· == '-') p1 with
    | some ⟨p2, h2⟩ => exponentDigits maxDigits true p p1 p2 (by pos_order)
    | none =>
      match accept (· == '+') p1 with
      | some ⟨p2, h2⟩ => exponentDigits maxDigits false p p1 p2 (by pos_order)
      | none => exponentDigits maxDigits false p p1 p1 (by pos_order)
  | none => .ok (0, ⟨p, String.Pos.le_refl p⟩)

/-- The number at `p1`, after its sign: `negative` if there was a minus. -/
def unsigned (maxDigits : Nat) (negative : Bool) (p p1 : s.Pos) (h : p ≤ p1) :
    Except String (JsonNumber × { q : s.Pos // p ≤ q }) :=
  match whole maxDigits p1 with
  | .ok (n, count, ⟨p2, h2⟩) =>
    match fraction maxDigits n count p2 with
    | .ok (digits, decimals, ⟨p3, h3⟩) =>
      match exponent maxDigits p3 with
      | .ok (e, ⟨p4, h4⟩) =>
        let mantissa : Int := if negative then -(digits : Int) else digits
        .ok (.ofScientific mantissa (e - decimals), ⟨p4, by pos_order⟩)
      | .error e => .error e
    | .error e => .error e
  | .error e => .error e

def num (maxDigits : Nat) (p : s.Pos) : Except String (JsonNumber × { q : s.Pos // p ≤ q }) :=
  match accept (· == '-') p with
  | some ⟨p1, h1⟩ => unsigned maxDigits true p p1 (by pos_order)
  | none => unsigned maxDigits false p p (String.Pos.le_refl p)

/-! ### Values -/

def literal (text : String) (value : Json) (p : s.Pos) :
    Except String (Json × { q : s.Pos // p ≤ q }) :=
  match acceptAll text.toList p with
  | some q => .ok (value, q)
  | none => fail p s!"JSON value expected, perhaps {text}"

def key (p : s.Pos) : Except String (String × { q : s.Pos // p < q }) :=
  match str p with
  | .ok (name, ⟨p1, h1⟩) =>
    let ⟨p2, h2⟩ := skipWs p1
    match accept (· == ':') p2 with
    | some ⟨p3, h3⟩ =>
      let ⟨p4, h4⟩ := skipWs p3
      .ok (name, ⟨p4, by pos_order⟩)
    | none => fail p2 "':' expected"
  | .error e => .error e

mutual

/-- The value at `p`, which must not be whitespace. Arrays and objects may nest `depth` levels
deep. -/
def value (depth maxDigits : Nat) (p : s.Pos) : Except String (Json × { q : s.Pos // p ≤ q }) :=
  match next? p with
  | some ('[', ⟨p1, h1⟩) =>
    match depth with
    | 0 => fail p "maximum nesting depth exceeded"
    | depth + 1 =>
      let ⟨p2, h2⟩ := skipWs p1
      match accept (· == ']') p2 with
      | some ⟨q, hq⟩ => .ok (.arr #[], ⟨q, by pos_order⟩)
      | none => elements depth maxDigits p p2 (by pos_order) #[]
  | some ('{', ⟨p1, h1⟩) =>
    match depth with
    | 0 => fail p "maximum nesting depth exceeded"
    | depth + 1 =>
      let ⟨p2, h2⟩ := skipWs p1
      match accept (· == '}') p2 with
      | some ⟨q, hq⟩ => .ok (.obj #[], ⟨q, by pos_order⟩)
      | none => fields depth maxDigits p p2 (by pos_order) #[]
  | some ('"', _) =>
    match str p with
    | .ok (text, q) => .ok (.str text, q)
    | .error e => .error e
  | some ('t', _) => literal "true" (.bool true) p
  | some ('f', _) => literal "false" (.bool false) p
  | some ('n', _) => literal "null" .null p
  | some (c, _) =>
    if c == '-' || ('0' ≤ c ∧ c ≤ '9') then
      match num maxDigits p with
      | .ok (n, q) => .ok (.num n, q)
      | .error e => .error e
    else fail p "JSON value expected"
  | none => fail p "unexpected end of input"
termination_by (p.remainingBytes, 0)
decreasing_by all_goals (apply Prod.Lex.left; pos_order)

def elements (depth maxDigits : Nat) (start p : s.Pos) (h : start < p) (acc : Array Json) :
    Except String (Json × { q : s.Pos // start ≤ q }) :=
  match value depth maxDigits p with
  | .ok (elem, ⟨p1, h1⟩) =>
    let ⟨p2, h2⟩ := skipWs p1
    match accept (· == ',') p2 with
    | some ⟨p3, h3⟩ =>
      let ⟨p4, h4⟩ := skipWs p3
      elements depth maxDigits start p4 (by pos_order) (acc.push elem)
    | none =>
      match accept (· == ']') p2 with
      | some ⟨q, hq⟩ => .ok (.arr (acc.push elem), ⟨q, by pos_order⟩)
      | none => fail p2 "',' or ']' expected"
  | .error e => .error e
termination_by (p.remainingBytes, 1)
decreasing_by
  · apply Prod.Lex.right; decide
  · apply Prod.Lex.left; pos_order

def fields (depth maxDigits : Nat) (start p : s.Pos) (h : start < p)
    (acc : Array (String × Json)) : Except String (Json × { q : s.Pos // start ≤ q }) :=
  match key p with
  | .ok (name, ⟨p1, h1⟩) =>
    match value depth maxDigits p1 with
    | .ok (fieldValue, ⟨p2, h2⟩) =>
      let ⟨p3, h3⟩ := skipWs p2
      match accept (· == ',') p3 with
      | some ⟨p4, h4⟩ =>
        let ⟨p5, h5⟩ := skipWs p4
        fields depth maxDigits start p5 (by pos_order) (acc.push (name, fieldValue))
      | none =>
        match accept (· == '}') p3 with
        | some ⟨q, hq⟩ => .ok (mkObj (acc.push (name, fieldValue)).toList, ⟨q, by pos_order⟩)
        | none => fail p3 "',' or '}' expected"
    | .error e => .error e
  | .error e => .error e
termination_by (p.remainingBytes, 1)
decreasing_by all_goals (apply Prod.Lex.left; pos_order)

end

def document (s : String) (maxDepth maxDigits : Nat) : Except String Json :=
  let ⟨p, _⟩ := skipWs s.startPos
  match value maxDepth maxDigits p with
  | .ok (result, ⟨p1, _⟩) =>
    let ⟨p2, _⟩ := skipWs p1
    if p2 = s.endPos then .ok result else fail p2 "end of input expected"
  | .error e => .error e

end Parser

/--
Parse a JSON document. An error names the byte offset it was found at.

The input is rejected if arrays and objects nest more than `maxDepth` deep, or if a number has
more than `maxDigits` digits or an exponent beyond `±maxDigits`; the module docstring says why
each is bounded. The defaults are generous for data and small enough that every function on the
result, `Json.pretty` included, stays cheap.
-/
def parse (s : String) (maxDepth : Nat := 128) (maxDigits : Nat := 1000) : Except String Json :=
  Parser.document s maxDepth maxDigits

end Lanes.Json
