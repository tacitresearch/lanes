/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.HashMap
public import Lanes.Web.Html.Entities

/-!
Character references in HTML text decoded as a browser decodes them (the WHATWG standard,
13.2.5.72 to 13.2.5.80): every named reference of the standard's table, the longest that the
text starts with, with or without `;` for the old names that may omit it; and numeric references
in decimal or hexadecimal, where 0, a surrogate and a number past U+10FFFF are U+FFFD and
0x80 to 0x9F are read as Windows-1252, as browsers do. Anything else after `&` is kept as
written.

In an attribute's value (`inAttribute`), a named reference without `;` followed by `=` or a
letter or digit is kept as written, as the standard says, so that `?a=1&copy=2` stays a query.
-/

@[expose] public section

namespace Lanes.Html

def parseHex (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else (c.toLower.toNat - 87))) 0

def entities : Std.HashMap String String :=
  (entityTable.splitOn "\n").foldl (init := {}) fun m line =>
    match line.splitOn " " with
    | [name, points] =>
      m.insert name (String.ofList ((points.splitOn ",").map fun p => Char.ofNat (parseHex p)))
    | _ => m

/-- The longest name in the table, `CounterClockwiseContourIntegral;`. -/
def longestEntity : Nat := 32

/-- What browsers make of 0x80 to 0x9F, Windows-1252's characters there. -/
def windows1252 : List (Nat × Nat) :=
  [(0x80, 0x20AC), (0x82, 0x201A), (0x83, 0x0192), (0x84, 0x201E), (0x85, 0x2026), (0x86, 0x2020),
    (0x87, 0x2021), (0x88, 0x02C6), (0x89, 0x2030), (0x8A, 0x0160), (0x8B, 0x2039), (0x8C, 0x0152),
    (0x8E, 0x017D), (0x91, 0x2018), (0x92, 0x2019), (0x93, 0x201C), (0x94, 0x201D), (0x95, 0x2022),
    (0x96, 0x2013), (0x97, 0x2014), (0x98, 0x02DC), (0x99, 0x2122), (0x9A, 0x0161), (0x9B, 0x203A),
    (0x9C, 0x0153), (0x9E, 0x017E), (0x9F, 0x0178)]

/-- The character a numeric reference names. -/
def numeric (n : Nat) : Char :=
  if n = 0 || n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then '�'
  else match windows1252.lookup n with
    | some m => Char.ofNat m
    | none => Char.ofNat n

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def isAsciiHex (c : Char) : Bool := isAsciiDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def isAsciiAlnum (c : Char) : Bool := isAsciiDigit c || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def digitValue (c : Char) : Nat :=
  if isAsciiDigit c then c.toNat - 48 else if 'a' ≤ c then c.toNat - 87 else c.toNat - 55

/-- The value of digits in a base, stopped past U+10FFFF so that a long run costs nothing. -/
def digitsValue (base : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun n c => if n > 0x10FFFF then n else n * base + digitValue c) 0

/-- After `&#`: the character and what follows the reference, or `none` if no digit follows. -/
def numericRef (cs : List Char) : Option (Char × List Char) :=
  let (base, body) := match cs with
    | 'x' :: rest | 'X' :: rest => (16, rest)
    | rest => (10, rest)
  let ds := body.takeWhile (if base == 16 then isAsciiHex else isAsciiDigit)
  if ds.isEmpty then none
  else
    let rest := body.drop ds.length
    some (numeric (digitsValue base ds), match rest with | ';' :: r => r | r => r)

/-- After `&`: the longest name of the table the text starts with, what it stands for and what
follows it. -/
def namedRef (inAttribute : Bool) (cs : List Char) : Option (String × List Char) :=
  let run := (cs.takeWhile isAsciiAlnum).take longestEntity
  let after := cs.drop run.length
  let withSemi := if after.head? == some ';' then [(run ++ [';'], after.drop 1)] else []
  let candidates := withSemi ++ ((List.range run.length).reverse.map fun k =>
    (run.take (k + 1), cs.drop (k + 1)))
  candidates.findSome? fun (name, rest) =>
    (entities.get? (String.ofList name)).bind fun value =>
      let keep := inAttribute && name.getLast? != some ';'
        && (rest.head?.any fun c => c == '=' || isAsciiAlnum c)
      if keep then none else some (value, rest)

/-- Characters are written onto `out`; each round reads at least one, so the length of the text
is fuel enough. -/
def unescapeChars (inAttribute : Bool) : Nat → List Char → String → String
  | 0, _, out => out
  | _, [], out => out
  | fuel + 1, '&' :: rest, out =>
    match rest with
    | '#' :: body =>
      match numericRef body with
      | some (c, rest') => unescapeChars inAttribute fuel rest' (out.push c)
      | none => unescapeChars inAttribute fuel rest (out.push '&')
    | _ =>
      match namedRef inAttribute rest with
      | some (value, rest') => unescapeChars inAttribute fuel rest' (out ++ value)
      | none => unescapeChars inAttribute fuel rest (out.push '&')
  | fuel + 1, c :: rest, out => unescapeChars inAttribute fuel rest (out.push c)

/-- Text with its character references decoded. -/
def unescape (s : String) (inAttribute : Bool := false) : String :=
  if s.contains '&' then unescapeChars inAttribute (s.length + 1) s.toList "" else s

end Lanes.Html
