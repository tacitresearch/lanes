/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-! `Lanes.Json.parse` against Go's `encoding/json`: what each accepts, and the value. -/

namespace Tests.Oracle.Json

open Lanes

/-- The value as `oracles/go/json` writes it: numbers as `num:<m>e-<e>`, strings after `s:`. -/
def canonical : Json → Json
  | .num n => .str s!"num:{n.mantissa}e-{n.exponent}"
  | .str s => .str ("s:" ++ s)
  | .arr elems => .arr (elems.attach.map fun ⟨e, _⟩ => canonical e)
  | .obj fields => .obj (fields.attach.map fun ⟨f, _⟩ => (f.1, canonical f.2))
  | j => j
termination_by j => j
decreasing_by
  · have := Array.sizeOf_lt_of_mem ‹_›
    simp only [Json.arr.sizeOf_spec]
    omega
  · have := Json.sizeOf_field_lt ‹_›
    simp only [Json.obj.sizeOf_spec]
    omega

def answerWith (maxDepth maxDigits : Nat) (input : ByteArray) : Answer :=
  match String.fromUTF8? input with
  | some s =>
    match Json.parse s maxDepth maxDigits with
    | .ok j => some (canonical j)
    | .error _ => none
  | none => none

def answer (c : Case) : Answer := answerWith 128 1000 c.input

def hexValue? (cs : List Char) : Option Nat :=
  cs.foldlM (fun n c => (Json.Parser.hexDigit? c).map (16 * n + ·)) 0

def replacement : List Char := "\\ufffd".toList

def lowSurrogateAt : List Char → Bool
  | '\\' :: 'u' :: e :: f :: g :: k :: _ =>
    match hexValue? [e, f, g, k] with
    | some l => 0xDC00 ≤ l && l < 0xE000
    | none => false
  | _ => false

/-- The text with each `\u` escape of a surrogate that is not half of a pair written `\ufffd`. -/
def withoutLoneSurrogates : List Char → List Char
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    match hexValue? [a, b, c, d] with
    | some h =>
      if 0xD800 ≤ h ∧ h < 0xDC00 ∧ lowSurrogateAt rest then
        '\\' :: 'u' :: a :: b :: c :: d :: rest.take 6 ++ withoutLoneSurrogates (rest.drop 6)
      else if 0xD800 ≤ h ∧ h < 0xE000 then replacement ++ withoutLoneSurrogates rest
      else '\\' :: 'u' :: a :: b :: c :: d :: withoutLoneSurrogates rest
    | none => '\\' :: 'u' :: withoutLoneSurrogates (a :: b :: c :: d :: rest)
  | '\\' :: c :: rest => '\\' :: c :: withoutLoneSurrogates rest
  | c :: rest => c :: withoutLoneSurrogates rest
  | [] => []
termination_by l => l.length
decreasing_by all_goals (try simp) <;> omega

def textChars : List Char :=
  ['a', 'Z', ' ', '"', '\\', '/', '\n', '\t', '\x00', '\x1f', '\x7f', 'é', '😀', '\u2028']

def genString : Gen String := do
  Gen.text textChars (← Gen.below 6)

def genNumber : Gen JsonNumber := do
  let m : Int := ((← Gen.below 2001 : Nat) : Int) - 1000
  let m := if ← Gen.chance 10 then m * 10 ^ 25 + 7 else m
  let e : Int := ((← Gen.below 41 : Nat) : Int) - 20
  return .ofScientific m e

def genJson : Nat → Gen Json
  | 0 => return .null
  | fuel + 1 => do
    match ← Gen.below 9 with
    | 0 => return .null
    | 1 => return .bool (← Gen.chance 50)
    | 2 | 3 => return .num (← genNumber)
    | 4 => return .str (← genString)
    | 5 | 6 => return .arr (← Gen.list (← Gen.below 4) (genJson fuel)).toArray
    | _ =>
      let keys := ["a", "b", "é", "", "a\"b"]
      return .obj (← Gen.list (← Gen.below 4) (do return (← Gen.pick keys, ← genJson fuel))).toArray

/-- Numbers spelled as the grammar allows and the printer does not write. -/
def numberText : Gen String := do
  let int ← Gen.pick ["0", "-0", "1", "-12", "120", "007", "9007199254740993"]
  let frac ← Gen.pick ["", ".5", ".50", ".0", ".", ".123456789"]
  let exp ← Gen.pick ["", "e5", "E+2", "e-3", "e", "e+", "E0", "e1000", "e-1000", "e1001"]
  return int ++ frac ++ exp

def escapeText : Gen String := do
  Gen.pick ["\\n", "\\/", "\\u00e9", "\\u00E9", "\\ud83d\\ude00", "\\ud800", "\\udc00",
    "\\ud800\\u0041", "\\u12", "\\x", "\\\\u0041", "\\uD834\\uDD1E", "\\u0000", "\\b\\f\\r\\t"]

def alphabet : List Char := "{}[],:0123456789.eE+-\"\\nultrfas \t\n\r".toList ++ ['\x00', 'é']

def case : Gen Case := do
  let s ← match ← Gen.below 10 with
    | 0 => numberText
    | 1 => do pure ("\"" ++ (← escapeText) ++ (← escapeText) ++ "\"")
    | 2 => do pure ("{\"" ++ (← escapeText) ++ "\":" ++ (← numberText) ++ "}")
    | 3 => Gen.text alphabet 12
    | 4 | 5 => do
      let j ← genJson 4
      Gen.mutate alphabet (if ← Gen.chance 50 then j.compress else j.pretty)
    | _ => do
      let j ← genJson 4
      pure (if ← Gen.chance 50 then j.compress else j.pretty)
  if ← Gen.chance 3 then
    return ⟨"parse", ⟨s.toUTF8.data.push ((← Gen.pick [0x80, 0xff, 0xc3]) : Nat).toUInt8⟩⟩
  return text s "parse"

def edges : List Case :=
  (["", " ", "null", "[1,2]", "{\"a\":1,\"a\":2}", "{\"b\":1,\"a\":[]}", "\"\\ud83d\\ude00\"",
    "\"\\ud800\"", "\"\\udc00\\ud800\"", "-0", "0.1e-2", "1E+2", "1.50", "100e-2", "[1,]", "01",
    "\"\\u0000\"", "1e1000", "1e1001", "\uFEFF{}", "\"\x7f\"", "[\"a\"\n,\t1\r]",
    "123456789012345678901234567890"].map (text · "parse"))
    ++ [⟨"parse", ⟨#[0x22, 0xff, 0x22]⟩⟩, ⟨"parse", ⟨#[0x22, 0xc3, 0x28, 0x22]⟩⟩]

/-- Go reads bytes; ours reads text, which is UTF-8 by its type. Where Go accepts a document
that is not UTF-8, ours accepts its lossy decoding. -/
def readsInvalidUtf8 (c : Case) (go : Answer) : Bool :=
  (String.fromUTF8? c.input).isNone && go.isSome
    && (answerWith 128 1000 (String.fromUTF8Lossy c.input).toUTF8).isSome

/-- Go reads `\ud800` alone as U+FFFD. Ours refuses it: it stands for no character. The
limits are lifted here, as `beyondLimits` does, so that both differences in one case are known. -/
def readsLoneSurrogates (c : Case) (go : Answer) : Bool :=
  match String.fromUTF8? c.input with
  | some s =>
    let fixed := String.ofList (withoutLoneSurrogates s.toList)
    fixed != s && answerWith 10000 100000 fixed.toUTF8 == go
  | none => false

/-- Go has no limit on the digits of a number. Ours refuses more than `maxDigits`, 1000 by
default. -/
def beyondLimits (c : Case) (go : Answer) : Bool :=
  (answer c).isNone && answerWith 10000 100000 c.input == go

/-- Go reads any exponent. `oracles/go/json` writes one beyond ±100000 as `num:unbounded`, and ours
refuses an exponent beyond `maxDigits` either way. -/
def unboundedExponent (c : Case) (go : Answer) : Bool :=
  (answer c).isNone && (go.map Json.compress).any (·.contains "num:unbounded")

/-- The text with the digits of each exponent beyond ±100000 written `0`; `fuel` is its length. -/
def capExponents : Nat → List Char → List Char
  | fuel + 1, e :: rest =>
    if e == 'e' || e == 'E' then
      let (sign, afterSign) := match rest with
        | c :: r => if c == '+' || c == '-' then ([c], r) else ([], rest)
        | [] => ([], [])
      let digits := afterSign.takeWhile Char.isDigit
      if digits.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0 > 100000 then
        e :: sign ++ '0' :: capExponents fuel (afterSign.drop digits.length)
      else e :: capExponents fuel rest
    else e :: capExponents fuel rest
  | _, cs => cs

/-- Go's answer, where each `num:unbounded` stands for any number. -/
def sameUpToUnbounded : Nat → Json → Json → Bool
  | _, .str "num:unbounded", .str s => s.startsWith "num:"
  | n + 1, .arr xs, .arr ys =>
    xs.size == ys.size && (xs.toList.zip ys.toList).all fun (x, y) => sameUpToUnbounded n x y
  | n + 1, .obj fs, .obj gs =>
    fs.size == gs.size && (fs.toList.zip gs.toList).all fun ((k, x), (l, y)) =>
      k == l && sameUpToUnbounded n x y
  | _, x, y => x == y

/-- Ours refuses an exponent beyond `maxDigits`. Go reads it, and keeps or discards the value:
a repeated key keeps only its last. With those exponents capped, ours agrees with Go up to the
values Go writes as `num:unbounded`. -/
def cappedExponent (c : Case) (go : Answer) : Bool :=
  (answer c).isNone &&
    match String.fromUTF8? c.input, go with
    | some s, some g =>
      let capped := String.ofList (capExponents s.length s.toList)
      capped != s && match answerWith 10000 100000 capped.toUTF8 with
        | some ours => sameUpToUnbounded c.input.size g ours
        | none => false
    | _, _ => false

def package : Package where
  name := "json"
  edges := edges
  case := case
  answer := answer
  known c go :=
    if readsInvalidUtf8 c go then some "Go reads invalid UTF-8 as U+FFFD; ours reads UTF-8 text"
    else if readsLoneSurrogates c go then
      some "Go reads an unpaired surrogate escape as U+FFFD; ours refuses it"
    else if beyondLimits c go then some "beyond the limits of ours on digits or nesting"
    else if unboundedExponent c go || cappedExponent c go then
      some "an exponent beyond ±100000, which ours refuses"
    else none

end Tests.Oracle.Json
