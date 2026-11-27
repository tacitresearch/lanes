/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Encoding.Json.Parser

/-!
# The grammar of JSON text

RFC 8259's grammar as inductive predicates on lists of characters, each relating a text to what
it means. It is the specification the printers and the parser are proved against
(`PrinterSound`, `ParserSound`).

`Value maxDigits depth cs v` says that `cs` is a JSON value that means `v`, with arrays and
objects nested at most `depth` deep and numbers within `maxDigits` (`Number`); those are the
limits the parser takes. The grammar is the RFC's, with one exception: a `\u` escape of a
surrogate that is not half of a pair matches the RFC's `char` but denotes no character, so it has
no meaning here. The meaning of an object is its fields in the order of the text, keys given
twice included; `Json.normalize` turns it into the value the parser builds.
-/

@[expose] public section

namespace Lanes.Json

namespace Grammar

/-- `ws`: space, horizontal tab, line feed, carriage return. -/
def IsWs (c : Char) : Prop := c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r'

def Ws (w : List Char) : Prop := ∀ c ∈ w, IsWs c

def IsDigit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

instance (c : Char) : Decidable (IsWs c) := inferInstanceAs (Decidable (_ ∨ _))

instance (c : Char) : Decidable (IsDigit c) := inferInstanceAs (Decidable (_ ∧ _))

def Digits (ds : List Char) : Prop := ds ≠ [] ∧ ∀ c ∈ ds, IsDigit c

/-- `int = zero / ( digit1-9 *DIGIT )` -/
def IntPart (ds : List Char) : Prop := Digits ds ∧ (ds.head? = some '0' → ds = ['0'])

/-- `frac = decimal-point 1*DIGIT`, or nothing; the second index is the digits. -/
inductive Frac : List Char → List Char → Prop
  | none : Frac [] []
  | some {ds : List Char} : Digits ds → Frac ('.' :: ds) ds

/-- `exp = e [ minus / plus ] 1*DIGIT`, or nothing; the indices are its value and its digits. -/
inductive Exp : List Char → Int → List Char → Prop
  | none : Exp [] 0 []
  | some {e : Char} {ds : List Char} (sign : List Char) :
      (e = 'e' ∨ e = 'E') → (sign = [] ∨ sign = ['+'] ∨ sign = ['-']) → Digits ds →
      Exp (e :: sign ++ ds)
        (if sign = ['-'] then -(Nat.ofDigitChars 10 ds 0 : Int) else Nat.ofDigitChars 10 ds 0) ds

/--
`number = [ minus ] int [ frac ] [ exp ]`, with at most `maxDigits` digits before the exponent,
at most `maxDigits` digits in it, and an exponent of at most `maxDigits` either way.
-/
inductive Number (maxDigits : Nat) : List Char → JsonNumber → Prop
  | mk {int frac fracDigits exp expDigits : List Char} {e : Int} (negative : Bool) :
      IntPart int → Frac frac fracDigits → Exp exp e expDigits →
      (int ++ fracDigits).length ≤ maxDigits → expDigits.length ≤ maxDigits →
      e.natAbs ≤ maxDigits →
      Number maxDigits ((if negative then ['-'] else []) ++ int ++ frac ++ exp)
        (.ofScientific
          (if negative then -(Nat.ofDigitChars 10 (int ++ fracDigits) 0 : Int)
            else Nat.ofDigitChars 10 (int ++ fracDigits) 0)
          (e - fracDigits.length))

/-- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF` -/
def Unescaped (c : Char) : Prop := 0x20 ≤ c.val ∧ c ≠ '"' ∧ c ≠ '\\'

/-- Four hexadecimal digits and the number they write. -/
inductive Hex4 : List Char → Nat → Prop
  | mk {a b c d : Char} {x y z w : Nat} :
      Parser.hexDigit? a = some x → Parser.hexDigit? b = some y → Parser.hexDigit? c = some z →
      Parser.hexDigit? d = some w → Hex4 [a, b, c, d] (4096 * x + 256 * y + 16 * z + w)

/-- What follows a backslash in a string, and the character it stands for. -/
inductive Escape : List Char → Char → Prop
  | quote : Escape ['"'] '"'
  | backslash : Escape ['\\'] '\\'
  | slash : Escape ['/'] '/'
  | backspace : Escape ['b'] '\x08'
  | formFeed : Escape ['f'] '\x0c'
  | lineFeed : Escape ['n'] '\n'
  | carriageReturn : Escape ['r'] '\r'
  | tab : Escape ['t'] '\t'
  | unicode {hs : List Char} {code : Nat} :
      Hex4 hs code → (code < 0xD800 ∨ 0xE000 ≤ code) → Escape ('u' :: hs) (Char.ofNat code)
  | pair {hs ls : List Char} {high low : Nat} :
      Hex4 hs high → 0xD800 ≤ high → high < 0xDC00 → Hex4 ls low → 0xDC00 ≤ low → low < 0xE000 →
      Escape ('u' :: hs ++ '\\' :: 'u' :: ls)
        (Char.ofNat (0x10000 + (high - 0xD800) * 0x400 + (low - 0xDC00)))

/-- The characters between the quotes of a string, and the characters they stand for. -/
inductive Chars : List Char → List Char → Prop
  | nil : Chars [] []
  | plain {c : Char} {cs ds : List Char} : Unescaped c → Chars cs ds → Chars (c :: cs) (c :: ds)
  | escape {es cs ds : List Char} {c : Char} :
      Escape es c → Chars cs ds → Chars ('\\' :: es ++ cs) (c :: ds)

/-- A text with whitespace on either side. -/
structure Spaced where
  before : List Char
  text : List Char
  after : List Char

def Spaced.Ws (x : Spaced) : Prop := Grammar.Ws x.before ∧ Grammar.Ws x.after

/-- An object member: its key with the whitespace around it, `:`, then its value. -/
structure Member where
  key : Spaced
  name : List Char
  value : Spaced
  json : Json

/--
`value`, nested at most `depth` deep. An array is `[`, its elements with whitespace around each,
separated by commas, whitespace, then `]`; an object likewise, of members.
-/
inductive Value (maxDigits : Nat) : Nat → List Char → Json → Prop
  | null (depth : Nat) : Value maxDigits depth ['n', 'u', 'l', 'l'] .null
  | true (depth : Nat) : Value maxDigits depth ['t', 'r', 'u', 'e'] (.bool .true)
  | false (depth : Nat) : Value maxDigits depth ['f', 'a', 'l', 's', 'e'] (.bool .false)
  | num (depth : Nat) {cs : List Char} {n : JsonNumber} :
      Number maxDigits cs n → Value maxDigits depth cs (.num n)
  | str (depth : Nat) {cs ds : List Char} :
      Chars cs ds → Value maxDigits depth ('"' :: cs ++ ['"']) (.str (String.ofList ds))
  | emptyArr (depth : Nat) {w : List Char} :
      Grammar.Ws w → Value maxDigits (depth + 1) ('[' :: w ++ [']']) (.arr #[])
  | arr (depth : Nat) (elems : List (Spaced × Json)) {close : List Char} :
      elems ≠ [] → (∀ e ∈ elems, e.1.Ws) → (∀ e ∈ elems, Value maxDigits depth e.1.text e.2) →
      Grammar.Ws close →
      Value maxDigits (depth + 1)
        ('[' :: [','].intercalate (elems.map fun e => e.1.before ++ e.1.text ++ e.1.after) ++
          close ++ [']'])
        (.arr (elems.map (·.2)).toArray)
  | emptyObj (depth : Nat) {w : List Char} :
      Grammar.Ws w → Value maxDigits (depth + 1) ('{' :: w ++ ['}']) (.obj #[])
  | obj (depth : Nat) (members : List Member) {close : List Char} :
      members ≠ [] → (∀ m ∈ members, m.key.Ws ∧ m.value.Ws) →
      (∀ m ∈ members, ∃ cs, m.key.text = '"' :: cs ++ ['"'] ∧ Chars cs m.name) →
      (∀ m ∈ members, Value maxDigits depth m.value.text m.json) → Grammar.Ws close →
      Value maxDigits (depth + 1)
        ('{' :: [','].intercalate (members.map fun m => m.key.before ++ m.key.text ++
          m.key.after ++ ':' :: (m.value.before ++ m.value.text ++ m.value.after)) ++
          close ++ ['}'])
        (.obj (members.map fun m => (String.ofList m.name, m.json)).toArray)

/-- `JSON-text = ws value ws` -/
def Text (maxDepth maxDigits : Nat) (cs : List Char) (v : Json) : Prop :=
  ∃ w₁ t w₂, cs = w₁ ++ t ++ w₂ ∧ Ws w₁ ∧ Ws w₂ ∧ Value maxDigits maxDepth t v

end Grammar

/-- Each object built as `Json.mkObj` builds it: sorted by key, the last of two equal keys kept. -/
def normalize : Json → Json
  | .arr elems => .arr (elems.map normalize)
  | .obj fields => mkObj (fields.toList.map fun field => (field.1, normalize field.2))
  | j => j
termination_by j => j
decreasing_by
  · decreasing_tactic
  · have := sizeOf_field_lt (Array.mem_toList_iff.mp ‹_›)
    simp only [obj.sizeOf_spec]
    omega

/-- How deep arrays and objects nest. -/
def depth : Json → Nat
  | .arr elems => elems.foldl (fun d elem => max d elem.depth) 0 + 1
  | .obj fields => fields.foldl (fun d field => max d field.2.depth) 0 + 1
  | _ => 0
termination_by j => j
decreasing_by
  · decreasing_tactic
  · have := sizeOf_field_lt ‹_›
    simp only [obj.sizeOf_spec]
    omega

/-- The digits `JsonNumber.toString` writes, and more: a bound for `Json.parse`'s `maxDigits`. -/
def _root_.Lanes.JsonNumber.digits (n : JsonNumber) : Nat :=
  (Nat.toDigits 10 n.mantissa.natAbs).length + n.exponent

/-- The most `JsonNumber.digits` of a number in the value. -/
def digits : Json → Nat
  | .num n => n.digits
  | .arr elems => elems.foldl (fun d elem => max d elem.digits) 0
  | .obj fields => fields.foldl (fun d field => max d field.2.digits) 0
  | _ => 0
termination_by j => j
decreasing_by
  · decreasing_tactic
  · have := sizeOf_field_lt ‹_›
    simp only [obj.sizeOf_spec]
    omega

end Lanes.Json
