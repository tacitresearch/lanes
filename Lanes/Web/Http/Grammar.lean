/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
The rules HTTP's fields are written in (RFC 9110 §5.5, §5.6): tokens, the blanks around a value,
the characters a value may hold, and quoted strings. The wire format, cookies and media types
read and write their text with these, so there is one definition of each.
-/

@[expose] public section

namespace Lanes.Http

/-- A character of an RFC 9110 token (`tchar`), which is what a header's name is. -/
def tokenChar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c

def token (s : String) : Bool :=
  s != "" && s.toList.all tokenChar

/-- No control character but tab: what a header's value may hold. -/
def plain (c : Char) : Bool :=
  c == '\t' || (32 ≤ c.val && c.val != 127)

def visible (c : Char) : Bool :=
  33 ≤ c.val && c.val ≤ 126

/-- The blanks a header's value may have around it (`OWS`). -/
def ows (c : Char) : Bool :=
  c == ' ' || c == '\t'

def trimOws (chars : List Char) : List Char :=
  ((chars.dropWhile ows).reverse.dropWhile ows).reverse

/-- What a quoted string holds without a backslash (`qdtext`): anything but controls, `"` and
`\`. -/
def isQdtext (c : Char) : Bool :=
  c == '\t' || c == ' ' || c == '!' || ('#' ≤ c && c ≤ '[') || (']' ≤ c && c ≤ '~') || 0x80 ≤ c.toNat

/-- What a quoted string can hold at all: anything but controls other than tab. -/
def isQuotable (c : Char) : Bool := c == '\t' || (' ' ≤ c && c ≤ '~') || 0x80 ≤ c.toNat

/-- A quoted string after its opening quote: its text, and what follows the closing quote. -/
def quoted : List Char → Option (List Char × List Char)
  | '"' :: rest => some ([], rest)
  | '\\' :: c :: rest =>
    if isQuotable c then (quoted rest).map fun (v, r) => (c :: v, r) else none
  | c :: rest => if isQdtext c then (quoted rest).map fun (v, r) => (c :: v, r) else none
  | [] => none

theorem visible_of_tokenChar {c : Char} (h : tokenChar c) : visible c := by
  rcases Bool.or_eq_true _ _ |>.mp h with alnum | symbol
  · simp only [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, visible,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le,
      ge_iff_le] at *
    simp at *
    omega
  · have all : "!#$%&'*+-.^_`|~".toList.all visible = true := by decide
    exact List.all_eq_true.mp all c (List.contains_iff_mem.mp symbol)

theorem plain_of_visible {c : Char} (h : visible c) : plain c := by
  simp only [visible, plain, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    UInt32.le_iff_toNat_le, bne_iff_ne, ne_eq, beq_iff_eq] at *
  refine .inr ⟨h.1 |> Nat.le_trans (by decide), ?_⟩
  intro eq
  rw [eq] at h
  exact absurd h.2 (by decide)

end Lanes.Http
