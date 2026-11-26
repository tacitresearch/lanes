/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Ported from Lean 4 core (`Lean.Data.Json.Printer`), Copyright (c) 2019 Gabriel Ebner, Microsoft
Corporation and Lean FRO, Apache 2.0.
Authors: Gabriel Ebner, Marc Huisinga, Wojciech Nawrocki
-/
module

public import Lanes.Data.Json.Basic

/-!
# JSON printer

`Json.compress` writes a value as JSON text with no whitespace, and `Json.pretty` writes it with
one element or field per line. Both print the fields of an object in the order they are stored,
which for objects built by `Json.mkObj` or the parser is the order of their keys, so the output is
deterministic.

In strings, the quote, the backslash and the control characters below U+0020 are escaped; every
other character, non-ASCII ones included, is written as it is.

The printers write straight into a `String`: the original goes through `Lean.Format`, which
runtime modules cannot import. They recurse once per level of nesting.
-/

@[expose] public section

namespace Lanes.Json

def needsEscape (c : Char) : Bool :=
  c == '"' || c == '\\' || c.val < 0x20

def escapeChar (acc : String) (c : Char) : String :=
  if c == '"' then acc ++ "\\\""
  else if c == '\\' then acc ++ "\\\\"
  else if c == '\n' then acc ++ "\\n"
  else if c == '\r' then acc ++ "\\r"
  else if c == '\t' then acc ++ "\\t"
  else if c == '\x08' then acc ++ "\\b"
  else if c == '\x0c' then acc ++ "\\f"
  else if c.val < 0x20 then
    (acc ++ "\\u00").push (Nat.digitChar (c.toNat / 16)) |>.push (Nat.digitChar (c.toNat % 16))
  else acc.push c

def escape (s : String) (acc : String := "") : String :=
  if s.any needsEscape then s.foldl escapeChar acc else acc ++ s

def renderString (s : String) (acc : String := "") : String :=
  (escape s (acc.push '"')).push '"'

@[inline] def separate (acc : String) (first : Bool) : String :=
  if first then acc else acc.push ','

def compressTo (acc : String) : Json → String
  | .null => acc ++ "null"
  | .bool true => acc ++ "true"
  | .bool false => acc ++ "false"
  | .num n => acc ++ n.toString
  | .str s => renderString s acc
  | .arr elems =>
    let state := elems.foldl (init := (acc.push '[', true)) fun (state : String × Bool) elem =>
      (compressTo (separate state.1 state.2) elem, false)
    state.1.push ']'
  | .obj fields =>
    let state := fields.foldl (init := (acc.push '{', true)) fun (state : String × Bool) field =>
      (compressTo ((renderString field.1 (separate state.1 state.2)).push ':') field.2, false)
    state.1.push '}'
termination_by j => j
decreasing_by
  · decreasing_tactic
  · have := sizeOf_field_lt ‹_›
    simp only [obj.sizeOf_spec]
    omega

/-- The text of a value with no whitespace. Parsing it gives the value back. -/
def compress (j : Json) : String :=
  compressTo "" j

def newline (indent level : Nat) : String :=
  "\n".pushn ' ' (indent * level)

def prettyTo (indent level : Nat) (acc : String) : Json → String
  | .arr elems =>
    if elems.isEmpty then acc ++ "[]"
    else
      let state := elems.foldl (init := (acc.push '[', true)) fun (state : String × Bool) elem =>
        let acc := separate state.1 state.2 ++ newline indent (level + 1)
        (prettyTo indent (level + 1) acc elem, false)
      (state.1 ++ newline indent level).push ']'
  | .obj fields =>
    if fields.isEmpty then acc ++ "{}"
    else
      let state := fields.foldl (init := (acc.push '{', true)) fun (state : String × Bool) field =>
        let acc := separate state.1 state.2 ++ newline indent (level + 1)
        (prettyTo indent (level + 1) (renderString field.1 acc ++ ": ") field.2, false)
      (state.1 ++ newline indent level).push '}'
  | j => compressTo acc j
termination_by j => j
decreasing_by
  · decreasing_tactic
  · have := sizeOf_field_lt ‹_›
    simp only [obj.sizeOf_spec]
    omega

/-- One array element or object field per line. Parsing it gives the value back. -/
def pretty (j : Json) (indent : Nat := 2) : String :=
  prettyTo indent 0 "" j

instance : ToString Json := ⟨compress⟩

end Lanes.Json
