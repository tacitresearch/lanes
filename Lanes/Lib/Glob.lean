/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Glob patterns over paths separated by `/`, as Go's `path.Match` reads them: `*` is any
characters but `/`, `?` one character but `/`, `[...]` one character of a class (`[^...]` one
not in it, ranges `a-z`, `\` quoting), `\c` the character `c`, and anything else itself. A
pattern matches the whole name.

One addition, as in `.gitignore` and most build tools: `**` as a whole name of the pattern
matches across `/`. `**/` is any names, each followed by `/`, possibly none (`a/**/b` matches
`a/b` and `a/x/y/b`), and a last `**` is anything (`a/**` matches what is below `a/`). Elsewhere
`**` is `*`, as in Go.

`compile` reads a pattern once and refuses one that is malformed, as Go does with
`ErrBadPattern`; `Glob.matches` then runs the pattern as an automaton over the name, with no
backtracking: its time is the name's length times the square of the pattern's.
-/

@[expose] public section

namespace Lanes

namespace Glob

inductive Item where
  | one (c : Char)
  | range (lo hi : Char)
  deriving DecidableEq, Repr

def Item.has (c : Char) : Item → Bool
  | .one d => c == d
  | .range lo hi => lo ≤ c && c ≤ hi

inductive Node where
  | char (c : Char)
  /-- `?` -/
  | any
  | set (negated : Bool) (items : List Item)
  /-- `*` -/
  | star
  /-- A last `**`. -/
  | deep
  /-- `**/`, before a name of it starts. -/
  | dirs
  /-- Inside a name of `**/`; always just after `dirs`. -/
  | dirsMid
  deriving DecidableEq, Repr

end Glob

/-- A compiled pattern. -/
structure Glob where
  nodes : Array Glob.Node
  deriving DecidableEq, Repr

namespace Glob

/-- A character of a class: not `-` or `]`, or quoted by `\`. -/
def classChar : List Char → Option (Char × List Char)
  | '\\' :: c :: rest => some (c, rest)
  | c :: rest => if c == '\\' || c == '-' || c == ']' then none else some (c, rest)
  | [] => none

/-- The items of a class up to its `]`, which closes it only after an item. Each round reads a
character, so the pattern's length is fuel enough. -/
def classItems : Nat → Bool → List Char → Option (List Item × List Char)
  | 0, _, _ => none
  | fuel + 1, first, cs =>
    match cs with
    | ']' :: rest => if first then none else some ([], rest)
    | _ =>
      match classChar cs with
      | none => none
      | some (lo, '-' :: rest) =>
        match classChar rest with
        | none => none
        | some (hi, rest') => (classItems fuel false rest').map fun (is, r) => (.range lo hi :: is, r)
      | some (c, rest) => (classItems fuel false rest).map fun (is, r) => (.one c :: is, r)

/-- Whether a run of stars is a whole name of the pattern: after its start or `/`, and before its
end or `/`. -/
def wholeName (before : Option Char) (after : List Char) : Bool :=
  (before.isNone || before == some '/') && (after.isEmpty || after.head? == some '/')

def parse : Nat → Option Char → List Char → Option (List Node)
  | 0, _, _ => none
  | _, _, [] => some []
  | fuel + 1, before, c :: rest =>
    match c with
    | '\\' =>
      match rest with
      | d :: rest' => (parse fuel (some d) rest').map (.char d :: ·)
      | [] => none
    | '?' => (parse fuel (some c) rest).map (.any :: ·)
    | '[' =>
      let (negated, body) := match rest with
        | '^' :: body => (true, body)
        | body => (false, body)
      match classItems (body.length + 1) true body with
      | some (items, rest') => (parse fuel (some ']') rest').map (.set negated items :: ·)
      | none => none
    | '*' =>
      let more := rest.takeWhile (· == '*')
      let after := rest.drop more.length
      if more.length == 1 && wholeName before after then
        match after with
        | '/' :: after' => (parse fuel (some '/') after').map ([.dirs, .dirsMid] ++ ·)
        | _ => (parse fuel (some '*') after).map (.deep :: ·)
      else (parse fuel (some '*') after).map (.star :: ·)
    | _ => (parse fuel (some c) rest).map (.char c :: ·)

/-- The pattern compiled, or `none` if it is malformed. -/
def compile (pattern : String) : Option Glob :=
  (parse (pattern.length + 1) none pattern.toList).map fun ns => ⟨ns.toArray⟩

/-! ### Matching -/

/-- The states reached from `i` without reading: past a `*`, a last `**` or a `**/`. -/
def close (ns : Array Node) (i : Nat) : List Nat :=
  if h : i < ns.size then
    match ns[i] with
    | .star | .deep => i :: close ns (i + 1)
    | .dirs => i :: close ns (i + 2)
    | _ => [i]
  else [i]
termination_by ns.size - i

/-- Where state `i` goes on `c`. -/
def next (ns : Array Node) (i : Nat) (c : Char) : List Nat :=
  if h : i < ns.size then
    match ns[i] with
    | .char d => if c == d then [i + 1] else []
    | .any => if c == '/' then [] else [i + 1]
    | .set negated items => if items.any (·.has c) != negated then [i + 1] else []
    | .star => if c == '/' then [] else [i]
    | .deep => [i]
    | .dirs => if c == '/' then [i] else [i + 1]
    | .dirsMid => if c == '/' then [i - 1] else [i]
  else []

def union (a b : List Nat) : List Nat := b.foldl (fun acc j => if acc.contains j then acc else j :: acc) a

def stepAll (ns : Array Node) (states : List Nat) (c : Char) : List Nat :=
  states.foldl (fun acc i => (next ns i c).foldl (fun acc j => union acc (close ns j)) acc) []

end Glob

/-- Whether the pattern matches all of `name`. -/
def Glob.matches (g : Glob) (name : String) : Bool :=
  (name.foldl (Glob.stepAll g.nodes) (Glob.close g.nodes 0)).contains g.nodes.size

/-- Go's `path.Match`: `none` if the pattern is malformed. -/
def Glob.check (pattern name : String) : Option Bool := (Glob.compile pattern).map (·.matches name)

end Lanes
