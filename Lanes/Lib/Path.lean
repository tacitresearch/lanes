/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
Paths of names separated by `/`, as in URLs and on POSIX systems. `clean` is Go's `path.Clean`:
one `/` between names, no `.`, a `..` only at the start of a relative path, `.` for the empty
path, and no `/` at the end but for the root. It is idempotent (`Path.clean_clean`, in
`Lanes/Lib/PathSound.lean`). `join` is Go's `path.Join`.

`under root rel` is the file a request for `rel` names below the directory `root`, for serving
files: `rel` is read as relative, even if it starts with `/`, and is refused if its `..` would
climb out of `root` or it holds a NUL. What it returns is `clean root` followed by names, none of
them `.`, `..` or empty (`Path.under_names`). A symbolic link below `root` can still lead
outside it: `under` reads text, not the file system.
-/

@[expose] public section

namespace Lanes.Path

/-- A name is not empty, not `.` or `..`, and holds no `/` or NUL. -/
def isName (n : List Char) : Bool :=
  !n.isEmpty && n != ['.'] && n != ['.', '.'] && !n.contains '/' && !n.contains '\x00'

/-- One name of a path, onto the names kept so far, last first. -/
def push (rooted : Bool) (acc : List (List Char)) (seg : List Char) : List (List Char) :=
  if seg.isEmpty || seg == ['.'] then acc
  else if seg == ['.', '.'] then
    match acc with
    | top :: rest => if top == ['.', '.'] then seg :: acc else rest
    | [] => if rooted then [] else [seg]
  else seg :: acc

/-- The names of a path once `.`, empty names and the `..` that can be resolved are gone. -/
def names (rooted : Bool) (p : List Char) : List (List Char) :=
  ((p.splitOn '/').foldl (push rooted) []).reverse

def isRooted (p : List Char) : Bool := p.head? == some '/'

def cleanChars (p : List Char) : List Char :=
  let ns := names (isRooted p) p
  if isRooted p then '/' :: ['/'].intercalate ns
  else if ns.isEmpty then ['.']
  else ['/'].intercalate ns

def clean (p : String) : String := String.ofList (cleanChars p.toList)

/-- The paths that are not empty, joined by `/` and cleaned; `""` if all are empty. -/
def join (ps : List String) : String :=
  match ps.filter (!·.isEmpty) with
  | [] => ""
  | ps => clean ("/".intercalate ps)

/-- The names of `rel` below a root, unless one would climb out of it or `rel` holds a NUL. -/
def namesBelow (rel : List Char) : Option (List (List Char)) :=
  let ns := names false rel
  if ns.head? == some ['.', '.'] || rel.contains '\x00' then none else some ns

/-- `root`, cleaned, then the names: under the root `/`, `/a/b`, not `//a/b`. -/
def below (root : List Char) (ns : List (List Char)) : List Char :=
  let base := cleanChars root
  if ns.isEmpty then base
  else (if base == ['/'] then [] else base) ++ ns.flatMap ('/' :: ·)

def under (root rel : String) : Option String :=
  (namesBelow rel.toList).map fun ns => String.ofList (below root.toList ns)

end Lanes.Path
