/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Generated

/-!
# The changelog's fragments

An unreleased change is a file of its own in `docs/changes/`, as Go's `doc/next/` is, so two
branches never edit one list. A fragment has one or more sections (`### Added`), each followed
by its entries (`- …`); a line that starts with two spaces continues the entry before it.
`CHANGELOG.md` holds the released history. `lanes changelog` prints the Unreleased section,
gathered from the fragments; `lanes changelog --release X.Y.Z DATE` writes it into
`CHANGELOG.md` as that release and deletes the fragments (`docs/RELEASING.md`).
-/

namespace Lanes.Cli.Changelog

open Generated

def changesDir : String := "docs/changes"

/-- Keep a Changelog's sections, in its order. -/
def sections : List String := ["Added", "Changed", "Deprecated", "Removed", "Fixed", "Security"]

/-- A fragment's entries, by section in the order it gives them. -/
abbrev Fragment := List (String × List String)

/-- A fragment read, or the line of its first problem and what it is. -/
def parse (text : String) : Except (Nat × String) Fragment := do
  let mut out : Fragment := []
  for (line, k) in (text.splitOn "\n").zipIdx do
    if line.trimAscii.isEmpty then continue
    if line.startsWith "### " then
      let name := (line.drop 4).trimAscii.toString
      unless sections.contains name do
        throw (k + 1, s!"`### {name}` is not a section: write one of {", ".intercalate sections}")
      out := out ++ [(name, [])]
    else if line.startsWith "- " || line.startsWith "  " then
      let some (name, entries) := out.getLast? |
        throw (k + 1, "an entry comes after its section's heading, such as `### Added`")
      let entries := if line.startsWith "- " then entries ++ [line]
        else match entries.getLast? with
          | some last => entries.dropLast ++ [last ++ "\n" ++ line]
          | none => entries
      if entries.isEmpty then throw (k + 1, "a continued line comes after an entry, `- …`")
      out := out.dropLast ++ [(name, entries)]
    else
      throw (k + 1, "a line is a heading (`### Added`), an entry (`- …`) or the entry's next line")
  if out.isEmpty then throw (1, "a fragment has a section, such as `### Added`, and an entry")
  if let some (name, _) := out.find? (·.2.isEmpty) then
    throw (1, s!"`### {name}` has no entry")
  return out

/-- The fragments' files, by name. -/
def files (root : System.FilePath) : IO (List String) := do
  return (← markdownIn (root / changesDir)).filter (· != "README.md")

/-- The fragments read, by name, and the problems of those that cannot be. -/
def read (root : System.FilePath) : IO (List Fragment × List Problem) := do
  let mut fragments := []
  let mut problems := []
  for name in ← files root do
    let path := s!"{changesDir}/{name}"
    match parse (← IO.FS.readFile (root / path)) with
    | .ok f => fragments := fragments ++ [f]
    | .error (line, message) => problems := problems ++ [(path, line, "changelog", message)]
  return (fragments, problems)

/-- The sections of a release: each section's entries from every fragment, in the fragments'
order. -/
def assemble (fragments : List Fragment) : String :=
  let parts := sections.filterMap fun name =>
    let entries := fragments.flatMap fun f => (f.filter (·.1 == name)).flatMap (·.2)
    if entries.isEmpty then none
    else some (s!"### {name}\n\n" ++ "\n".intercalate entries ++ "\n")
  "\n".intercalate parts

def unreleasedHeading : String := "## [Unreleased]"

/-- The lines of `CHANGELOG.md`'s Unreleased section that are entries: they belong in
fragments. -/
def strayEntries (changelog : String) : List Nat := Id.run do
  let mut inside := false
  let mut out := []
  for (line, k) in (changelog.splitOn "\n").zipIdx do
    if line.startsWith "## " then inside := line == unreleasedHeading
    else if inside && line.startsWith "- " then out := out ++ [k + 1]
  return out

/-- Lint `changelog`, in a project with `docs/changes/`: each fragment reads, and
`CHANGELOG.md`'s Unreleased section has no entries of its own. -/
def check (root : System.FilePath) : IO (List Problem) := do
  if !(← (root / changesDir).isDir) then return []
  let (_, problems) ← read root
  let stray := match ← readIfExists (root / "CHANGELOG.md") with
    | some text => (strayEntries text).map fun line => ("CHANGELOG.md", line, "changelog",
      s!"an unreleased change is a file in `{changesDir}/`, not a line here (`CONTRIBUTING.md`)")
    | none => []
  return problems ++ stray

/-- `CHANGELOG.md` with the release's section put after the Unreleased section's text, before
the release above it. -/
def insertRelease (changelog version date body : String) : Except String String := do
  let lines := changelog.splitOn "\n"
  let some start := lines.findIdx? (· == unreleasedHeading) |
    throw s!"CHANGELOG.md has no line `{unreleasedHeading}`"
  let after := lines.drop (start + 1)
  let next := (after.findIdx? (·.startsWith "## [")).getD after.length
  let (unreleased, older) := (after.take next, after.drop next)
  let unreleased := (unreleased.reverse.dropWhile (·.trimAscii.isEmpty)).reverse
  let release := s!"## [{version}] - {date}\n\n{body}"
  return "\n".intercalate (lines.take (start + 1) ++ unreleased ++ [""] ++ release.splitOn "\n"
    ++ older)

/-- `lanes changelog [--release <version> <date>]`. -/
def run (root : System.FilePath) (args : List String) : IO UInt32 := do
  let (fragments, problems) ← read root
  for (file, line, rule, message) in problems do
    IO.eprintln s!"{file}:{line}: [{rule}] {message}"
  if !problems.isEmpty then return 1
  match args with
  | [] =>
    IO.print (if fragments.isEmpty then "No unreleased changes.\n" else assemble fragments)
    return 0
  | ["--release", version, date] =>
    if fragments.isEmpty then
      IO.eprintln s!"lanes changelog: no fragments in {changesDir}/"
      return 1
    let changelog ← IO.FS.readFile (root / "CHANGELOG.md")
    match insertRelease changelog version date (assemble fragments) with
    | .error e =>
      IO.eprintln s!"lanes changelog: {e}"
      return 1
    | .ok text =>
      IO.FS.writeFile (root / "CHANGELOG.md") text
      let names ← files root
      for name in names do IO.FS.removeFile (root / changesDir / name)
      IO.println s!"wrote [{version}] in CHANGELOG.md from {names.length} fragments, and removed them"
      return 0
  | _ =>
    IO.eprintln "usage: lanes changelog [--release <version> <date>]"
    return 1

end Lanes.Cli.Changelog
