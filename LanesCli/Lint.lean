/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Generated

/-!
# `lanes lint`

Source-level checks of the rules in `AGENTS.md` that can be decided from the text of a project:

- `no-sorry` (rule 4): no `sorry` or `admit`.
- `trusted-listed` (rule 5.5): `partial`, `unsafe`, `axiom`, `panic!`, `@[implemented_by]` and
  `@[extern]` appear only in files named in `TRUSTED.md`, and so does every C file, all of
  which is trusted.
- `trusted-size` (rule 5.5): a file that `TRUSTED.md` lists as `` `path`, N lines `` has `N`
  lines, so trusted code cannot grow without the list changing; `--fix` rewrites the counts.
- `decisions`, `status`: the files `LanesCli/Generated.lean` derives agree with their sources.
- `layering` (rule 1.6): files that import Mathlib, CSLib or a proof module (`Lanes.Semantics`,
  `App.Proofs`) live in a proof directory, one named `…Proofs` included, or are named
  `…Proofs.lean`, so executable code never links them.

Comments and string literals are ignored. The checks that need the elaborator (`no-io-in-step`,
`bounded`, `field-leak`) are not implemented yet.
-/

namespace Lanes.Cli.Lint

structure Finding where
  file : System.FilePath
  line : Nat
  rule : String
  message : String

/-- Replace comments and string literals by spaces, keeping line breaks, so that later checks
see only code. -/
def stripCommentsAndStrings (src : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut depth := 0          -- nesting depth of block comments
  let mut inLine := false     -- inside a line comment
  let mut inString := false
  let mut skip := 0           -- characters already handled
  let chars := src.toList.toArray
  for h : k in [0:chars.size] do
    let c := chars[k]
    let next := chars[k + 1]?
    let blank := if c == '\n' then '\n' else ' '
    if skip > 0 then
      skip := skip - 1
      out := out.push blank
    else if inLine then
      if c == '\n' then inLine := false
      out := out.push blank
    else if depth > 0 then
      if c == '/' && next == some '-' then
        depth := depth + 1
        skip := 1
      else if c == '-' && next == some '/' then
        depth := depth - 1
        skip := 1
      out := out.push blank
    else if inString then
      if c == '\\' then skip := 1
      else if c == '"' then inString := false
      out := out.push blank
    else if c == '-' && next == some '-' then
      inLine := true
      out := out.push blank
    else if c == '/' && next == some '-' then
      depth := 1
      skip := 1
      out := out.push blank
    else if c == '"' then
      inString := true
      out := out.push blank
    else if c == '\'' && chars[k + 2]? == some '\'' then
      -- A character literal such as '"' must not open a string.
      skip := 2
      out := out.push blank
    else
      out := out.push c
  return String.ofList out.toList

def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '!' || c == '?' || c == '\''

def hasWord (line word : String) : Bool :=
  (line.splitOn word).length > 1 && Id.run do
    let parts := line.splitOn word
    let mut found := false
    for k in [0:parts.length - 1] do
      let before := parts[k]!.toList.getLast?
      let after := parts[k + 1]!.toList.head?
      let startsOk := before.all (!isWordChar ·)
      -- `panic!` ends in `!`, so only letters and digits continue a word here.
      let endsOk := after.all fun c => !(c.isAlphanum || c == '_')
      if startsOk && endsOk then found := true
    return found

def trustedWords : List String :=
  ["partial", "unsafe", "axiom", "panic!", "implemented_by", "extern"]

def proofDirs : List String :=
  ["Semantics", "Temporal", "Proofs", "Examples", "Tests"]

def isProofFile (file : System.FilePath) : Bool :=
  file.components.any fun part =>
    proofDirs.contains part || part.endsWith "Proofs" || part.endsWith "Proofs.lean"
      || proofDirs.any fun dir => part == dir ++ ".lean"

def importsProofModule (line : String) : Bool :=
  match (line.splitOn " ").filter (· != "") |>.getLast? with
  | some module =>
    (module.splitOn ".").any fun part =>
      part == "Semantics" || part == "Temporal" || part.endsWith "Proofs"
  | none => false

/-- `trusted` is the text of `TRUSTED.md`. -/
def checkFile (root file : System.FilePath) (trusted : String) : IO (List Finding) := do
  let src ← IO.FS.readFile file
  let relative := (file.toString.dropPrefix (root.toString ++ "/")).toString
  let listed := Generated.occursIn relative.toUTF8 trusted.toUTF8
  let code := stripCommentsAndStrings src
  let mut findings : List Finding := []
  for (text, k) in (code.splitOn "\n").zipIdx do
    let line := k + 1
    for word in ["sorry", "admit"] do
      if hasWord text word then
        findings := ⟨relative, line, "no-sorry", s!"`{word}` is not allowed (rule 4)"⟩ :: findings
    if !listed then
      for word in trustedWords do
        if hasWord text word then
          findings := ⟨relative, line, "trusted-listed",
            s!"`{word}` in a file that TRUSTED.md does not name (rule 5.5)"⟩ :: findings
    if !isProofFile relative then
      let t := text.trimAscii.toString
      if t.startsWith "import " || t.startsWith "public import " then
        if hasWord t "Mathlib" || hasWord t "Cslib" || (t.splitOn "import Mathlib.").length > 1
            || (t.splitOn "import Cslib.").length > 1 then
          findings := ⟨relative, line, "layering",
            "Mathlib and CSLib may only be imported from proof files (rule 1.6)"⟩ :: findings
        else if importsProofModule t then
          findings := ⟨relative, line, "layering",
            "a proof module imported from executable code links Mathlib into the binary "
              ++ "(rule 1.6)"⟩ :: findings
  return findings.reverse

def sourceFiles (root : System.FilePath) (extension : String := "lean") :
    IO (Array System.FilePath) := do
  let files ← root.walkDir fun dir =>
    let name := dir.fileName.getD ""
    return !(name.startsWith "." || name == "templates")
  return (files.filter fun f => f.extension == some extension).qsort (·.toString < ·.toString)

def checkC (root file : System.FilePath) (trusted : String) : List Finding :=
  let relative := (file.toString.dropPrefix (root.toString ++ "/")).toString
  if (trusted.splitOn relative).length > 1 then []
  else [⟨relative, 1, "trusted-listed", "C in a file that TRUSTED.md does not name (rule 5.5)"⟩]

structure Options where
  /-- Rewrite the generated files instead of reporting them. -/
  fix : Bool := false
  /-- This is the main branch: decisions without a number are numbered, or reported. -/
  main : Bool := false

structure Report where
  findings : List Finding
  fixed : List Generated.Edit
  files : Nat

def lint (root : System.FilePath) (options : Options := {}) : IO Report := do
  let fixed ← if options.fix then Generated.fix root options.main else pure []
  let plan ← Generated.plan root options.main
  let mut findings : List Finding :=
    plan.problems.map (fun (file, line, rule, message) => ⟨file, line, rule, message⟩)
      ++ plan.edits.map fun e => ⟨e.path, 1, e.rule, e.message⟩
  let trustedFile := root / "TRUSTED.md"
  let trusted ← if ← trustedFile.pathExists then IO.FS.readFile trustedFile else pure ""
  let files ← sourceFiles root
  findings := findings ++ (← sourceFiles root "c").toList.flatMap (checkC root · trusted)
  for file in files do
    findings := findings ++ (← checkFile root file trusted)
  return ⟨findings, fixed, files.size⟩

def run (root : System.FilePath) (options : Options := {}) : IO Nat := do
  let report ← lint root options
  for e in report.fixed do
    IO.println s!"fixed {e.describe}"
  for f in report.findings do
    IO.println s!"{f.file}:{f.line}: [{f.rule}] {f.message}"
  let count := report.findings.length
  if count == 0 then
    IO.println s!"lanes lint: {report.files} files, no findings"
  else
    IO.println s!"lanes lint: {count} findings in {report.files} files"
  return count

end Lanes.Cli.Lint
