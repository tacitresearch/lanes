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
- `links`: every repository path that a Markdown file at the root or under `docs/` writes in
  backquotes exists (`a/{b,c}.lean` names two). `docs/history/` and `docs/decisions/` record
  the past and are not checked.
- `oracles`, where there is an `oracles/README.md`: its tables name a reference for each folder
  of `oracles/`, and an oracle, or why there is none, for each module of `Lanes/Lib/` and
  `Lanes/Web/` and each model of `Lanes/Outside/` that is not a proof or IO; every module and
  path they name exists (`docs/decisions/new-oracles.md`).
- `inventory`, `inventory-none`, in Lanes itself: `docs/INVENTORY.md` is up to date, and every
  definition of `Lanes/` without evidence is on `docs/inventory-none.md`. These read the built
  modules, so `lanesInventory`, which links `Lean`, does them; `--fix` has it rewrite the file.

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

/-! ## Paths that docs cite -/

/-- The inline code spans of Markdown text outside fenced blocks, each with the line it starts
on. A span that runs past the end of its line is kept open, so the spans after it stay paired. -/
def codeSpans (text : String) : List (Nat × String) := Id.run do
  let mut spans : Array (Nat × String) := #[]
  let mut fenced := false
  -- An open span: how many backquotes opened it, its line, and its text so far.
  let mut current : Option (Nat × Nat × Array Char) := none
  for (line, k) in (text.splitOn "\n").zipIdx do
    if line.trimAsciiStart.toString.startsWith "```" then
      fenced := !fenced
      continue
    if fenced then continue
    let chars := line.toList.toArray
    let mut i := 0
    while h : i < chars.size do
      if chars[i] == '`' then
        let mut j := i
        while j < chars.size && chars[j]! == '`' do j := j + 1
        let run := j - i
        match current with
        | none => current := some (run, k + 1, #[])
        | some (ticks, start, acc) =>
          if run == ticks then
            spans := spans.push (start, String.ofList acc.toList)
            current := none
          else current := some (ticks, start, acc ++ (Array.replicate run '`'))
        i := j
      else
        if let some (ticks, start, acc) := current then
          current := some (ticks, start, acc.push chars[i])
        i := i + 1
    if let some (ticks, start, acc) := current then
      current := some (ticks, start, acc.push ' ')
  return spans.toList

/-- The text before the first `{`, inside it up to the next `}`, and after that. -/
def firstBraces (path : String) : Option (String × String × String) :=
  match path.splitOn "{" with
  | before :: after :: rest =>
    match ("{".intercalate (after :: rest)).splitOn "}" with
    | inner :: tail :: more => some (before, inner, "}".intercalate (tail :: more))
    | _ => none
  | _ => none

/-- `a/{b,c}.lean` as `a/b.lean` and `a/c.lean`; a path without braces as itself. Each round
takes one group of braces out of every path, and a path has fewer groups than characters. -/
def expandBraces (path : String) : List String := Id.run do
  let mut done : List String := []
  let mut todo := [path]
  for _ in [0:path.length] do
    let mut next : List String := []
    for p in todo do
      match firstBraces p with
      | some (before, inner, after) => next := next ++ (inner.splitOn ",").map (before ++ · ++ after)
      | none => done := done ++ [p]
    todo := next
  return done ++ todo

/-- A code span that is written as a path in the repository: it has a `/`, no blanks and no
placeholder (`<area>`, `*`, `…`), and its first part is at the root of the project. Module
names (`Lanes.Http`), Go packages (`net/http`) and URLs are not. -/
def citedPaths (root : System.FilePath) (span : String) : IO (List String) := do
  let bad := [' ', '\t', '<', '>', '*', '?', '$', '|', '…', '"', '\'', '(', ')', '#', ':', '=']
  if !span.contains '/' || span.any (bad.contains ·) || span.startsWith "/"
      || span.startsWith "~" || span.startsWith "-" || span.contains '\\' then
    return []
  let paths := expandBraces span
  let first := (span.splitOn "/").headD ""
  if first.isEmpty || first == "." || first == ".." || first == ".lake" || first == ".git"
      || first.contains '{' || !(← (root / first).pathExists) then
    return []
  return paths

/-- The Markdown files whose citations are checked: those at the root and under `docs/`, but
not the records of the past, `docs/history/` and `docs/decisions/`, nor `docs/STATUS.md`, which
is written from `docs/status/`, whose fragments are checked instead. -/
def citingDocs (root : System.FilePath) : IO (List String) := do
  let top := (← Generated.markdownIn root)
  let docs := root / "docs"
  let nested ← if ← docs.isDir then
      docs.walkDir fun dir => return !["history", "decisions"].contains (dir.fileName.getD "")
    else pure #[]
  let below := nested.toList.filterMap fun file =>
    let relative := (file.toString.dropPrefix (root.toString ++ "/")).toString
    if file.extension == some "md" && relative != "docs/STATUS.md" then some relative else none
  return top ++ Generated.sortStrings below

/-- `links`: every repository path a doc cites in backquotes exists. -/
def checkLinks (root : System.FilePath) : IO (List Finding) := do
  let mut findings : List Finding := []
  for doc in ← citingDocs root do
    for (line, span) in codeSpans (← IO.FS.readFile (root / doc)) do
      for path in ← citedPaths root span do
        if !(← (root / path).pathExists) then
          findings := ⟨doc, line, "links", s!"`{path}` does not exist"⟩ :: findings
  return findings.reverse

/-! ## The oracles' manifest -/

/-- The cells of a Markdown table's row: `| a | b |` is `["a", "b"]`. -/
def cells (line : String) : List String :=
  ((line.trimAscii.toString.splitOn "|").drop 1).dropLast.map (·.trimAscii.toString)

/-- The rows of the table under `heading`, each with its line, without its head and rule. -/
def tableRows (text heading : String) : List (Nat × List String) :=
  let lines := (text.splitOn "\n").zipIdx
  let after := (lines.dropWhile (·.1 != heading)).drop 1
  let section_ := after.takeWhile fun (l, _) => !l.startsWith "#"
  let rows := section_.filter (·.1.startsWith "|")
  (rows.drop 2).map fun (l, i) => (i + 1, cells l)

def spans (cell : String) : List String := (codeSpans cell).map (·.2)

/-- The modules under `dirs` that must have a row: neither proofs (`…Sound.lean`) nor IO. -/
def inScope (root : System.FilePath) (dirs : List String) : IO (List String) := do
  let mut out := []
  for dir in dirs do
    if ← (root / dir).isDir then
      for file in ← sourceFiles (root / dir) do
        let relative := (file.toString.dropPrefix (root.toString ++ "/")).toString
        unless relative.endsWith "Sound.lean" || (relative.splitOn "/").contains "IO" do
          out := out ++ [relative]
  return out

/-- `oracles`: `oracles/README.md` has a row for each folder of `oracles/`, for each module of
`Lanes/Lib/` and `Lanes/Web/` and each model of `Lanes/Outside/`, but proofs and IO; a module's
row names an oracle or says why there is none; and every module and path the rows name exists. -/
def checkOracles (root : System.FilePath) : IO (List Finding) := do
  let doc := "oracles/README.md"
  unless ← (root / doc).pathExists do return []
  let text ← IO.FS.readFile (root / doc)
  let mut findings : List Finding := []
  let refs := tableRows text "## References"
  for (line, row) in refs do
    for path in spans (row.headD "") do
      unless ← (root / path).isDir do
        findings := findings ++ [⟨doc, line, "oracles", s!"`{path}` is not a folder"⟩]
  for entry in ← (root / "oracles").readDir do
    if ← entry.path.isDir then
      let folder := s!"oracles/{entry.fileName}"
      unless refs.any (fun (_, row) => (spans (row.headD "")).contains folder) do
        findings := findings ++ [⟨doc, 1, "oracles",
          s!"`{folder}` has no row under References: its reference, version and pin"⟩]
  for (heading, dirs) in [("## Protocol modules", ["Lanes/Lib", "Lanes/Web"]),
      ("## Outside models", ["Lanes/Outside"])] do
    let rows := tableRows text heading
    for (line, row) in rows do
      match row with
      | first :: oracle :: rest =>
        let oracles ← (spans oracle).flatMapM (citedPaths root)
        let cited ← (rest.flatMap spans).flatMapM (citedPaths root)
        for path in spans first ++ oracles ++ cited do
          unless ← (root / path).pathExists do
            findings := findings ++ [⟨doc, line, "oracles", s!"`{path}` does not exist"⟩]
        if oracles.isEmpty && (rest.headD "").isEmpty then
          findings := findings ++ [⟨doc, line, "oracles",
            s!"{", ".intercalate (spans first)} names no oracle and gives no reason"⟩]
      | _ => findings := findings ++ [⟨doc, line, "oracles", "a row of fewer than three cells"⟩]
    let listed := rows.flatMap fun (_, row) => spans (row.headD "")
    for module in ← inScope root dirs do
      unless listed.contains module do
        findings := findings ++ [⟨doc, 1, "oracles",
          s!"`{module}` has no row under {heading.drop 3}: name its oracle, or why it has none"⟩]
  return findings

structure Options where
  /-- Rewrite the generated files instead of reporting them. -/
  fix : Bool := false
  /-- This is the main branch: decisions without a number are numbered, or reported. -/
  main : Bool := false

structure Report where
  findings : List Finding
  fixed : List Generated.Edit
  files : Nat

/-- `path:line: [rule] message`, as `lanesInventory` prints a finding. -/
def parseFinding (text : String) : Option Finding := do
  let (place, rest) ← match text.splitOn ": [" with
    | place :: rest@(_ :: _) => some (place, ": [".intercalate rest)
    | _ => none
  let (file, line) ← match place.splitOn ":" with
    | [file, line] => line.toNat?.map (file, ·)
    | _ => none
  let (rule, message) ← match rest.splitOn "] " with
    | rule :: message@(_ :: _) => some (rule, "] ".intercalate message)
    | _ => none
  return ⟨file, line, rule, message⟩

/-- The inventory's findings, in Lanes itself: a project with `Lanes.lean` and the inventory's
program. They need the built modules and `Lean`, so `lanesInventory` finds them. -/
def inventory (root : System.FilePath) (fix : Bool) : IO (List Finding) := do
  if !(← (root / "Lanes.lean").pathExists) || !(← (root / "LanesCli" / "Inventory.lean").pathExists)
  then return []
  let mode := if fix then "--fix" else "--check"
  let out ← IO.Process.output
    { cmd := "lake", args := #["exe", "lanesInventory", mode], cwd := some root }
  let findings := (out.stdout.splitOn "\n").filterMap parseFinding
  if out.exitCode != 0 && findings.isEmpty then
    return [⟨"docs/INVENTORY.md", 1, "inventory",
      s!"`lake exe lanesInventory` failed: {(out.stderr ++ out.stdout).trimAscii}"⟩]
  return findings

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
  findings := findings ++ (← checkLinks root)
  findings := findings ++ (← checkOracles root)
  findings := findings ++ (← inventory root options.fix)
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
