/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# What `lanes lint --fix` writes

Text that is derived from other files, so that no one types it and two branches never edit it
by hand:

- the line counts in `TRUSTED.md` (`` `path.lean`, N lines `` or `` `path.c`, N lines ``), from
  the files;
- the index of `docs/decisions/README.md`, from the decisions' headings and status lines,
  current ones first, and the numbers of new decisions (`new-<slug>.md`, `# D?. Title`), given
  on the main branch only.

Every line written is about one item: one file or one decision. No line holds a count
or a total over the repository, so two branches that change different items never change the
same line, and git merges them. `lanes stats` prints the totals.

Each part is a plan: the edits that would make the files agree, and the findings no edit can
fix. `lanes lint` reports the edits as findings; `lanes lint --fix` performs them.
-/

namespace Lanes.Cli.Generated

inductive Change where
  | write (text : String)
  /-- The file moves to `new` and then holds `text`. -/
  | move (new text : String)

/-- A change to the file at `path`, relative to the project's root, and what `lanes lint`
reports while it is not made. -/
structure Edit where
  path : String
  change : Change
  rule : String
  message : String

/-- A problem `--fix` cannot repair: a file, a line, a rule and a message. -/
abbrev Problem := String × Nat × String × String

structure Plan where
  edits : List Edit := []
  problems : List Problem := []

instance : Append Plan := ⟨fun a b => ⟨a.edits ++ b.edits, a.problems ++ b.problems⟩⟩

def lineCount (text : String) : Nat :=
  (text.splitOn "\n").length - 1

def readIfExists (file : System.FilePath) : IO (Option String) := do
  if ← file.pathExists then return some (← IO.FS.readFile file) else return none

def sortStrings (xs : List String) : List String :=
  (xs.toArray.qsort (· < ·)).toList

def charsFrom (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

/-- Whether `part` occurs in `whole`. `String.splitOn` takes seconds over every file. -/
def occursIn (part whole : ByteArray) : Bool := Id.run do
  if part.size > whole.size then return false
  for i in [0:whole.size - part.size + 1] do
    let mut same := true
    for j in [0:part.size] do
      if whole[i + j]! != part[j]! then
        same := false
        break
    if same then return true
  return false

/-- `s` with each `old` that does not continue a name replaced by `new`: `new-one.md` in
`D4-new-one.md` stays. -/
def replaceName (s old new : String) : String :=
  if !occursIn old.toUTF8 s.toUTF8 then s
  else match s.splitOn old with
    | [] => s
    | first :: rest => rest.foldl (init := first) fun done part =>
      let continues := done.toList.getLast?.any fun c => c.isAlphanum || c == '-' || c == '_'
      done ++ (if continues then old else new) ++ part

/-- A write that changes nothing is no edit. -/
def writeIfChanged (root : System.FilePath) (path text rule message : String) :
    IO (List Edit) := do
  if (← readIfExists (root / path)) == some text then return []
  else return [⟨path, .write text, rule, message⟩]

def stale : String := "out of date: run `lake exe lanes lint --fix`"

/-- The Markdown files of a directory, sorted by name. -/
def markdownIn (dir : System.FilePath) : IO (List String) := do
  if !(← dir.isDir) then return []
  let names := (← dir.readDir).toList.map (·.fileName)
  return sortStrings (names.filter (·.endsWith ".md"))

/-! ## Line counts of trusted files -/

/-- `", N lines…"` read as `N` and what follows the number. -/
def parseCount (after : String) : Option (Nat × String) := do
  let cs := after.toList
  guard (cs.take 2 == [',', ' '])
  let digits := (cs.drop 2).takeWhile Char.isDigit
  let tail := String.ofList ((cs.drop 2).dropWhile Char.isDigit)
  guard (!digits.isEmpty && tail.startsWith " lines")
  return ((String.ofList digits).toNat!, tail)

def isTrustedSource (path : String) : Bool :=
  path.endsWith ".lean" || path.endsWith ".c"

/-- The `` `path.lean`, N lines `` and `` `path.c`, N lines `` entries of `TRUSTED.md`. -/
def trustedSizes (trusted : String) : List (String × Nat) :=
  let parts := trusted.splitOn "`"
  (parts.zip (parts.drop 1)).filterMap fun (path, after) =>
    if isTrustedSource path then (parseCount after).map fun (n, _) => (path, n) else none

/-- `TRUSTED.md` with each entry's count replaced by `actual path`, where that is known. -/
def rewriteSizes (trusted : String) (actual : String → Option Nat) : String :=
  let parts := trusted.splitOn "`"
  let fixed := (parts.zip ("" :: parts)).map fun (part, path) =>
    if isTrustedSource path then
      match parseCount part, actual path with
      | some (_, tail), some n => s!", {n}{tail}"
      | _, _ => part
    else part
  "`".intercalate fixed

/-- `1587` as `1,587`. -/
def withCommas (n : Nat) : String :=
  let digits := (toString n).toList.reverse
  let groups := (List.range ((digits.length + 2) / 3)).map fun k =>
    String.ofList ((digits.drop (3 * k)).take 3).reverse
  ",".intercalate groups.reverse

/-- Trusted sources written `` `path`, lines `` with no number before `lines`, as a merge
leaves an entry when it drops the count: `trustedSizes` cannot read them, so they would be
left out of the total. -/
def countless (trusted : String) : List String :=
  let parts := trusted.splitOn "`"
  (parts.zip (parts.drop 1)).filterMap fun (path, after) =>
    let rest := (after.toList.drop 1).dropWhile (· == ' ')
    if isTrustedSource path && after.startsWith "," && String.ofList (rest.take 5) == "lines"
    then some path else none

def trustedPlan (root : System.FilePath) : IO Plan := do
  let some trusted ← readIfExists (root / "TRUSTED.md") | return {}
  let mut actual : List (String × Nat) := []
  let mut problems : List Problem := (countless trusted).map fun path =>
    ("TRUSTED.md", 1, "trusted-size", s!"`{path}` is listed with no line count: write `{path}`, N lines")
  for (path, _) in trustedSizes trusted do
    match ← readIfExists (root / path) with
    | some text => actual := (path, lineCount text) :: actual
    | none => problems := ("TRUSTED.md", 1, "trusted-size", s!"`{path}` does not exist") :: problems
  let lookup := fun path => (actual.find? (·.1 == path)).map (·.2)
  let wrong := (trustedSizes trusted).filterMap fun (path, listed) =>
    (lookup path).bind fun n =>
      if n == listed then none else some s!"`{path}` has {n} lines, not {listed}"
  let edits ← writeIfChanged root "TRUSTED.md" (rewriteSizes trusted lookup) "trusted-size"
    s!"{"; ".intercalate wrong}: run `lake exe lanes lint --fix` (rule 5.5)"
  return { edits, problems := problems.reverse }

/-- The trusted files `TRUSTED.md` counts, and their lines as the files have them now. -/
def trustedTotal (root : System.FilePath) : IO (Nat × Nat) := do
  let some trusted ← readIfExists (root / "TRUSTED.md") | return (0, 0)
  let paths := (trustedSizes trusted).map (·.1) |>.eraseDups
  let mut total := 0
  for path in paths do
    if let some text ← readIfExists (root / path) then total := total + lineCount text
  return (paths.length, total)

/-! ## Decisions -/

def decisionsDir : String := "docs/decisions"

structure Decision where
  /-- The file's name in `docs/decisions`. -/
  file : String
  /-- `none` for a decision not numbered yet. -/
  number : Option Nat
  slug : String
  title : String
  /-- The text after the heading line. -/
  body : String

/-- `D12-slug.md` as `(12, slug)`, `new-slug.md` as `(none, slug)`. -/
def parseDecisionName (name : String) : Option (Option Nat × String) := do
  guard (name.endsWith ".md")
  let stem := String.ofList (name.toList.take (name.length - 3))
  if stem.startsWith "new-" then
    return (none, charsFrom stem 4)
  let cs := stem.toList
  guard (cs.head? == some 'D')
  let digits := (cs.drop 1).takeWhile Char.isDigit
  let rest := (cs.drop 1).dropWhile Char.isDigit
  guard (!digits.isEmpty && rest.head? == some '-')
  return (some (String.ofList digits).toNat!, String.ofList (rest.drop 1))

/-- `# D12. Title` as `(some 12, Title)`, `# D?. Title` as `(none, Title)`. -/
def parseHeading (line : String) : Option (Option Nat × String) := do
  guard (line.startsWith "# D")
  let cs := (charsFrom line 3).toList
  if cs.take 3 == ['?', '.', ' '] then return (none, String.ofList (cs.drop 3))
  let digits := cs.takeWhile Char.isDigit
  let rest := cs.dropWhile Char.isDigit
  guard (!digits.isEmpty && rest.take 2 == ['.', ' '])
  return (some (String.ofList digits).toNat!, String.ofList (rest.drop 2))

/-- The text after `Status: ` on the first line of the body that is not blank: `Accepted`,
`Superseded by D18`, or `Partly superseded by D37 (the router)`. -/
def Decision.status? (d : Decision) : Option String := do
  let line ← (d.body.splitOn "\n").find? fun l => !l.trimAscii.isEmpty
  guard (line.startsWith "Status: ")
  let status := charsFrom line 8
  guard (["Accepted", "Superseded by ", "Partly superseded by "].any fun p => status.startsWith p)
  return status

/-- Current unless wholly superseded. -/
def Decision.current (d : Decision) : Bool :=
  !(d.status?.any (·.startsWith "Superseded"))

def readDecisions (root : System.FilePath) : IO (List Decision × List Problem) := do
  let mut decisions : List Decision := []
  let mut problems : List Problem := []
  for name in ← markdownIn (root / decisionsDir) do
    if name == "README.md" then continue
    let path := s!"{decisionsDir}/{name}"
    let text ← IO.FS.readFile (root / path)
    let (first, body) := match text.splitOn "\n" with
      | first :: rest => (first, "\n".intercalate rest)
      | [] => ("", "")
    match parseDecisionName name, parseHeading first with
    | some (number, slug), some (heading, title) =>
      if heading != number then
        problems := (path, 1, "decisions",
          s!"the heading's number does not match the file's name ({name})") :: problems
      let d : Decision := ⟨name, number, slug, title, body⟩
      if d.status?.isNone then
        problems := (path, 3, "decisions", "the line after the title is `Status: Accepted`, "
          ++ "`Status: Superseded by Dn` or `Status: Partly superseded by Dn (the part)`") :: problems
      decisions := d :: decisions
    | none, _ =>
      problems := (path, 1, "decisions", "a decision is `Dn-<slug>.md`, or `new-<slug>.md` "
        ++ "before it has a number") :: problems
    | some _, none =>
      problems := (path, 1, "decisions", "the first line is `# Dn. Title`, or `# D?. Title` "
        ++ "before the decision has a number") :: problems
  return (decisions.reverse, problems.reverse)

def indexLine (d : Decision) (n : Nat) : String :=
  let link := s!"- [D{n}. {d.title}]({d.file})"
  match d.status? with
  | some "Accepted" | none => link
  | some status => match status.toList with
    | c :: cs => s!"{link}: {String.ofList (c.toLower :: cs)}"
    | [] => link

/-- Current decisions first, then those superseded. Each list is sorted by slug, not by number:
a new decision lands at its own place in the list, not after the last line, where every other
new one would land too. -/
def indexText (readme : Option String) (decisions : List Decision) : String :=
  let numbered := decisions.filterMap fun d => d.number.map (d, ·)
  let sorted := fun (ds : List (Decision × Nat)) => (ds.toArray.qsort fun (a, m) (b, n) =>
    a.slug < b.slug || (a.slug == b.slug && m < n)).toList
  let lines := fun ds => "\n".intercalate ((sorted ds).map fun (d, n) => indexLine d n)
  let (current, superseded) := numbered.partition (·.1.current)
  let index := "### Current\n\n" ++ lines current
    ++ (if superseded.isEmpty then "" else "\n\n### Superseded\n\n" ++ lines superseded)
  let preamble := match readme with
    | none => "# Decisions\n\n## Index\n"
    | some text => match text.splitOn "\n## Index\n" with
      | before :: _ :: _ => before ++ "\n## Index\n"
      | _ => text.trimAsciiEnd.toString ++ "\n\n## Index\n"
  preamble ++ "\n" ++ index ++ "\n"

/-- The `.lean` and `.md` files outside `.lake`, `.git` and other hidden directories. -/
def textFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let files ← root.walkDir fun dir => return !(dir.fileName.getD "").startsWith "."
  return files.filter fun f => f.extension == some "lean" || f.extension == some "md"

/-- Number the decisions that have none, after the highest number, in the order of their
names; rewrite the references to their paths. -/
def numberPlan (root : System.FilePath) (decisions : List Decision) : IO (List Edit) := do
  let fresh := decisions.filter (·.number.isNone)
  if fresh.isEmpty then return []
  let next := (decisions.filterMap (·.number)).foldl max 0 + 1
  let named := fresh.zipIdx.map fun (d, k) => (d, next + k, s!"D{next + k}-{d.slug}.md")
  let mut edits : List Edit := []
  let unnumbered := "has no number: run `lake exe lanes lint --fix --main` on the main branch"
  let refer := fun text => named.foldl (fun t (d, _, name) => replaceName t d.file name) text
  for (d, n, name) in named do
    edits := edits ++ [⟨s!"{decisionsDir}/{d.file}",
      .move s!"{decisionsDir}/{name}" (refer s!"# D{n}. {d.title}\n{d.body}"), "decisions",
      unnumbered⟩]
  let skip := fresh.map fun d => s!"{decisionsDir}/{d.file}"
  for file in ← textFiles root do
    let path := (file.toString.dropPrefix (root.toString ++ "/")).toString
    if skip.contains path then continue
    let text ← IO.FS.readFile file
    let fixed := refer text
    if fixed != text then
      edits := edits ++ [⟨path, .write fixed, "decisions",
        "refers to a decision that has no number yet"⟩]
  return edits

/-- With `main`, decisions without a number are numbered; elsewhere they wait. -/
def decisionsPlan (root : System.FilePath) (main : Bool) : IO Plan := do
  if !(← (root / decisionsDir).isDir) then return {}
  let (decisions, problems) ← readDecisions root
  let mut duplicates : List Problem := []
  for d in decisions do
    if let some n := d.number then
      if (decisions.filter (·.number == some n)).length > 1 then
        duplicates := (s!"{decisionsDir}/{d.file}", 1, "decisions",
          s!"D{n} is the number of another decision too") :: duplicates
  let readmePath := s!"{decisionsDir}/README.md"
  let readme ← readIfExists (root / readmePath)
  let index ← writeIfChanged root readmePath (indexText readme decisions) "decisions"
    s!"the index is {stale}"
  let numbering ← if main then numberPlan root decisions else pure []
  return { edits := index ++ numbering, problems := problems ++ duplicates.reverse }

/-! ## Applying a plan -/

def plan (root : System.FilePath) (main : Bool) : IO Plan := do
  return (← trustedPlan root) ++ (← decisionsPlan root main)

def Edit.describe (e : Edit) : String :=
  match e.change with
  | .write _ => s!"{e.path}: rewritten"
  | .move new _ => s!"{e.path}: renamed to {new}"

def apply (root : System.FilePath) (e : Edit) : IO Unit :=
  match e.change with
  | .write text => IO.FS.writeFile (root / e.path) text
  | .move new text => do
    IO.FS.writeFile (root / new) text
    IO.FS.removeFile (root / e.path)

/-- Apply plans until one has no edits, and return the edits made. Each round reads what the
last one wrote: a decision numbered in one round is in the index of the next. -/
def fix (root : System.FilePath) (main : Bool) : IO (List Edit) := do
  let mut done : List Edit := []
  for _ in [0:4] do
    let p ← plan root main
    if p.edits.isEmpty then return done
    for e in p.edits do apply root e
    done := done ++ p.edits.filter fun e => !done.any (·.describe == e.describe)
  throw (IO.userError "lanes lint --fix: the generated files did not settle")

end Lanes.Cli.Generated
