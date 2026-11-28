/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# The inventory

Every public definition of `Lanes` and `LanesCli` with one status and its evidence, read from the
built modules and printed by `lanes inventory`; no committed file holds it. The rules are those
of `docs/decisions/D47-the-inventory-is-computed.md`. This module imports `Lean`, so only the
`lanesInventory` executable links it; `lanes` starts that with `lake exe`.
-/

namespace Lanes.Cli.Inventory

open Lean

inductive Status where
  | proved
  /-- A bound function whose theorems are about its Lean body: the C runs, and is trusted. -/
  | reference
  | trusted | checked | tested | spec | none
  deriving DecidableEq, Inhabited

def Status.label : Status → String
  | .proved => "proved" | .reference => "proved of its reference, C trusted"
  | .trusted => "trusted" | .checked => "checked"
  | .tested => "tested" | .spec => "spec" | .none => "none"

def Status.all : List Status :=
  [.proved, .reference, .trusted, .checked, .tested, .spec, .none]

structure Entry where
  name : Name
  module : Name
  line : Nat
  status : Status
  evidence : String

def noneFile : String := "docs/inventory-none.md"

/-! ## Reading the project -/

def sortStrings (xs : Array String) : Array String := xs.qsort (· < ·)

def moduleOfPath (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun n s => Name.str n s) .anonymous

def pathOfModule (m : Name) : String :=
  "/".intercalate (m.components.map toString) ++ ".lean"

/-- The modules of a directory's `.lean` files. -/
def modulesIn (root : System.FilePath) (dir : String) : IO (Array Name) := do
  if !(← (root / dir).isDir) then return #[]
  let files ← (root / dir).walkDir
  let rel := files.filterMap fun f =>
    if f.extension == some "lean" then
      some (moduleOfPath ((f.toString.dropPrefix (root.toString ++ "/")).toString))
    else none
  return rel.qsort (·.toString < ·.toString)

/-- What the inventory imports: the roots of the library, the test kit, `lanes`, this module and
the docstring coverage, every module of `Tests`, the fixtures included. The other executables'
`main` modules are left out: they would define `main` twice, and they only call what other
modules define. -/
def imports (root : System.FilePath) : IO (Array Name) := do
  let tests ← modulesIn root "Tests"
  let all := #[`Lanes, `Lanes.Semantics, `Lanes.Testing, `LanesCli.Main, `LanesCli.Docstrings]
    ++ tests
  return all.filter fun m => !(m.getString!.endsWith "Main") || m == `LanesCli.Main

/-- The theorems with an axiom gate: every `#print axioms` in `Tests/Axioms/`. -/
def gates (root : System.FilePath) : IO NameSet := do
  let dir := root / "Tests" / "Axioms"
  if !(← dir.isDir) then return {}
  let mut out : NameSet := {}
  for f in ← dir.walkDir do
    if f.extension != some "lean" then continue
    for line in (← IO.FS.readFile f).splitOn "\n" do
      if let some rest := (line.splitOn "#print axioms ")[1]? then
        out := out.insert rest.trimAscii.toString.toName
  return out

/-- The rows of `TRUSTED.md`'s tables: each `.lean` file named in the second column, with the
row's first column. -/
def trustedRows (root : System.FilePath) : IO (List (String × String)) := do
  let file := root / "TRUSTED.md"
  if !(← file.pathExists) then return []
  let mut out := []
  for line in (← IO.FS.readFile file).splitOn "\n" do
    let cells := line.splitOn " | "
    if !line.startsWith "| " || cells.length < 3 then continue
    let what := (cells[0]!.drop 2).toString
    let parts := cells[1]!.splitOn "`"
    for (part, k) in parts.zipIdx do
      if k % 2 == 1 && part.endsWith ".lean" then out := (part, what) :: out
  return out.reverse

/-! ## Reading the declarations -/

/-- The declaration a generated one belongs to: `f.match_1`, `f.proof_2`, `f._unary` and
`f.eq_1` are `f`'s. -/
def owner : Name → Name
  | .str p s =>
    if s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"
    then owner p else .str p s
  | .num p _ => owner p
  | .anonymous => .anonymous

/-- What the body of a type is, after its binders: a proposition, a type, or a value whose type
has this head constant. -/
inductive Shape where
  | prop | type | value (head : Option Name)

def shapeOf (type : Expr) : MetaM Shape :=
  Meta.forallTelescopeReducing type fun _ body => do
    let body ← Meta.whnfD body
    match body with
    | .sort .zero => return .prop
    | .sort _ => return .type
    | _ => return .value body.getAppFn.constName?

/-- Types whose values carry their specification as fields or constructor arguments. -/
def specTypes : List Name :=
  [``Decidable, `Lanes.Codec, `Lanes.Codable, `Lanes.Enum]

/-- The types a model check's result has. -/
def reportTypes : List Name := [`Lanes.Check.Report, `Lanes.Check.FuzzReport]

def libraryRoots : List Name := [`Lanes, `LanesCli]

def isLibrary (m : Name) : Bool := libraryRoots.contains m.getRoot

/-- What the inventory knows of a project. -/
structure Facts where
  env : Environment
  moduleOf : NameMap Name := {}
  /-- Of each library definition the inventory may list, its shape. -/
  listed : Array Name := #[]
  shape : NameMap Shape := {}
  /-- Of every definition, by owner, the constants its value uses. -/
  uses : NameMap NameSet := {}
  /-- Constants a statement mentions: of a theorem, a constructor, or a predicate. -/
  stated : NameSet := {}
  /-- Of each gated theorem, the constants of its statement. -/
  gated : NameMap NameSet := {}
  /-- Model-checking functions. -/
  runners : NameSet := {}
  /-- Definitions Lean unfolds at reducible transparency, instances aside: the `abbrev`s. -/
  reducible : NameSet := {}

def ranges (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .server) env n <|> declRangeExt.find? (level := .exported) env n

/-- Whether a declaration's position is in a `deriving` clause, as it is for what `deriving`
writes. -/
def inDeriving (lines : Array String) (pos : Position) : Bool :=
  let line := lines[pos.line - 1]?.getD ""
  let before := (String.ofList (line.toList.take pos.column)).trimAscii.toString
  let previous := (lines[pos.line - 2]?.getD "").trimAscii.toString
  pos.column > 0 && (before.startsWith "deriving"
    || (previous.startsWith "deriving" && previous.endsWith ","))

def generatedParsers : List Name := [``ParserDescr, ``TrailingParserDescr, ``Parser.Category]

/-- Whether `n` is bound: `@[extern]`, so that compiled code calls C, with a Lean body beside it,
its reference (rule 2.7). Lean reasons about the body, so a theorem of it is a theorem of the
reference, not of the C. -/
def isBound (env : Environment) (n : Name) : Bool :=
  isExtern env n && env.find? n matches some (.defnInfo _)

/-- Whether `n` is a theorem, or the private name Lean files a theorem's matchers under. What
those define is part of a proof: it neither runs nor states. -/
def ofTheorem (env : Environment) (n : Name) : Bool :=
  [n, (privateToUserName? n).getD n].any fun n => env.find? n matches some (.thmInfo _)

def readFacts (root : System.FilePath) (env : Environment) : IO Facts := do
  let gated ← gates root
  let mut facts : Facts := { env }
  let mut sources : NameMap (Array String) := {}
  let mut shapes : Array (Name × Expr) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    let r := m.getRoot
    if !(r == `Lanes || r == `LanesCli || r == `Tests) then continue
    for name in env.header.moduleData[i]!.constNames do
      let some ci := env.find? name | continue
      facts := { facts with moduleOf := facts.moduleOf.insert name m }
      match ci with
      | .thmInfo t =>
        let consts := t.type.getUsedConstants
        facts := { facts with stated := consts.foldl (·.insert ·) facts.stated }
        if gated.contains name then
          facts := { facts with gated := facts.gated.insert name (consts.foldl (·.insert ·) {}) }
      | .ctorInfo c =>
        facts := { facts with stated := c.type.getUsedConstants.foldl (·.insert ·) facts.stated }
      | .defnInfo _ | .opaqueInfo _ =>
        let o := owner name
        if ofTheorem env o then continue
        let used := (ci.value?.map (·.getUsedConstants)).getD #[]
        facts := { facts with
          uses := facts.uses.insert o (used.foldl (·.insert ·) (facts.uses.getD o {})) }
        if o == name then shapes := shapes.push (name, ci.type)
        if o == name && getReducibilityStatusCore env name == .reducible
            && !Meta.isInstanceCore env name then
          facts := { facts with reducible := facts.reducible.insert name }
        if !isLibrary m || name.isInternalDetail || isPrivateName name then continue
        if isAuxRecursor env name || isNoConfusion env name || Meta.isMatcherCore env name
          || env.isProjectionFn name then continue
        if generatedParsers.any (ci.type.isConstOf ·) then continue
        let some rs := ranges env name | continue
        let lines ← match sources.find? m with
          | some ls => pure ls
          | none => do
            let file := root / pathOfModule m
            let text ← if ← file.pathExists then IO.FS.readFile file else pure ""
            let ls := (text.splitOn "\n").toArray
            sources := sources.insert m ls
            pure ls
        if inDeriving lines rs.range.pos then continue
        if (ranges env name.getPrefix).any (inDeriving lines ·.range.pos) then continue
        facts := { facts with listed := facts.listed.push name }
      | _ => pure ()
  let ctx : Core.Context := { fileName := "<inventory>", fileMap := default, maxHeartbeats := 0 }
  let ((shape, runners), _) ← (do
      let mut shape : NameMap Shape := {}
      let mut runners : NameSet := {}
      for (name, type) in shapes do
        let s ← try shapeOf type catch _ => pure (.value none)
        shape := shape.insert name s
        if let .value (some h) := s then
          if reportTypes.contains h then runners := runners.insert name
      return (shape, runners) : MetaM _).run' {} |>.toIO ctx { env }
  return { facts with shape, runners }

/-! ## Statuses -/

def isProp (f : Facts) (n : Name) : Bool := f.shape.find? n matches some .prop

def isType (f : Facts) (n : Name) : Bool := f.shape.find? n matches some .type

/-- The constants each one's value uses, the other way round. -/
def usersOf (f : Facts) : NameMap NameSet := Id.run do
  let mut users : NameMap NameSet := {}
  for (u, used) in f.uses do
    for c in used do
      if c != u then users := users.insert c ((users.getD c {}).insert u)
  return users

/-- Definitions used only to state things: a theorem or a predicate uses them, and no
definition that runs does, a test included. The largest such set, then only what a statement
reaches. -/
def specs (f : Facts) : NameSet := Id.run do
  let users := usersOf f
  let candidates := f.uses.foldl (init := ({} : NameSet)) fun s n _ =>
    if f.shape.find? n matches some (.value _) && (f.stated.contains n || users.contains n)
    then s.insert n else s
  let mut set := candidates
  let mut changed := true
  let mut fuel := candidates.size + 1
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for n in set do
      let us := users.getD n {}
      let runs := us.any fun u => !isProp f u && !set.contains u
      let statedBy := f.stated.contains n || us.any fun u => isProp f u || set.contains u
      if runs || !statedBy then
        set := set.erase n
        changed := true
  let mut reached : NameSet := {}
  let mut todo := set.toList.filter fun n =>
    f.stated.contains n || (users.getD n {}).any (isProp f)
  let mut steps := f.uses.size + set.size + 1
  while steps > 0 do
    steps := steps - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if reached.contains n then continue
      reached := reached.insert n
      for c in f.uses.getD n {} do
        if set.contains c && !reached.contains c then todo := c :: todo
  return reached

/-- What naming `start` covers: `start`, and what its value runs in its own module, through
such definitions, and anything a spec's value uses. -/
def covers (f : Facts) (spec : NameSet) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [start]
  let mut fuel := f.uses.size + 2
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let here := f.moduleOf.find? n
      let through := spec.contains n
      for c in f.uses.getD n {} do
        let c := owner c
        if !seen.contains c && (through || f.moduleOf.find? c == here) then todo := c :: todo
  return seen

/-- The constants of a statement, with each predicate abbreviation in it read as its body, in
whatever module it is: Lean reads it so, and it is the statement written shorter, not an entry
point of its module. -/
def statement (f : Facts) (consts : NameSet) : NameSet := Id.run do
  let unfolds := fun n => f.reducible.contains n && isProp f n
  let mut out := consts
  let mut todo := consts.toList.filter unfolds
  let mut fuel := f.reducible.size + consts.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      for c in f.uses.getD n {} do
        if !out.contains c then
          out := out.insert c
          if unfolds c then todo := c :: todo
  return out

/-- Of each constant, the gated theorems that state it, each with the constant of its
statement it is reached through, if it is not there itself. -/
def provedBy (f : Facts) (spec : NameSet) : NameMap (Array (Name × Option Name)) := Id.run do
  let mut out : NameMap (Array (Name × Option Name)) := {}
  for (thm, consts) in f.gated do
    let mut credit : NameMap (Option Name) := {}
    for c in statement f consts do
      if isProp f c then
        credit := credit.insert c none
        continue
      for x in covers f spec c do
        if x == c then credit := credit.insert x none
        else if !credit.contains x then credit := credit.insert x (some c)
    for (x, via) in credit do
      out := out.insert x ((out.getD x #[]).push (thm, via))
  return out

def isOutside (f : Facts) (n : Name) : Bool :=
  (f.moduleOf.find? n).any fun m => m.getRoot == `Tests

/-- The library constants the declarations reach through declarations of `Tests`, with no
library declaration between. -/
def reach (f : Facts) (start : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo := start
  let mut fuel := f.uses.size + start.length + 1
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      for c in f.uses.getD n {} do
        if (f.moduleOf.find? c).any isLibrary then out := out.insert (owner c)
        else if isOutside f c then todo := owner c :: todo
  return out

/-- Of each library constant, the test modules that cover it, and those whose checks do. -/
def exercised (f : Facts) (spec : NameSet) : NameMap (Array Name) × NameMap (Array Name) :=
  Id.run do
  let mut byModule : NameMap (Array Name) := {}
  let mut checksBy : NameMap (Array Name) := {}
  for (n, used) in f.uses do
    let some m := f.moduleOf.find? n | continue
    if m.getRoot != `Tests then continue
    byModule := byModule.insert m ((byModule.getD m #[]).push n)
    if used.any f.runners.contains then
      checksBy := checksBy.insert m ((checksBy.getD m #[]).push n)
  let credit (from_ : NameMap (Array Name)) : NameMap (Array Name) :=
    from_.foldl (init := {}) fun acc m decls =>
      let covered := (reach f decls.toList).foldl (init := ({} : NameSet)) fun s c =>
        (covers f spec c).foldl (·.insert ·) s
      covered.foldl (init := acc) fun acc c => acc.insert c ((acc.getD c #[]).push m)
  return (credit byModule, credit checksBy)

/-- A name as the documents write it, without the leading `Lanes.`. -/
def display (n : Name) : String :=
  match n.components with
  | `Lanes :: rest@(_ :: _) => toString (rest.foldl Name.append .anonymous)
  | _ => toString n

/-- The first `most` names in order, then "and others": with a count, every new test of a name
would change its line. -/
def listOf (names : Array String) (most : Nat := 3) : String :=
  let names := sortStrings names
  let shown := ", ".intercalate ((names.toList.take most).map fun s => s!"`{s}`")
  if names.size > most then s!"{shown} and others" else shown

def entries (root : System.FilePath) (f : Facts) : IO (Array Entry) := do
  let trusted ← trustedRows root
  let spec := specs f
  let proved := provedBy f spec
  let (tested, checked) := exercised f spec
  let mut out := #[]
  for name in f.listed do
    if isType f name then continue
    let module := (f.moduleOf.find? name).getD .anonymous
    let line := ((ranges f.env name).map (·.range.pos.line)).getD 0
    let path := pathOfModule module
    let shape := f.shape.find? name
    let tests := fun (m : NameMap (Array Name)) => (m.getD name #[]).map fun t => pathOfModule t
    let byType := match shape with
      | some (.value (some h)) => if specTypes.contains h then some h else none
      | _ => none
    let ts := proved.getD name #[]
    let direct := ts.filterMap fun (t, via) => if via.isNone then some (display t) else none
    let through := (ts.filterMap (·.2)).map display
    let (status, evidence) :=
      if shape matches some .prop then (Status.spec, "a predicate")
      else if spec.contains name then (.spec, "used only in statements")
      else if !direct.isEmpty then (.proved, listOf direct)
      else if let some h := byType then (.proved, s!"its type, `{display h}`")
      else if !ts.isEmpty then
        (.proved, s!"through {listOf through.toList.eraseDups.toArray 2}: "
          ++ listOf (ts.map (display ·.1)).toList.eraseDups.toArray 2)
      else (.none, "")
    let row := trusted.find? (·.1 == path)
    let (status, evidence) :=
      if status == .proved && isBound f.env name then
        (.reference, evidence ++ (row.map fun (_, what) => s!"; the C: TRUSTED.md: {what}").getD "")
      else (status, evidence)
    let (status, evidence) :=
      if status != .none then (status, evidence)
      else if let some (_, what) := row then (.trusted, s!"TRUSTED.md: {what}")
      else if !(tests checked).isEmpty then (.checked, listOf (tests checked))
      else if !(tests tested).isEmpty then (.tested, listOf (tests tested))
      else (.none, "")
    out := out.push { name, module, line, status, evidence }
  return out.qsort fun a b =>
    a.module.toString < b.module.toString
      || (a.module == b.module && (a.line < b.line || (a.line == b.line && display a.name < display b.name)))

/-! ## The document -/

/-- `Lanes.Runtime.Kernel` is in `Lanes/Runtime`; `LanesCli.Lint` in `LanesCli`. -/
def area (m : Name) : String :=
  match m.components with
  | `Lanes :: a :: _ :: _ => s!"Lanes/{a}"
  | `Lanes :: _ => "Lanes"
  | r :: _ => toString r
  | [] => ""

def cell (s : String) : String := s.replace "|" "\\|"

/-- The count of each status by area. It is printed (`lanes stats`), not written in the
inventory: every new definition would change its last line. -/
def summary (es : Array Entry) : String := Id.run do
  let areas := sortStrings ((es.map (area ·.module)).toList.eraseDups.toArray)
  let header := "| Area | Definitions | " ++ " | ".intercalate (Status.all.map (·.label)) ++ " |\n"
    ++ "| --- | ---: | " ++ " | ".intercalate (Status.all.map fun _ => "---:") ++ " |\n"
  let row := fun (label : String) (xs : Array Entry) =>
    s!"| {label} | {xs.size} | "
      ++ " | ".intercalate (Status.all.map fun s => toString (xs.filter (·.status == s)).size)
      ++ " |\n"
  let mut out := header
  for a in areas do
    out := out ++ row s!"`{a}`" (es.filter (area ·.module == a))
  out := out ++ row "All" es
  return out

def render (es : Array Entry) : String := Id.run do
  let mut out := "# Inventory\n\n"
    ++ "Every public definition of `Lanes` and `LanesCli`, with its status and the evidence for it.\n"
    ++ "Printed from the built modules by `lake exe lanes inventory` (`LanesCli/Inventory.lean`).\n"
    ++ "What each status means, and what is not listed, is in\n"
    ++ "`docs/decisions/D47-the-inventory-is-computed.md`. The definitions of `Lanes/` with status\n"
    ++ "none are on `docs/inventory-none.md`, which only shrinks. `lake exe lanes stats` counts\n"
    ++ "them by area.\n"
  let modules := (es.map (·.module)).toList.eraseDups
  for m in modules do
    out := out ++ s!"\n## `{pathOfModule m}`\n\n| Definition | Status | Evidence |\n| --- | --- | --- |\n"
    for e in es.filter (·.module == m) do
      out := out ++ s!"| `{cell (display e.name)}` | {e.status.label} | {cell e.evidence} |\n"
  return out

/-! ## The check -/

/-- The entries of `docs/inventory-none.md`: each `` - `name` `` with its line and whether a
section heading, its reason, comes before it. -/
def allowed (text : String) : Array (String × Nat × Bool) := Id.run do
  let mut out := #[]
  let mut inSection := false
  for (line, k) in (text.splitOn "\n").zipIdx do
    if line.startsWith "## " then inSection := !(line.drop 3).trimAscii.isEmpty
    else if line.startsWith "- `" then
      let name := ((line.drop 3).toString.splitOn "`")[0]!
      out := out.push (name, k + 1, inSection)
  return out

abbrev Finding := String × Nat × String × String

def check (root : System.FilePath) (es : Array Entry) : IO (Array Finding) := do
  let mut findings := #[]
  let text ← if ← (root / noneFile).pathExists then IO.FS.readFile (root / noneFile) else pure ""
  let allow := allowed text
  let none := es.filter fun e => e.status == .none && e.module.getRoot == `Lanes
  for e in none do
    if !allow.any (·.1 == display e.name) then
      findings := findings.push (pathOfModule e.module, e.line, "inventory-none",
        s!"`{display e.name}` has no evidence: prove it, test it, name its file in TRUSTED.md, "
          ++ s!"or add it to {noneFile} under a heading that says why")
  for (name, line, reasoned) in allow do
    if !none.any (display ·.name == name) then
      findings := findings.push (noneFile, line, "inventory-none",
        s!"`{name}` is not a definition of `Lanes/` without evidence: remove it")
    else if !reasoned then
      findings := findings.push (noneFile, line, "inventory-none",
        s!"`{name}` is under no heading: the heading says why it is here")
  return findings

def load (root : System.FilePath) : IO (Array Entry) := do
  initSearchPath (← findSysroot)
  let env ← importModules ((← imports root).map ({ module := · })) {}
  entries root (← readFacts root env)

/-- `lanesInventory [--check | --summary | --list <status>]`: print the inventory, check the
definitions without evidence against `docs/inventory-none.md`, print the counts by area, or
print the library's definitions of a status. -/
def run (args : List String) : IO UInt32 := do
  let root : System.FilePath := "."
  let es ← load root
  match args with
  | ["--summary"] =>
    IO.print (summary es)
    return 0
  | ["--list", s] =>
    for e in es do
      if e.status.label == s && e.module.getRoot == `Lanes then
        IO.println s!"{pathOfModule e.module}:{e.line}\t{display e.name}\t{e.evidence}"
    return 0
  | [] =>
    IO.print (render es)
    return 0
  | _ =>
  let findings ← check root es
  for (file, line, rule, message) in findings do
    IO.println s!"{file}:{line}: [{rule}] {message}"
  return if findings.isEmpty then 0 else 1

end Lanes.Cli.Inventory
