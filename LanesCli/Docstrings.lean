/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Inventory

/-!
# Docstring coverage

Which public declarations of `import Lanes` have a docstring, by module, read from the built
modules: `lanes docstrings`. A declaration is counted when the API docs (`docs/api/`) give it an
entry of its own: not a constructor, a field, a recursor, a matcher, a private or internal name,
nor what a `deriving` clause writes. It reports and fails nothing: AGENTS.md says a declaration
gets a docstring only when its name and type do not say what it is, and no count can judge that.
-/

namespace Lanes.Cli.Docstrings

open Lean Lanes.Cli.Inventory

inductive Kind where
  | type | definition | «theorem» | «instance»
  deriving DecidableEq, Inhabited

def Kind.label : Kind → String
  | .type => "type" | .definition => "definition" | .theorem => "theorem" | .instance => "instance"

def Kind.all : List Kind := [.type, .definition, .theorem, .instance]

structure Decl where
  name : Name
  module : Name
  line : Nat
  kind : Kind
  documented : Bool

/-- The instances the modules declare, from the entries they export: `Meta.isInstanceCore` reads
the extension's state, which `importModules` builds only when it runs the extensions'
initializers, and that takes the interpreter. -/
def instances (env : Environment) : NameSet := Id.run do
  let mut out : NameSet := {}
  for i in [0:env.header.moduleNames.size] do
    for level in [OLeanLevel.exported, .server] do
      for e in Meta.instanceExtension.ext.getModuleEntries env i (level := level) do
        let entry := match e with | .global x => x | .scoped _ x => x
        if let some n := entry.globalName? then out := out.insert n
  return out

def kindOf (insts : NameSet) (name : Name) : ConstantInfo → Option Kind
  | .inductInfo _ => some .type
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => none
  | .thmInfo _ => some (if insts.contains name then .instance else .theorem)
  | _ => some (if insts.contains name then .instance else .definition)

/-- Whether the API docs give `name` an entry: what doc-gen4 leaves out, and what Lean or a
`deriving` clause writes, is not counted. -/
def shown (env : Environment) (lines : Array String) (name : Name) (ci : ConstantInfo) : Bool :=
  !(name.isInternal || name.isInternalDetail || isPrivateName name || owner name != name
    || isAuxRecursor env name || isNoConfusion env name || isRecCore env name
    || Meta.isMatcherCore env name || env.isProjectionFn name
    || generatedParsers.any (ci.type.isConstOf ·))
  && match ranges env name with
    | none => false
    | some rs => !inDeriving lines rs.range.pos
        && !(ranges env name.getPrefix).any (inDeriving lines ·.range.pos)

def read (root : System.FilePath) (env : Environment) : IO (Array Decl) := do
  let insts := instances env
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m.getRoot != `Lanes then continue
    let file := root / pathOfModule m
    let lines := ((← if ← file.pathExists then IO.FS.readFile file else pure "").splitOn "\n").toArray
    for name in env.header.moduleData[i]!.constNames do
      let some ci := env.find? name | continue
      let some kind := kindOf insts name ci | continue
      if !shown env lines name ci then continue
      let line := ((ranges env name).map (·.range.pos.line)).getD 0
      let documented := (← findInternalDocString? env name).isSome
      out := out.push { name, module := m, line, kind, documented }
  return out.qsort fun a b =>
    a.module.toString < b.module.toString || (a.module == b.module && a.line < b.line)

def ratio (ds : Array Decl) (k : Kind) : String :=
  let of := ds.filter (·.kind == k)
  s!"{(of.filter (·.documented)).size}/{of.size}"

def row (label : String) (ds : Array Decl) : String :=
  let documented := (ds.filter (·.documented)).size
  s!"| {label} | {documented}/{ds.size} | " ++ " | ".intercalate (Kind.all.map (ratio ds)) ++ " |"

/-- The table: of each module, then each area, then all, the declarations with a docstring out
of those counted, in all and of each kind. -/
def table (ds : Array Decl) : String := Id.run do
  let header := "| Module | All | " ++ " | ".intercalate (Kind.all.map (·.label ++ "s")) ++ " |\n"
    ++ "| --- | ---: | " ++ " | ".intercalate (Kind.all.map fun _ => "---:") ++ " |\n"
  let modules := (ds.map (·.module)).toList.eraseDups
  let areas := sortStrings ((ds.map (area ·.module)).toList.eraseDups.toArray)
  let mut out := header
  for m in modules do
    out := out ++ row s!"`{display m}`" (ds.filter (·.module == m)) ++ "\n"
  for a in areas do
    out := out ++ row s!"`{a}/`" (ds.filter (area ·.module == a)) ++ "\n"
  return out ++ row "All" ds ++ "\n"

/-- `lanes docstrings [--list]`: the table, or each declaration without a docstring, with its
place and its kind. -/
def run (root : System.FilePath) (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Lanes }] {}
  let ds ← read root env
  if args == ["--list"] then
    for d in ds do
      if !d.documented then
        IO.println s!"{pathOfModule d.module}:{d.line}\t{d.kind.label}\t{display d.name}"
    return 0
  IO.print (table ds)
  return 0

end Lanes.Cli.Docstrings
