/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The layers of Lanes

Lanes is built in layers, each of which works without the ones above it
(`docs/decisions/D99-layered-packages.md`): the semantics and the checker (`model`); actors
(`actors`), with the standard library beside them (`std`); a runtime; the web; the umbrella
`Lanes`, which imports them all and is the core; and the services (`Lanes/Services/`, D110),
which may import the core, which never imports them. Each module of `Lanes/` belongs to
one of these packages, read from `homes` by the longest prefix of its path, and may import only
the modules of its own package and of the packages it requires, directly or below
(`Package.requires`). `lanes lint` reports any other import of a module of Lanes (rule
`layering`, rule 1.6 of `AGENTS.md`): it would make the lower package fail to build alone.

A file sits under the directory of its concern today, and `homes` names, by its path, each file
whose package is not its directory's. They move into their packages' directories later, with no
change to this table's packages. `scripts/layers.py` reads this file to plan those moves.

-/

namespace Lanes.Cli.Layers

inductive Package where
  | model | actors | std | runtime | web | umbrella | services
  deriving DecidableEq, Repr, Inhabited

def Package.all : List Package :=
  [.model, .actors, .std, .runtime, .web, .umbrella, .services]

def Package.name : Package → String
  | .model => "model"
  | .actors => "actors"
  | .std => "std"
  | .runtime => "runtime"
  | .web => "web"
  | .umbrella => "umbrella"
  | .services => "services"

/-- The packages each package requires directly. -/
def Package.requires : Package → List Package
  | .model => []
  | .actors => [.model]
  | .std => [.model]
  | .runtime => [.actors]
  | .web => [.runtime, .std]
  | .umbrella => [.web]
  | .services => [.umbrella]

/-- The packages `p` requires, directly or below. A chain of requirements is shorter than the
list of packages, so that many rounds reach all of them. -/
def Package.below (p : Package) : List Package := Id.run do
  let mut found := p.requires
  for _ in Package.all do
    for q in found do
      for r in q.requires do
        unless found.contains r do found := found ++ [r]
  return found

/-- Whether a module of `p` may import a module of `q`. -/
def Package.mayImport (p q : Package) : Bool :=
  p == q || p.below.contains q

/-- Where each module of `Lanes/` belongs: a prefix of its path, and its package. The longest
prefix that a path starts with gives the package. -/
def homes : List (String × Package) := [
  ("Lanes/Data/", .model),
  ("Lanes/Proof/List/", .model),
  ("Lanes/Proof/List.lean", .model),
  ("Lanes/Proof/Utf8.lean", .model),
  ("Lanes/Proof/ByteArray.lean", .model),
  ("Lanes/Proof/HashMap.lean", .model),
  ("Lanes/Check/Search.lean", .model),
  ("Lanes/Check/SearchSound.lean", .model),
  ("Lanes/Check/Fingerprint.lean", .model),
  ("Lanes/Semantics/Refinement.lean", .model),
  ("Lanes/Semantics/Lts.lean", .model),
  ("Lanes/Semantics/Seq.lean", .model),
  ("Lanes/Core/", .actors),
  ("Lanes/Proof/", .actors),
  ("Lanes/Check/", .actors),
  ("Lanes/Behaviours/", .actors),
  ("Lanes/Outside/", .actors),
  ("Lanes/Outside/FileSystem/", .model),
  ("Lanes/Db/", .actors),
  ("Lanes/Semantics/", .actors),
  ("Lanes/Lib/", .std),
  ("Lanes/Outside/IO/FileSystem.lean", .std),
  ("Lanes/Web/IO/Tls.lean", .std),
  ("Lanes/Runtime/", .runtime),
  ("Lanes/Outside/IO/Clock.lean", .runtime),
  ("Lanes/Behaviours/Jobs/IO/Pool.lean", .runtime),
  ("Lanes/Semantics/FairRuns.lean", .runtime),
  ("Lanes/Semantics/Restart.lean", .runtime),
  ("Lanes/Web/", .web),
  ("Lanes/Lib/Mime/", .web),
  ("Lanes/Semantics/Front.lean", .web),
  ("Lanes/Testing/", .web),
  ("Lanes/Testing.lean", .web),
  ("Lanes.lean", .umbrella),
  ("Lanes/Proofs.lean", .umbrella),
  ("Lanes/Semantics.lean", .umbrella),
  ("Lanes/Services/", .services),
  ("Lanes/Services.lean", .services)
]

/-- The package of the module at `path`, relative to the root of Lanes. -/
def home? (path : String) : Option Package :=
  let found := homes.filter fun (start, _) => path.startsWith start
  (found.foldl (fun best (start, p) =>
    match best with
    | some (b, _) => if start.length > b.length then some (start, p) else best
    | none => some (start, p)) none).map (·.2)

/-- The module an `import` line names, if the line is one: `public import all Lanes.X` names
`Lanes.X`. -/
def imported? (line : String) : Option String :=
  let words := (line.trimAscii.toString.splitOn " ").filter (· != "")
  let lead := words.takeWhile fun w => ["public", "private", "meta"].contains w
  match words.drop lead.length with
  | "import" :: rest =>
    match rest.filter (· != "all") with
    | [module] => some module
    | _ => none
  | _ => none

/-- The path of a module of Lanes: `Lanes.Web.Http.Basic` is `Lanes/Web/Http/Basic.lean`. -/
def pathOf (module : String) : String :=
  "/".intercalate (module.splitOn ".") ++ ".lean"

end Lanes.Cli.Layers
