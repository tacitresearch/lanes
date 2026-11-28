/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes

/-!
The runner behind an application's `lake test`, and Lanes' own: named results of tests, model
checks, proofs and builds, printed as text or, with `--json`, as one JSON object, and an exit
code that tells a complete pass from a bounded one.

Each result has a kind, so that a program reading the output knows what failed without parsing
text: the code did not build, a proof does not hold, a model check failed, or a test did. A
check whose search hit a bound is `bounded`: it passed only in the part of its instance it
explored, and the run exits 2, not 0.
-/

@[expose] public section

namespace Lanes.Testing

inductive Kind where
  | build | proof | check | test
  deriving DecidableEq, Repr

def Kind.label : Kind → String
  | .build => "build" | .proof => "proof" | .check => "check" | .test => "test"

inductive Status where
  | passed
  /-- A model check passed, but only in the part of its instance it explored. -/
  | bounded
  | failed
  deriving DecidableEq, Repr

def Status.label : Status → String
  | .passed => "passed" | .bounded => "bounded" | .failed => "failed"

def Status.ofVerdict : Check.Verdict → Status
  | .complete => .passed
  | .bounded => .bounded
  | .failed => .failed

structure Result where
  name : String
  kind : Kind
  status : Status
  /-- What to show with it: a check's report, or a build's messages when it failed. -/
  detail : String := ""
  deriving DecidableEq, Repr

namespace Result

def ofBool (kind : Kind) (name : String) (ok : Bool) (detail : String := "") : Result :=
  { name, kind, status := if ok then .passed else .failed, detail }

/-- Named tests, each passed or failed. -/
def tests (results : List (String × Bool)) (kind : Kind := .test) : List Result :=
  results.map fun (name, ok) => ofBool kind name ok

/-- A model check, by its report: a complete pass passes, a bounded one is `bounded`. `detail`
is what to print, usually the report rendered. -/
def check {S L : Type} (name : String) (r : Check.Report S L) (detail : String := "") : Result :=
  { name, kind := .check, status := Status.ofVerdict r.verdict, detail }

def toJson (r : Result) : Json :=
  .obj #[("name", .str r.name), ("kind", .str r.kind.label), ("status", .str r.status.label),
    ("detail", .str r.detail)]

end Result

def count (results : List Result) (s : Status) : Nat :=
  results.countP (·.status == s)

/-- 1 if anything failed; else 2 if a check was bounded; else 0. -/
def exitCode (results : List Result) : UInt32 :=
  if count results .failed > 0 then 1
  else if count results .bounded > 0 then 2
  else 0

def toJson (results : List Result) : Json :=
  .obj #[("passed", .num (count results .passed)), ("bounded", .num (count results .bounded)),
    ("failed", .num (count results .failed)), ("results", .arr (results.map (·.toJson)).toArray)]

/-- The line naming a result; for one that passed, only if `passes`. -/
def line (r : Result) (passes : Bool := false) : Option String :=
  match r.status with
  | .passed => if passes then some s!"ok ({r.kind.label}) {r.name}" else none
  | .bounded => some s!"BOUNDED ({r.kind.label}) {r.name}"
  | .failed => some s!"FAIL ({r.kind.label}) {r.name}"

/-- What the runner prints as text: each result's detail and a line naming it, then the counts.
A result that passed gets its line only if `passes`, for a long list. The first `shown`
results were printed already. -/
def render (results : List Result) (shown : Nat := 0) (passes : Bool := true) : String :=
  let each := (results.drop shown).flatMap fun r =>
    (if r.detail.isEmpty then [] else [r.detail]) ++ (line r passes).toList
  let counts := s!"{count results .passed} passed, {count results .bounded} bounded, \
    {count results .failed} failed"
  "\n".intercalate (each ++ [counts])

def wantsJson (args : List String) : Bool :=
  args.contains "--json"

/-- Print the results with `print`, as JSON if `args` holds `--json` and as text otherwise
(`render`), and return the exit code. -/
def report (args : List String) (results : List Result) (shown : Nat := 0)
    (passes : Bool := true) (print : String → IO Unit := IO.println) : IO UInt32 := do
  print (if wantsJson args then (toJson results).compress else render results shown passes)
  (← IO.getStdout).flush
  return exitCode results

/-- What Lake printed, without its `trace:` lines, which give each command it ran. -/
def messages (output : String) : String :=
  "\n".intercalate ((output.trimAscii.toString.splitOn "\n").filter (!·.startsWith "trace:"))

/-- Build `modules` with `lake build --wfail`, so that a `sorry`, which is only a warning, fails
too: a result of kind `proof` named `name`. The checks run first and do not import the modules,
so a broken proof does not stop them. -/
def build (name : String) (modules : List String) (kind : Kind := .proof) : IO Result := do
  try
    let out ← IO.Process.output { cmd := "lake", args := #["build", "--wfail"] ++ modules.toArray }
    let ok := out.exitCode == 0
    return .ofBool kind name ok (if ok then "" else messages (out.stdout ++ out.stderr))
  catch e =>
    return .ofBool kind name false s!"`lake build` did not start: {e}"

end Lanes.Testing
