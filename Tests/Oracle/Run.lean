/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Basic

/-!
The driver of the pure oracles: `[--cases N] [--seed S] [--record] [package…]` sets up each
package's reference program (`go build` for Go, a virtual environment made from its
`requirements.txt` for Python), asks it the same generated cases as ours and compares. It fails
on any difference that no `known` predicate decides, after shrinking it by deleting bytes.
`--record` rewrites `oracles/<reference>/answers.jsonl` from the first answers, for `lake test`.
Built programs and environments are kept in `LANES_ORACLE_CACHE`, or else `.lake/oracles`.
-/

namespace Tests.Oracle

open Lanes

structure Options where
  command : String
  count : Nat := 20000
  seed : Nat := 0
  record : Bool := false
  names : List String := []

def parseArgs : List String → Options → Except String Options
  | "--cases" :: n :: rest, o => do parseArgs rest { o with count := ← n.toNat?.elim (throw n) pure }
  | "--seed" :: n :: rest, o => do parseArgs rest { o with seed := ← n.toNat?.elim (throw n) pure }
  | "--record" :: rest, o => parseArgs rest { o with record := true }
  | name :: rest, o => parseArgs rest { o with names := o.names ++ [name] }
  | [], o => return o

def cacheDir (root : System.FilePath) : IO System.FilePath := do
  match (← IO.getEnv "LANES_ORACLE_CACHE").filter (!·.isEmpty) with
  | some dir => return dir
  | none => return root / ".lake" / "oracles"

/-- A reference's program, ready to be given a file of cases. -/
structure Program where
  cmd : String
  args : Array String := #[]
  /-- Where the file of cases is written. -/
  scratch : System.FilePath

def step (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) : IO Unit := do
  let out ← IO.Process.output { cmd, args, cwd }
  if out.exitCode != 0 then
    throw (IO.userError s!"{cmd} {" ".intercalate args.toList} failed:\n{out.stderr}{out.stdout}")

/-- Builds the Go program, or makes the Python environment again when `requirements.txt` is
not the one it was made from. `root` is absolute. -/
def setUp (root : System.FilePath) : Reference → IO Program
  | .go dir => do
    let cache ← cacheDir root
    let bin := cache / "go" / dir
    IO.FS.createDirAll (cache / "go")
    step "go" #["build", "-o", bin.toString, s!"./{dir}"] (root / "oracles" / "go")
    return { cmd := bin.toString, scratch := bin.addExtension "cases.jsonl" }
  | .python dir => do
    let venv := (← cacheDir root) / "venv" / dir
    let requirements := root / "oracles" / dir / "requirements.txt"
    let wanted ← IO.FS.readFile requirements
    let stamp := venv / "lanes-requirements.txt"
    let made ← if ← stamp.pathExists then some <$> IO.FS.readFile stamp else pure none
    unless made == some wanted do
      step ((← IO.getEnv "LANES_PYTHON").getD "python3") #["-m", "venv", "--clear", venv.toString]
      step (venv / "bin" / "pip").toString
        #["install", "--quiet", "--disable-pip-version-check", "-r", requirements.toString]
      IO.FS.writeFile stamp wanted
    return { cmd := (venv / "bin" / "python").toString,
             args := #["-I", (root / "oracles" / dir / "main.py").toString],
             scratch := venv / "cases.jsonl" }

def caseLines (cases : Array Case) : String :=
  String.join (cases.toList.mapIdx fun i c => Json.compress (c.json i) ++ "\n")

def ask (bin : Program) (cases : Array Case) : IO (Array Answer) := do
  IO.FS.writeFile bin.scratch (caseLines cases)
  let out ← IO.Process.output { cmd := bin.cmd, args := bin.args.push bin.scratch.toString }
  if out.exitCode != 0 then throw (IO.userError s!"{bin.cmd} failed:\n{out.stderr}")
  match readLines out.stdout >>= (·.mapM readAnswer) with
  | .ok answers =>
    if answers.size == cases.size then return answers
    else throw (IO.userError s!"{bin.cmd} answered {answers.size} of {cases.size} cases")
  | .error e => throw (IO.userError s!"{bin.cmd}: {e}")

def deletions (c : Case) : Array Case :=
  (Array.range c.input.size).map fun k => ⟨c.op, ⟨c.input.data.eraseIdxIfInBounds k⟩⟩

def shrink (p : Package) (bin : Program) : Nat → Case → Answer → IO (Case × Answer)
  | 0, c, go => return (c, go)
  | fuel + 1, c, go => do
    let smaller := deletions c
    let answers ← ask bin smaller
    match (smaller.zip answers).find? fun (c, go) => p.judge c go == .differ with
    | some (c, go) => shrink p bin fuel c go
    | none => return (c, go)

def showCase (c : Case) : String :=
  match String.fromUTF8? c.input with
  | some s => s!"{c.op} {s.quote}"
  | none => s!"{c.op} hex {Bytes.hex c.input}"

def showAnswer : Answer → String
  | none => "refused"
  | some out => Json.compress out

def tally (verdicts : Array (Case × Answer × Verdict)) : List (String × Nat × Case × Answer) :=
  verdicts.foldl (init := []) fun acc (c, go, v) =>
    match v with
    | .known reason =>
      match acc.find? (·.1 == reason) with
      | some _ => acc.map fun (r, n, e) => if r == reason then (r, n + 1, e) else (r, n, e)
      | none => acc ++ [(reason, 1, c, go)]
    | _ => acc

def compare (root : System.FilePath) (o : Options) (p : Package) : IO Bool := do
  let bin ← setUp root p.reference
  let cases := p.cases o.count o.seed
  let answers ← ask bin cases
  let verdicts := (cases.zip answers).map fun (c, go) => (c, go, p.judge c go)
  let agree := verdicts.filter (·.2.2 == .agree) |>.size
  let differ := verdicts.filter (·.2.2 == .differ)
  let accepted := answers.filter (·.isSome) |>.size
  IO.println s!"{p.name}: {cases.size} cases at seed {o.seed}, {accepted} accepted by the reference: \
    {agree} agree, {cases.size - agree - differ.size} known differences, {differ.size} disagreements"
  for (reason, n, c, go) in tally verdicts do
    IO.println s!"  known ({n}): {reason}; for example {showCase c}: ours {showAnswer (p.answer c)}, reference {showAnswer go}"
  for (c, go, _) in differ.toList.take 10 do
    let (c, go) ← if p.shrinks then shrink p bin c.input.size c go else pure (c, go)
    IO.println s!"  DIFFER {showCase c}: ours {showAnswer (p.answer c)}, reference {showAnswer go}"
  unless differ.isEmpty do
    IO.println s!"  reproduce: lake exe {o.command} --cases {o.count} --seed {o.seed} {p.name}"
  if o.record then
    let lines := (cases.zip answers).toList.take p.recorded |>.mapIdx fun i (c, go) =>
      Json.compress (Json.mkObj (("id", (i : Json)) :: ("op", (c.op : Json))
        :: ("in", (Bytes.hex c.input : Json)) :: answerFields go)) ++ "\n"
    IO.FS.writeFile (p.vectorsPath root) (String.join lines)
    IO.println s!"  recorded {lines.length} answers in oracles/{p.reference.dir}/{p.answers}"
  return differ.isEmpty

/-- The command line of `command`, comparing `packages`, for the repository at `root`. -/
def main (command : String) (root : System.FilePath) (packages : List Package)
    (args : List String) : IO UInt32 := do
  match parseArgs args { command } with
  | .error arg =>
    IO.eprintln s!"{command}: bad argument {arg}; usage: {command} [--cases N] [--seed S] [--record] [package…]"
    return 2
  | .ok o =>
    let unknown := o.names.filter fun n => !packages.any (·.name == n)
    unless unknown.isEmpty do
      IO.eprintln s!"{command}: no package {", ".intercalate unknown}; there are {", ".intercalate (packages.map (·.name))}"
      return 2
    let root ← IO.FS.realPath root
    let chosen := if o.names.isEmpty then packages else packages.filter (o.names.contains ·.name)
    let results ← chosen.mapM (compare root o)
    return if results.all id then 0 else 1

end Tests.Oracle
