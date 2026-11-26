/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.All

/-!
`lake exe lanesOracle [--cases N] [--seed S] [--record] [package…]` builds each package's Go
program with `go build`, asks it the same generated cases as ours and compares. It fails on any
difference that no `known` predicate decides, after shrinking it by deleting bytes. `--record`
rewrites `Tests/Oracle/vectors/<package>.jsonl` from the first answers, for `lake test`.
-/

open Lanes Tests.Oracle

structure Options where
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

def recorded : Nat := 1000

def oracleDir : IO System.FilePath := return (← IO.currentDir) / ".lake" / "oracle"

def build (name : String) : IO System.FilePath := do
  let bin := (← oracleDir) / name
  IO.FS.createDirAll (← oracleDir)
  let out ← IO.Process.output
    { cmd := "go", args := #["build", "-o", bin.toString, s!"./{name}"], cwd := some "oracle" }
  if out.exitCode != 0 then throw (IO.userError s!"go build ./{name} failed:\n{out.stderr}")
  return bin

def caseLines (cases : Array Case) : String :=
  String.join (cases.toList.mapIdx fun i c => Json.compress (c.json i) ++ "\n")

def ask (bin : System.FilePath) (cases : Array Case) : IO (Array Answer) := do
  let file := bin.addExtension "cases.jsonl"
  IO.FS.writeFile file (caseLines cases)
  let out ← IO.Process.output { cmd := bin.toString, args := #[file.toString] }
  if out.exitCode != 0 then throw (IO.userError s!"{bin} failed:\n{out.stderr}")
  match readLines out.stdout >>= (·.mapM readAnswer) with
  | .ok answers =>
    if answers.size == cases.size then return answers
    else throw (IO.userError s!"{bin} answered {answers.size} of {cases.size} cases")
  | .error e => throw (IO.userError s!"{bin}: {e}")

def deletions (c : Case) : Array Case :=
  (Array.range c.input.size).map fun k => ⟨c.op, ⟨c.input.data.eraseIdxIfInBounds k⟩⟩

def shrink (p : Package) (bin : System.FilePath) : Nat → Case → Answer → IO (Case × Answer)
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

def compare (o : Options) (p : Package) : IO Bool := do
  let bin ← build p.name
  let cases := p.cases o.count o.seed
  let answers ← ask bin cases
  let verdicts := (cases.zip answers).map fun (c, go) => (c, go, p.judge c go)
  let agree := verdicts.filter (·.2.2 == .agree) |>.size
  let differ := verdicts.filter (·.2.2 == .differ)
  IO.println s!"{p.name}: {cases.size} cases at seed {o.seed}: {agree} agree, \
    {cases.size - agree - differ.size} known differences, {differ.size} disagreements"
  for (reason, n, c, go) in tally verdicts do
    IO.println s!"  known ({n}): {reason}; for example {showCase c}: ours {showAnswer (p.answer c)}, Go {showAnswer go}"
  for (c, go, _) in differ.toList.take 10 do
    let (c, go) ← shrink p bin c.input.size c go
    IO.println s!"  DIFFER {showCase c}: ours {showAnswer (p.answer c)}, Go {showAnswer go}"
  unless differ.isEmpty do
    IO.println s!"  reproduce: lake exe lanesOracle --cases {o.count} --seed {o.seed} {p.name}"
  if o.record then
    let lines := (cases.zip answers).toList.take recorded |>.mapIdx fun i (c, go) =>
      Json.compress (Json.mkObj (("id", (i : Json)) :: ("op", (c.op : Json))
        :: ("in", (Bytes.hex c.input : Json)) :: answerFields go)) ++ "\n"
    IO.FS.writeFile (vectorsPath p.name) (String.join lines)
    IO.println s!"  recorded {lines.length} answers in {vectorsPath p.name}"
  return differ.isEmpty

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error arg =>
    IO.eprintln s!"lanesOracle: bad argument {arg}; usage: lanesOracle [--cases N] [--seed S] [--record] [package…]"
    return 2
  | .ok o =>
    let chosen := if o.names.isEmpty then packages else packages.filter (o.names.contains ·.name)
    let results ← chosen.mapM (compare o)
    return if results.all id then 0 else 1
