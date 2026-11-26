/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Differential tests against Go (`docs/decisions/D50-differential-tests-against-go.md`). A package
generates cases, Go's program in `oracle/<name>/` answers them, and ours must give the same
answer or one its `known` predicate names a reason for. `lake test` replays the answers recorded
in `Tests/Oracle/vectors/<name>.jsonl`; `lake exe lanesOracle` asks Go itself.
-/

namespace Tests.Oracle

open Lanes

structure Case where
  op : String
  input : ByteArray

/-- `none` when the input is refused. -/
abbrev Answer := Option Json

abbrev Gen := StateM StdGen

namespace Gen

def below (n : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (n - 1)

def chance (percent : Nat) : Gen Bool := return (← below 100) < percent

def pick {α : Type} [Inhabited α] (xs : List α) : Gen α := return xs.getD (← below xs.length) default

def list {α : Type} (n : Nat) (one : Gen α) : Gen (List α) :=
  (List.range n).mapM fun _ => one

def bytes (maxLength : Nat) : Gen ByteArray := do
  let n ← below (maxLength + 1)
  return ⟨(← list n (return (← below 256).toUInt8)).toArray⟩

def text (alphabet : List Char) (maxLength : Nat) : Gen String := do
  return String.ofList (← list (← below (maxLength + 1)) (pick alphabet))

/-- One edit: a character deleted, inserted or replaced. -/
def mutate (alphabet : List Char) (s : String) : Gen String := do
  let chars := s.toList
  let at_ ← below (chars.length + 1)
  let c ← pick alphabet
  match ← below 3 with
  | 0 => return String.ofList (chars.eraseIdx at_)
  | 1 => return String.ofList (chars.insertIdx at_ c)
  | _ => return String.ofList (chars.set at_ c)

def run {α : Type} (seed : Nat) (g : Gen α) : α := (StateT.run g (mkStdGen seed)).1

end Gen

structure Package where
  name : String
  /-- Cases that are always asked first: the RFC's examples, the edges. -/
  edges : List Case
  case : Gen Case
  answer : Case → Answer
  /-- Given Go's answer to a case where ours differs, the decided reason, if there is one. -/
  known : Case → Answer → Option String := fun _ _ => none

def Package.cases (p : Package) (count seed : Nat) : Array Case :=
  (p.edges ++ Gen.run seed (Gen.list (count - min count p.edges.length) p.case)).toArray.take count

def text (s : String) (op : String) : Case := ⟨op, s.toUTF8⟩

def Case.json (c : Case) (id : Nat) : Json :=
  Json.mkObj [("id", (id : Json)), ("op", (c.op : Json)), ("in", (Bytes.hex c.input : Json))]

def answerFields : Answer → List (String × Json)
  | none => [("ok", (false : Json))]
  | some out => [("ok", (true : Json)), ("out", out)]

def readAnswer (j : Json) : Except String Answer := do
  if ← (j.getObjValD "ok").getBool? then return some (j.getObjValD "out") else return none

def readCase (j : Json) : Except String Case := do
  let op ← (j.getObjValD "op").getStr?
  match Bytes.unhex? (← (j.getObjValD "in").getStr?) with
  | some input => return ⟨op, input⟩
  | none => throw "input is not lowercase hex"

def readLines (text : String) : Except String (Array Json) :=
  ((text.splitOn "\n").filter (· ≠ "")).toArray.mapM Json.parse

inductive Verdict where
  | agree
  | known (reason : String)
  | differ
  deriving DecidableEq

def Package.judge (p : Package) (c : Case) (go : Answer) : Verdict :=
  if p.answer c = go then .agree
  else match p.known c go with
    | some reason => .known reason
    | none => .differ

def vectorsPath (name : String) : System.FilePath := s!"Tests/Oracle/vectors/{name}.jsonl"

def Package.vectors (p : Package) : IO (Except String (Array (Case × Answer))) := do
  let lines ← IO.FS.readFile (vectorsPath p.name)
  return do
    (← readLines lines).mapM fun j => return (← readCase j, ← readAnswer j)

/-- The recorded answers, replayed: every one must agree or be a known difference. -/
def Package.replay (p : Package) : IO (List (String × Bool)) := do
  match ← p.vectors with
  | .error e => return [(s!"oracle vectors of {p.name} read: {e}", false)]
  | .ok vectors =>
    let failed := vectors.filter fun (c, go) => p.judge c go = .differ
    for (c, go) in failed.toList.take 5 do
      IO.println s!"oracle {p.name}: {c.op} {Bytes.hex c.input}: ours {(p.answer c).map Json.compress}, Go {go.map Json.compress}"
    return [(s!"oracle vectors of {p.name}: {vectors.size} recorded answers of Go agree", failed.isEmpty)]

end Tests.Oracle
