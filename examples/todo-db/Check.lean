/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import TodoDb

/-!
The to-do list against a user who adds to-dos and the store model (`Lanes/Outside/Store/Basic.lean`)
at each isolation level, run by `lake test`. The store answers each request with what it may,
fails it, or loses the answer; a lost `COMMIT` may have taken effect, or may take effect at any
later moment, or never, and the model keeps every database consistent with what the system has
seen. Check before you prove (Lanes rule 5.1).

With `keyed := false` the checker finds the duplicate: the `COMMIT`'s answer is lost, the to-do
is appended again in a new transaction, and in a database the answers allow it is there twice.
With `keyed := true` no database the store may be in has a to-do twice, and a to-do reported
added is in every one.
-/

open Lanes TodoDb

instance : sig.Inspect := by instance_by_cases
instance (cfg : Config) : (system cfg).Inspect := by instance_by_cases

/-- The user: the to-dos still to add, and what the system said about each. -/
structure User where
  toAdd : List (Nat × String)
  added : List Nat := []
  gaveUp : List Nat := []
  deriving DecidableEq, Hashable

instance : BEq User := instBEqOfDecidableEq

def user (todos : List (Nat × String)) : Outside sig User where
  init := { toAdd := todos }
  allow d
    | .add key title => if (key, title) ∈ d.toAdd then some { d with toAdd := d.toAdd.erase (key, title) } else none
    | .store _ => none
  observe d
    | .added key => { d with added := d.added ++ [key] }
    | .gaveUp key => { d with gaveUp := d.gaveUp ++ [key] }
    | .store _ => d

def storeConfig (isolation : Store.Isolation) : Store.Config Nat :=
  { isolation, nextKey := fun keys => keys.foldl max 0 + 1 }

def world (isolation : Store.Isolation) (todos : List (Nat × String)) :=
  (user todos).both (Store.outside (storeConfig isolation) port) fun x => x matches .add ..

abbrev W (cfg : Config) := World (system cfg) (User × Store.State Nat String)

def samples (isolation : Store.Isolation) (failures : Bool) (d : User × Store.State Nat String) : List In :=
  d.1.toAdd.map (fun (key, title) => .add key title)
    ++ Store.samples (storeConfig isolation) port failures true d.2

/-- No database the store may be in holds a to-do twice. -/
def noDuplicate (w : W cfg) : Bool :=
  w.driver.2.worlds.all fun db =>
    let titles := db.db.map (·.2)
    titles.eraseDups.length == titles.length

/-- With the fix, a to-do reported added is in every database the store may be in, under its key. -/
def addedStored (w : W cfg) : Bool :=
  !cfg.keyed || w.driver.1.added.all fun key => w.driver.2.worlds.all fun db => db.db.any (·.1 == key)

def check (cfg : Config) (isolation : Store.Isolation) (todos : List (Nat × String)) (failures : Bool) :=
  Check.system (system cfg) { driver := (world isolation todos).driver (samples isolation failures) }
    [ .always "no database the store may be in has a to-do twice" noDuplicate,
      .always "a to-do reported added is in every database the store may be in" addedStored,
      .sometimes "a to-do is added" fun w => !w.driver.1.added.isEmpty,
      .sometimes "a commit's answer is lost" fun w =>
        w.driver.2.worlds.any fun db => db.commits.any (·.request.isNone) ]
    {}

def report (r : Check.Report (W cfg) (Event sig)) : String :=
  match r.failure with
  | none => s!"PASS ({r.states} states{if r.complete then "" else ", bounded"})"
  | some (.violated p t) =>
    s!"FAIL: \"{p}\" after {t.steps.length} steps:\n" ++ "\n".intercalate (t.steps.map fun (e, _) => "  " ++ (Event.render e))
  | some (.unreached ps) => s!"FAIL: never reached {ps}"
  | some (.deadlock _) => "FAIL: deadlock"

def duplicate (r : Check.Report (W cfg) (Event sig)) : Bool :=
  match r.failure with
  | some (.violated p _) => p == "no database the store may be in has a to-do twice"
  | _ => false

def todos : List (Nat × String) := [(1, "milk")]

def tests : IO (List (String × Bool)) := do
  let buggyRc := check { keyed := false } .readCommitted todos false
  let buggySer := check { keyed := false } .serializable todos false
  let fixedRc := check { keyed := true } .readCommitted todos true
  let fixedSer := check { keyed := true } .serializable todos true
  let fixedTwo := check { keyed := true } .readCommitted [(1, "milk"), (2, "eggs")] false
  IO.println s!"appended, read committed: {report buggyRc}"
  IO.println s!"appended, serializable: {report buggySer}"
  IO.println s!"keyed, read committed, with failures: {report fixedRc}"
  IO.println s!"keyed, serializable, with failures: {report fixedSer}"
  IO.println s!"keyed, two to-dos: {report fixedTwo}"
  return [
    ("appending and retrying a lost COMMIT stores a to-do twice, at read committed", duplicate buggyRc),
    ("and at serializable", duplicate buggySer),
    ("the keyed insert never stores a to-do twice, at read committed, with failures",
      fixedRc.ok && fixedRc.complete),
    ("and at serializable", fixedSer.ok && fixedSer.complete),
    ("and with two to-dos", fixedTwo.ok && fixedTwo.complete) ]

def main : IO UInt32 := do
  let results ← tests
  for (name, ok) in results do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  return if results.all (·.2) then 0 else 1
