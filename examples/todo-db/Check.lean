/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import TodoDb
import Lanes.Testing

/-!
The to-do list against a user and the typed store's model (`Lanes/Db/Model.lean`), run by `lake
test`. The store answers each call with what one run of the handler gives, fails it, or loses
the answer; a lost `COMMIT` may have taken effect, or may take effect at any later moment, or
never, and the model keeps every database consistent with what the system has seen. Check
before you prove (Lanes rule 5.1).

With the unchecked handler the checker finds a duplicate: the answer to an `add` is lost, the
actor sends it again, and in a database the answers allow the title is there twice. With the
checked handler no database the store may be in has a title twice for one user, which
`TodoDb.unique_always` proves for every run.
-/

open Lanes TodoDb

instance : sig.Inspect := by instance_by_cases
instance (cfg : TodoDb.Config) : (system cfg).Inspect := by instance_by_cases

/-- The user: the requests still to send, and what the system answered. -/
structure User where
  toSend : List (Nat × Request)
  answered : List (Nat × Answer) := []
  gaveUp : List Nat := []
  deriving DecidableEq, Hashable

instance : BEq User := instBEqOfDecidableEq

def user (requests : List (Nat × Request)) : Outside sig User where
  init := { toSend := requests }
  allow d
    | .request n r => if (n, r) ∈ d.toSend then some { d with toSend := d.toSend.erase (n, r) } else none
    | .store _ => none
  observe d
    | .answered n a => { d with answered := d.answered ++ [(n, a)] }
    | .gaveUp n => { d with gaveUp := d.gaveUp ++ [n] }
    | .call _ => d

abbrev D := User × Db.State Request Answer

def world (cfg : TodoDb.Config) (requests : List (Nat × Request)) :=
  (user requests).both (Db.outside {} (handler cfg.checked) (Db.Db.empty schema) port) fun x => x matches .request ..

abbrev W (cfg : TodoDb.Config) := World (system cfg) D

def samples (cfg : TodoDb.Config) (failures : Bool) (d : D) : List In :=
  d.1.toSend.map (fun (n, r) => .request n r) ++ Db.samples (handler cfg.checked) port failures true d.2

/-- No user has two to-dos with one title, in any database the store may be in. -/
def unique (w : W cfg) : Bool :=
  w.driver.2.worlds.all fun db =>
    let titles := (db.db.rows todos.table.name).map byTitle.project
    titles.eraseDups.length == titles.length

def check (cfg : TodoDb.Config) (requests : List (Nat × Request)) (failures : Bool) :=
  Check.system (system cfg) { driver := (world cfg requests).driver (samples cfg failures) }
    [ .always "no user has two to-dos with one title" unique,
      .sometimes "a to-do is added" fun w => w.driver.1.answered.any fun | (_, .added _) => true | _ => false,
      .sometimes "an answer is lost" fun w => w.driver.2.worlds.any fun db => !db.lost.isEmpty ]
    {}

def report (r : Check.Report (W cfg) (Event sig)) : String :=
  match r.failure with
  | none => s!"PASS ({if r.ok then "complete" else "bounded"}, {r.states} states)"
  | some (.violated p t) =>
    s!"FAIL: \"{p}\" after {t.steps.length} steps:\n" ++ "\n".intercalate (t.steps.map fun (e, _) => "  " ++ (Event.render e))
  | some (.unreached ps) => s!"FAIL: never reached {ps}"
  | some (.deadlock _) => "FAIL: deadlock"

def duplicate (r : Check.Report (W cfg) (Event sig)) : Bool :=
  match r.failure with
  | some (.violated p _) => p == "no user has two to-dos with one title"
  | _ => false

def milk : List (Nat × Request) := [(1, .add 7 "milk")]

def tests (json : Bool) : IO (List (String × Bool)) := do
  let unchecked := check { checked := false } milk false
  let checked := check {} milk true
  let two := check {} [(1, .add 7 "milk"), (2, .add 7 "milk")] false
  let mixed := check { attempts_max := 1 } [(1, .add 7 "milk"), (2, .complete 7 0), (3, .remove 7 0)] false
  unless json do
    IO.println s!"unchecked, a lost answer and a retry: {report unchecked}"
    IO.println s!"checked, with failures: {report checked}"
    IO.println s!"checked, the same title twice: {report two}"
    IO.println s!"checked, add, complete and remove: {report mixed}"
  return [
    ("adding without looking, and retrying a lost answer, stores a title twice", duplicate unchecked),
    ("the checked add never stores a title twice, with failures", checked.ok),
    ("nor when a user adds the same title twice", two.ok),
    ("nor with add, complete and remove at once", mixed.ok) ]

def main (args : List String) : IO UInt32 := do
  let results ← tests (Lanes.Testing.wantsJson args)
  Lanes.Testing.report args (Lanes.Testing.Result.tests results .check)
