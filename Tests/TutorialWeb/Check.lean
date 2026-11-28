/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.TutorialWeb.Files

/-!
Step 5 of `docs/TUTORIAL-WEB.md`: the model check of the shelf beside the store's model, run on
the shelf and on the shelf with the step's bug.
-/

namespace Tests.TutorialWeb

open Lanes Shelf

instance : sig.Inspect := {}
instance : system.Inspect := {}

/-- The members' browsers: the requests still to send, each with the requests whose answers it
waits for, and what the front answered. -/
structure Browsers where
  toSend : List (Nat × Request × List Nat)
  answered : List (Nat × Answer) := []
  deriving DecidableEq, Hashable

instance : BEq Browsers := instBEqOfDecidableEq

def browsers (requests : List (Nat × Request × List Nat)) : Outside sig Browsers where
  init := { toSend := requests }
  allow d
    | .request n r => match d.toSend.find? (·.1 == n) with
      | some (_, r', waits) =>
        if r' == r && waits.all (fun w => d.answered.any (·.1 == w)) then
          some { d with toSend := d.toSend.filter (·.1 != n) }
        else none
      | none => none
    | .store _ => none
  observe d
    | .answered n a => { d with answered := d.answered ++ [(n, a)] }
    | _ => d

abbrev D := Browsers × Db.State Request Answer

def uploadsOf (db : Db.Db) : List Upload := (db.rows uploads.table.name).filterMap uploads.ofRow

def holds (db : Db.Db) (who : Member) (file : Int64) : Bool :=
  (uploadsOf db).any fun u => u.owner == who && u.id == file

def begun (db : Db.Db) : Bool := !(db.rows counters.table.name).isEmpty

def requests : List (Nat × Request × List Nat) :=
  [(1, .begin "alice" 0, []), (2, .seen "alice" 0 (some 5), [1]), (3, .delete "bob" 0, [1]),
    (4, .delete "alice" 0, [2]), (5, .begin "alice" 0, [1])]

/-- The bug the tutorial seeds: a delete takes the file off whoever asks. -/
def buggy (config : Config) : Db.Handler Request Answer
  | .delete _ file => do
    match (← onShelf config).find? (·.id == file) with
    | some u =>
      let _ ← uploads.delete [.text u.owner, .int file]
      return .deleted file
    | none => return .refused file
  | r => handler config r

def report (handler : Config → Db.Handler Request Answer) :=
  let world := (browsers requests).both
    (Db.outside {} (handler { maxFiles := 1 }) (Db.Db.empty schema) port) fun x => x matches .request ..
  let samples := fun (d : D) =>
    d.1.toSend.map (fun (n, r, _) => In.request n r)
      ++ Db.samples (handler { maxFiles := 1 }) port false false d.2
  Check.system system { driver := world.driver samples }
    [ .always "the shelf holds at most one upload" fun w =>
        w.driver.2.worlds.all fun world => (uploadsOf world.db).length ≤ 1,
      .sometimes "the shelf is full" fun w => w.driver.1.answered.any (·.2 == .full),
      .sometimes "a file is listed" fun w =>
        w.driver.2.worlds.any fun world => (uploadsOf world.db).any (·.size.isSome),
      .always "only its uploader deletes a file" fun w =>
        w.driver.2.worlds.all fun world => holds world.db "alice" 0 || !begun world.db
          || !w.driver.1.toSend.contains (4, .delete "alice" 0, [2]),
      .sometimes "a file is deleted" fun w =>
        w.driver.2.worlds.any fun world => begun world.db && !holds world.db "alice" 0 ]
    {}

end Tests.TutorialWeb
