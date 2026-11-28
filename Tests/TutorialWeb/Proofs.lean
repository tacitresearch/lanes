/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.TutorialWeb.Files

/-!
The theorem of step 5, and its axiom gate. Nothing executable imports this file.
-/

namespace Shelf

open Lanes Lanes.Db

/-- What a request made as `who` writes of the uploads: rows whose key starts with `who`. -/
abbrev Writes (who : Member) : Op → Prop :=
  Op.WritesWithin uploads.table (·.head? = some (.text who))

theorem writes (config : Config) (r : Request) : (handler config r).All (Writes r.who) := by
  have counter : ∀ o : Op, o.table = counters.table → Writes r.who o :=
    fun o ht hn => absurd (ht ▸ hn) (by decide)
  have shelf : (onShelf config).All (Writes r.who) :=
    TableOf.scan_all _ _ fun _ => ⟨rfl, fun k hk => by cases hk⟩
  have next : nextId.All (Writes r.who) :=
    Txn.All.bind (TableOf.get_all _ _ (counter _ rfl)) fun _ =>
      Txn.All.bind (TableOf.upsert_all _ _ (counter _ rfl)) fun _ => .pure _
  cases r with
  | list who at_s => exact Txn.All.bind shelf fun _ => .pure _
  | begin who at_s =>
    refine Txn.All.bind shelf fun _ => ?_
    split
    · exact .pure _
    · exact Txn.All.bind next fun _ =>
        Txn.All.bind (TableOf.insert_all _ _ fun _ => ⟨rfl, fun k hk => by cases hk; rfl⟩) fun _ => .pure _
  | seen who file size =>
    cases size with
    | some n =>
      exact Txn.All.bind (TableOf.update_all _ _ fun _ => ⟨rfl, fun k hk => by cases hk; rfl⟩) fun _ => by
        split <;> exact .pure _
    | none => exact .pure _
  | delete who file =>
    exact Txn.All.bind (TableOf.delete_all _ _ fun _ => ⟨rfl, fun k hk => by cases hk; rfl⟩) fun _ => by
      split <;> exact .pure _

/-- **Only its uploader takes a file off the shelf.** A transaction of a request made as `who`
leaves every upload of another member on the shelf if it was there, and off it if it was not. -/
theorem only_uploader_deletes (config : Config) (r : Request) {db : Db} {a : Answer} {db' : Db}
    (h : (handler config r).run db = .ok (a, db')) (u : Upload) (other : u.owner ≠ r.who) :
    uploads.toRow u ∈ db'.rows uploads.table.name ↔ uploads.toRow u ∈ db.rows uploads.table.name :=
  Txn.All.others (writes config r) h (by simpa [uploads, Columns.table, Table.keyOf] using other)

end Shelf

/-- info: 'Shelf.only_uploader_deletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shelf.only_uploader_deletes
