/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Db/`. -/

-- Lanes.Db.Sound
/-- info: 'Lanes.Db.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.invariant

/-- info: 'Lanes.Db.Retry.loop_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Retry.loop_committed

/-- info: 'Lanes.Db.Txn.interp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Txn.interp_apply

/-- info: 'Lanes.Db.Txn.run_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Txn.run_bind

/-- info: 'Lanes.Db.Op.rows_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Op.rows_apply

/-- info: 'Lanes.Db.Op.insert_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Op.insert_rows

/-- info: 'Lanes.Db.Scan.run_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Scan.run_eq_nil

/-- info: 'Lanes.Db.Scan.matches_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Scan.matches_lookup

/-- info: 'Lanes.Db.Value.compare_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Value.compare_eq_iff
