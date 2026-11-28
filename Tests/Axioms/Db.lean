/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Db/`. -/

-- Lanes.Db.Columns
/-- info: 'Lanes.Db.Columns.toRow_of_ofRow' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Db.Columns.toRow_of_ofRow

/-- info: 'Lanes.Db.Columns.table' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Db.Columns.table

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

/-- info: 'Lanes.Db.world_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.world_invariant

/-- info: 'Lanes.Db.Op.unique_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Op.unique_apply

-- Lanes.Db.JobsSound
/-- info: 'Lanes.Db.Jobs.Queue.keeps_beside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.keeps_beside

/-- info: 'Lanes.Db.Jobs.Queue.claimed_has' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.claimed_has

/-- info: 'Lanes.Db.Jobs.Queue.enqueue_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.enqueue_keeps

/-- info: 'Lanes.Db.Jobs.Queue.claim_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.claim_length

/-- info: 'Lanes.Db.Jobs.Queue.claim_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.claim_attempts

/-- info: 'Lanes.Db.Jobs.Queue.claim_takes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.claim_takes

/-- info: 'Lanes.Db.Jobs.Queue.finish_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.finish_stale

/-- info: 'Lanes.Db.Jobs.Queue.one_per_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Jobs.Queue.one_per_key

-- Lanes.Db.OnceSound
/-- info: 'Lanes.Db.Keys.once_again' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Keys.once_again

-- Lanes.Db.WorkerSound
/-- info: 'Lanes.Db.Worker.committed_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Worker.committed_only

/-- info: 'Lanes.Db.Worker.once_each' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Db.Worker.once_each
