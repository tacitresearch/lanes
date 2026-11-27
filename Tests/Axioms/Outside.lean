/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Outside/`. -/

-- Lanes.Outside.Store.Sound
/-- info: 'Lanes.Store.lost_commit_either' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.lost_commit_either

/-- info: 'Lanes.Store.lost_commit_later' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.lost_commit_later

/-- info: 'Lanes.Store.failed_never_committed' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.failed_never_committed

/-- info: 'Lanes.Store.insert_unique' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.insert_unique

/-- info: 'Lanes.Store.write_skew' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.write_skew

/-- info: 'Lanes.Store.lost_update' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.lost_update

/-- info: 'Lanes.Store.serializable_earlier' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.serializable_earlier

/-- info: 'Lanes.Store.sees_acknowledged' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Store.sees_acknowledged
