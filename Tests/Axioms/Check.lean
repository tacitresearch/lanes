/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Check/`. -/

-- Lanes.Check.Complete
/-- info: 'Lanes.SysState.mem_successors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.mem_successors_iff

-- Lanes.Check.EquivDecide
/-- info: 'Lanes.SysState.equiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.equiv_iff

/-- info: 'Lanes.netEquiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.netEquiv_iff

-- Lanes.Check.Monitor
/-- info: 'Lanes.Service.State.equiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Service.State.equiv_iff

/-- info: 'Lanes.Service.State.equiv_of_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Service.State.equiv_of_ret

/-- info: 'Lanes.Check.Monitor.distinct_filterMap_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.distinct_filterMap_ret

/-- info: 'Lanes.Check.Monitor.withinFrom_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.withinFrom_eq

-- Lanes.Check.SearchSound
/-- info: 'Lanes.Check.search_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_violated

/-- info: 'Lanes.Check.search_deadlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_deadlock

/-- info: 'Lanes.Check.search_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_witness

/-- info: 'Lanes.Check.search_states_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_states_le

/-- info: 'Lanes.Check.search_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_sound

/-- info: 'Lanes.Check.search_sound_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_sound_of_lawful

/-- info: 'Lanes.Check.search_unreached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_unreached

/-- info: 'Lanes.Check.search_deadlock_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_deadlock_free

/-- info: 'Lanes.Check.search_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_reached

/-- info: 'Lanes.Check.search_unreached_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_unreached_exists

/-- info: 'Lanes.Check.Search.explore_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Search.explore_eq

/-- info: 'Lanes.Check.Search.runBatches_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Search.runBatches_eq

-- Lanes.Check.SystemSound
/-- info: 'Lanes.Check.Node.beq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Node.beq_iff

/-- info: 'Lanes.Scenario.reachable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Scenario.reachable_iff

/-- info: 'Lanes.Check.system_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.system_violated

/-- info: 'Lanes.Check.system_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.system_sound

/-- info: 'Lanes.Check.system_sound_of_respects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.system_sound_of_respects

-- Lanes.Check.WorldEquiv
/-- info: 'Lanes.World.Equiv.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.World.Equiv.next
