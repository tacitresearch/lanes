/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Proof/`. -/

-- Lanes.Proof.Deed
/-- info: 'Lanes.System.handled_le_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.handled_le_put

-- Lanes.Proof.Equiv
/-- info: 'Lanes.SysState.Equiv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Equiv.step

-- Lanes.Proof.Ghost
/-- info: 'Lanes.SysState.erase_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.erase_step

/-- info: 'Lanes.System.Invariant.of_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.of_ghost

/-- info: 'Lanes.System.Invariant.to_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.to_ghost

-- Lanes.Proof.JoinSound
/-- info: 'Lanes.SysState.exists_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.exists_block

/-- info: 'Lanes.System.Reachable.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.left

/-- info: 'Lanes.SysState.run_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.run_left

/-- info: 'Lanes.System.Invariant.join_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.join_left

/-- info: 'Lanes.System.Invariant.join_left_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.join_left_state

/-- info: 'Lanes.System.Reachable.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.right

/-- info: 'Lanes.System.Invariant.join_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.join_right

/-- info: 'Lanes.System.Invariant.join_right_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.join_right_state

/-- info: 'Lanes.System.Reachable.right_of_quiet_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.right_of_quiet_boot

-- Lanes.Proof.Lift
/-- info: 'Lanes.System.Reachable.actor' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Reachable.actor

/-- info: 'Lanes.System.invariant_of_actor' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.invariant_of_actor

-- Lanes.Proof.Loses
/-- info: 'Lanes.SysState.Loses.settle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Loses.settle

-- Lanes.Proof.Lossy
/-- info: 'Lanes.System.Reachable.lossy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.lossy

-- Lanes.Proof.MapIOSound
/-- info: 'Lanes.SysState.run_filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.run_filterMapIO

/-- info: 'Lanes.System.Invariant.filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.filterMapIO

-- Lanes.Proof.Monotone
/-- info: 'Lanes.System.Inductive.of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Inductive.of_monotone

/-- info: 'Lanes.System.Monotone.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Monotone.invariant

/-- info: 'Lanes.System.Monotone.and' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Monotone.and

/-- info: 'Lanes.System.Monotone.and_net' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Monotone.and_net

/-- info: 'Lanes.System.Monotone.timers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Monotone.timers

-- Lanes.Proof.Past
/-- info: 'Lanes.SysState.mem_seen_grow_of_mem' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.mem_seen_grow_of_mem
