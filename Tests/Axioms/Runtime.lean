/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Runtime/`. -/

-- Lanes.Runtime.KernelSound
/-- info: 'Lanes.Kernel.exec_inductive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_inductive

/-- info: 'Lanes.Kernel.exec_cell_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_cell_reachable

/-- info: 'Lanes.Kernel.abs_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.abs_boot

/-- info: 'Lanes.Kernel.accept_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.accept_sound

/-- info: 'Lanes.Kernel.run1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.run1_sound

/-- info: 'Lanes.Kernel.fire_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.fire_sound

/-- info: 'Lanes.Kernel.exec_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_outputs

/-- info: 'Lanes.Kernel.runBatch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runBatch_sound

/-- info: 'Lanes.Kernel.runBatch_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runBatch_outputs

/-- info: 'Lanes.Kernel.exec_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_reachable

/-- info: 'Lanes.Kernel.exec_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_append

/-- info: 'Lanes.Kernel.exec_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_visible

/-- info: 'Lanes.Kernel.performAll_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.performAll_eq

-- Lanes.Runtime.KernelTimers
/-- info: 'Lanes.Kernel.boot_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.boot_wellFormed

/-- info: 'Lanes.Kernel.WellFormed.apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.apply

/-- info: 'Lanes.Kernel.exec_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_wellFormed

/-- info: 'Lanes.Kernel.WellFormed.runBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.runBatch

/-- info: 'Lanes.Kernel.WellFormed.wait_of_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.wait_of_due

/-- info: 'Lanes.Kernel.WellFormed.step_of_queued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.step_of_queued

/-- info: 'Lanes.Kernel.WellFormed.step_of_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.step_of_due

/-- info: 'Lanes.Kernel.WellFormed.runBatch_of_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.runBatch_of_due

/-- info: 'Lanes.Kernel.WellFormed.step_events_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.step_events_ne_nil

/-- info: 'Lanes.Kernel.WellFormed.quiet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.quiet_iff

/-- info: 'Lanes.Kernel.WellFormed.wait_for_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.wait_for_ms

/-- info: 'Lanes.Kernel.WellFormed.wait_forever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.wait_forever

-- Lanes.Runtime.Peek
/-- info: 'Lanes.Peek.get_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peek.get_of

/-- info: 'Lanes.Peek.others_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peek.others_of

/-- info: 'Lanes.Peek.init_of_not_others' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peek.init_of_not_others

-- Lanes.Runtime.Release
/-- info: 'Lanes.Event.filterMap_eq_of_awake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Event.filterMap_eq_of_awake

/-- info: 'Lanes.SysState.Released.visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Released.visible

/-- info: 'Lanes.SysState.Leads.reachable' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.Leads.reachable

-- Lanes.Runtime.SchedSound
/-- info: 'Lanes.Sched.Step.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Step.sound

/-- info: 'Lanes.Sched.Step.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Step.inv

/-- info: 'Lanes.Sched.Run.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Run.sound

/-- info: 'Lanes.Sched.Run.reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Run.reachable

/-- info: 'Lanes.Sched.Model.init_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Model.init_spec

/-- info: 'Lanes.Sched.Slot.take_push' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Sched.Slot.take_push

/-- info: 'Lanes.Sched.Slot.put_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Slot.put_push

/-- info: 'Lanes.Sched.Slot.put_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Slot.put_eq

/-- info: 'Lanes.Sched.Ledger.offer_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Sched.Ledger.offer_taken

/-- info: 'Lanes.Sched.Ledger.offer_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Sched.Ledger.offer_refused

/-- info: 'Lanes.Sched.Ledger.done_wakes' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Sched.Ledger.done_wakes
