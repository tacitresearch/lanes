/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Runtime/`. -/

-- Lanes.Runtime.Batch
/-- info: 'Lanes.Batch.group_ins' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Batch.group_ins

/-- info: 'Lanes.Batch.run_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.run_kernel

/-- info: 'Lanes.Batch.run_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.run_handed

/-- info: 'Lanes.Batch.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.run_sound

/-- info: 'Lanes.Batch.run_peek' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.run_peek

/-- info: 'Lanes.Batch.settle_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.settle_kernel

/-- info: 'Lanes.Batch.run_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.run_resolved

/-- info: 'Lanes.Batch.flush_save' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.flush_save

/-- info: 'Lanes.Batch.due_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.due_iff

/-- info: 'Lanes.Batch.run_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Batch.run_spread

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

/-- info: 'Lanes.Kernel.abs_image_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.abs_image_kernel

/-- info: 'Lanes.Kernel.exec_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_reachable

/-- info: 'Lanes.Kernel.exec_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_append

/-- info: 'Lanes.Kernel.exec_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_visible

-- Lanes.Runtime.KernelTimers
/-- info: 'Lanes.Kernel.WellFormed.image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.image

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

-- Lanes.Runtime.MailboxSound
/-- info: 'Lanes.Mailbox.Reachable.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.Reachable.sound

/-- info: 'Lanes.Mailbox.Reachable.offer_full_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.Reachable.offer_full_iff

/-- info: 'Lanes.Mailbox.Reachable.bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.Reachable.bounded

/-- info: 'Lanes.Mailbox.Reachable.asleep_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.Reachable.asleep_empty

/-- info: 'Lanes.Mailbox.Reachable.not_asleep_waiting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.Reachable.not_asleep_waiting

/-- info: 'Lanes.Mailbox.rest_eq_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Mailbox.rest_eq_false

/-- info: 'Lanes.Mailbox.batch_since_take' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Mailbox.batch_since_take

/-- info: 'Lanes.Mailbox.wake_since_take' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Mailbox.wake_since_take

/-- info: 'Lanes.Mailbox.close_since_take' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Mailbox.close_since_take

/-- info: 'Lanes.Mailbox.woken_after_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.woken_after_rest

/-- info: 'Lanes.Mailbox.after_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Mailbox.after_close

-- Lanes.Runtime.Release
/-- info: 'Lanes.Event.filterMap_eq_of_awake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Event.filterMap_eq_of_awake

/-- info: 'Lanes.SysState.Released.visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Released.visible

/-- info: 'Lanes.SysState.Leads.reachable' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.Leads.reachable

-- Lanes.Runtime.Shard
/-- info: 'Lanes.Parcel.receive_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Parcel.receive_send

-- Lanes.Runtime.ShardSound
/-- info: 'Lanes.SysState.AtHome.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.AtHome.step

/-- info: 'Lanes.SysState.init_merged_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.init_merged_equiv

/-- info: 'Lanes.System.SplitReachable.merged_of_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.SplitReachable.merged_of_init

/-- info: 'Lanes.System.SplitReachable.merged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.SplitReachable.merged

/-- info: 'Lanes.System.Invariant.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.split

/-- info: 'Lanes.System.Invariant.split_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.split_state

/-- info: 'Lanes.System.SplitReachable.merged_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.SplitReachable.merged_exact

/-- info: 'Lanes.System.Invariant.split_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.split_of_forall

-- Lanes.Runtime.ShardsSound
/-- info: 'Lanes.Shards.AtHome.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Shards.AtHome.step

/-- info: 'Lanes.SysState.init_unsharded_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.init_unsharded_equiv

/-- info: 'Lanes.System.ShardsReachable.unsharded_of_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.ShardsReachable.unsharded_of_init

/-- info: 'Lanes.System.ShardsReachable.unsharded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.ShardsReachable.unsharded

/-- info: 'Lanes.System.Invariant.shards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.shards

/-- info: 'Lanes.System.Invariant.shards_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.shards_of_forall

/-- info: 'Lanes.System.Invariant.shards_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.shards_state

-- Lanes.Runtime.Wave
/-- info: 'Lanes.Kernel.frame_handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.frame_handle

/-- info: 'Lanes.Kernel.frame_startActor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.frame_startActor

/-- info: 'Lanes.Kernel.frame_fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.frame_fire

/-- info: 'Lanes.Kernel.runBatchAhead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runBatchAhead_eq

/-- info: 'Lanes.Kernel.good_plan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.good_plan

/-- info: 'Lanes.Kernel.runBatch_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runBatch_add

/-- info: 'Lanes.Kernel.waves_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.waves_eq

/-- info: 'Lanes.Kernel.runWaves_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runWaves_eq

/-- info: 'Lanes.Kernel.exec_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_inputs
