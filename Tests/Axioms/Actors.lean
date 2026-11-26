/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Actors/`. -/

-- Lanes.Actors.Batch
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

-- Lanes.Actors.CourierSound
/-- info: 'Lanes.Peers.Courier.Reachable.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.Reachable.sound

/-- info: 'Lanes.Peers.Courier.Reachable.queue_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.Reachable.queue_le

/-- info: 'Lanes.Peers.Courier.Reachable.write_not_busy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.Reachable.write_not_busy

/-- info: 'Lanes.Peers.Courier.written_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.written_between

/-- info: 'Lanes.Peers.Courier.write_dialed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.write_dialed

/-- info: 'Lanes.Peers.Courier.stop_closes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.stop_closes

/-- info: 'Lanes.Peers.Courier.after_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.after_stop

/-- info: 'Lanes.Peers.Courier.rest_after_break' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.rest_after_break

/-- info: 'Lanes.Peers.Courier.delivered_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.delivered_read

/-- info: 'Lanes.Peers.Courier.written_sublist_sent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Peers.Courier.written_sublist_sent

-- Lanes.Actors.Deed
/-- info: 'Lanes.System.handled_le_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.handled_le_put

-- Lanes.Actors.Disk
/-- info: 'Lanes.Journal.Disk.load_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.load_cut

/-- info: 'Lanes.Journal.Disk.read_of_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.read_of_start

/-- info: 'Lanes.Journal.Disk.torn_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.torn_nil

/-- info: 'Lanes.Journal.Disk.Torn.load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.load

/-- info: 'Lanes.Journal.Disk.Torn.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.read

/-- info: 'Lanes.Journal.Disk.Torn.mend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.mend

/-- info: 'Lanes.Journal.Disk.Torn.mend_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.mend_crash

/-- info: 'Lanes.Journal.Disk.Holds.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.append

/-- info: 'Lanes.Journal.Disk.Holds.append_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.append_crash

/-- info: 'Lanes.Journal.Disk.Holds.save' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.save

/-- info: 'Lanes.Journal.Disk.Holds.save_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.save_crash

/-- info: 'Lanes.Journal.Disk.Holds.load_append_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.load_append_crash

/-- info: 'Lanes.Journal.Disk.Holds.load_save_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.load_save_crash

-- Lanes.Actors.Equiv
/-- info: 'Lanes.SysState.Equiv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Equiv.step

-- Lanes.Actors.Ghost
/-- info: 'Lanes.SysState.erase_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.erase_step

/-- info: 'Lanes.System.Invariant.of_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.of_ghost

/-- info: 'Lanes.System.Invariant.to_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.to_ghost

-- Lanes.Actors.Inspect
/-- info: 'Lanes.SysState.step_of_mem_successors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.step_of_mem_successors

-- Lanes.Actors.JoinSound
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

-- Lanes.Actors.Journal
/-- info: 'Lanes.Journal.open?_file' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.open?_file

/-- info: 'Lanes.Journal.open?_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.open?_cut

/-- info: 'Lanes.Journal.recover_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_handed

/-- info: 'Lanes.Journal.resume_eq_recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.resume_eq_recover

/-- info: 'Lanes.Journal.turns_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turns_kernel

/-- info: 'Lanes.Journal.recover_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_kernel

/-- info: 'Lanes.Journal.recover_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_outputs

-- Lanes.Actors.KernelSound
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

-- Lanes.Actors.KernelTimers
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

-- Lanes.Actors.Lift
/-- info: 'Lanes.System.Reachable.actor' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Reachable.actor

-- Lanes.Actors.Loses
/-- info: 'Lanes.SysState.Loses.settle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Loses.settle

-- Lanes.Actors.Lossy
/-- info: 'Lanes.System.Reachable.lossy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.lossy

-- Lanes.Actors.MailboxSound
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

-- Lanes.Actors.MapIOSound
/-- info: 'Lanes.SysState.run_filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.run_filterMapIO

/-- info: 'Lanes.System.Invariant.filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.filterMapIO

-- Lanes.Actors.Monotone
/-- info: 'Lanes.System.Inductive.of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Inductive.of_monotone

/-- info: 'Lanes.System.Monotone.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Monotone.invariant

/-- info: 'Lanes.System.Monotone.and' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Monotone.and

/-- info: 'Lanes.System.Monotone.timers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Monotone.timers

-- Lanes.Actors.Past
/-- info: 'Lanes.SysState.mem_seen_grow_of_mem' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.mem_seen_grow_of_mem

-- Lanes.Actors.Release
/-- info: 'Lanes.SysState.Released.visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Released.visible

/-- info: 'Lanes.SysState.Leads.reachable' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.Leads.reachable

-- Lanes.Actors.Shard
/-- info: 'Lanes.Parcel.receive_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Parcel.receive_send

-- Lanes.Actors.ShardSound
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

-- Lanes.Actors.ShardsSound
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
