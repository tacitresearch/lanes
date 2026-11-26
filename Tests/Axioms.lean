/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Examples.BankProofs
import Examples.ElectionProofs
import Examples.WatchdogProofs
import Tests.BatchProofs

/-!
The axiom gate (rule 5.5). Each headline theorem may depend only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one of them, this file stops compiling. It is built
by `lake build`, not linked into the test executable.
-/

/-- info: 'Lanes.System.Reachable.actor' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Reachable.actor

/-- info: 'Lanes.Refines.of_map' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_map

/-- info: 'Lanes.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Refines.trans

/-- info: 'Lanes.Refines.traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Refines.traces

/-- info: 'Lanes.System.reachable_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.reachable_iff

/-- info: 'Lanes.System.LeadsTo.ensures_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.ensures_of_invariant

/-- info: 'Lanes.System.LeadsTo.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.trans

/-- info: 'Lanes.System.Run.Fair.output_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.output_taken

/-- info: 'Lanes.System.Run.Impatient.fair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Impatient.fair

/-- info: 'Lanes.System.Run.fairAfter_fair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.fairAfter_fair

/-- info: 'Lanes.System.exists_fair_run_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.exists_fair_run_of_run

/-- info: 'Lanes.System.Reachable.exists_fair_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.exists_fair_run

/-- info: 'Lanes.System.exists_fair_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.exists_fair_run

/-- info: 'Lanes.System.LeadsTo.reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.reachable

/-- info: 'Lanes.Http.deadline_not_restarted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.deadline_not_restarted

/-- info: 'Lanes.Http.pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.pending_leaves

/-- info: 'Lanes.Http.answered_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.answered_of_leaves

/-- info: 'Lanes.Http.pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.pending_answered

/-- info: 'Examples.Watchdog.exists_fair_run_never_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Watchdog.exists_fair_run_never_barks

/-- info: 'Examples.Watchdog.impatient_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Watchdog.impatient_barks

/-- info: 'Lanes.Html.escape_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.escape_safe

/-- info: 'Lanes.SysState.step_of_mem_successors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.step_of_mem_successors

/-- info: 'Lanes.SysState.mem_successors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.mem_successors_iff

/-- info: 'Lanes.Kernel.abs_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.abs_boot

/-- info: 'Lanes.Kernel.accept_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.accept_sound

/-- info: 'Lanes.Kernel.run1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.run1_sound

/-- info: 'Lanes.Kernel.fire_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.fire_sound

/-- info: 'Lanes.Http.gate_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.gate_bounded

/-- info: 'Lanes.Http.answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.answered_le_arrived

/-- info: 'Lanes.Http.answered_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.answered_nodup

/-- info: 'Lanes.Http.kernel_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.kernel_answered_le_arrived

/-- info: 'Lanes.Http.deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.deadlines_armed

/-- info: 'Lanes.Http.Gate.step_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.step_bounded

/-- info: 'Lanes.Http.Gate.answered_le_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.answered_le_handled

/-- info: 'Lanes.Http.fronted_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_answered_le_arrived

/-- info: 'Lanes.Http.fronted_answered_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_answered_nodup

/-- info: 'Lanes.Http.Gate.deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.deadlines_armed

/-- info: 'Lanes.Http.fronted_deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_deadlines_armed

/-- info: 'Lanes.Http.kernel_fronted_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.kernel_fronted_answered_le_arrived

/-- info: 'Lanes.Http.Route.match?_link' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Http.Route.match?_link

/-- info: 'Lanes.Http.percentDecode_percentEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.percentDecode_percentEncode

/-- info: 'Lanes.Kernel.exec_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_outputs

/-- info: 'Lanes.Kernel.runBatch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runBatch_sound

/-- info: 'Lanes.Kernel.runBatch_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.runBatch_outputs

/-- info: 'Lanes.Journal.open?_file' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.open?_file

/-- info: 'Lanes.Journal.open?_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.open?_cut

/-- info: 'Lanes.Journal.recover_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_handed

/-- info: 'Lanes.Journal.resume_eq_recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.resume_eq_recover

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

/-- info: 'Lanes.Http.Waiting.exec_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_handed

/-- info: 'Lanes.Http.Waiting.exec_handed_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_handed_nodup

/-- info: 'Lanes.Http.Waiting.exec_waiting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_waiting

/-- info: 'Lanes.Http.Waiting.exec_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_answered

/-- info: 'Lanes.Http.Waiting.exec_drain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_drain

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

/-- info: 'Lanes.Kernel.abs_image_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.abs_image_kernel

/-- info: 'Lanes.Kernel.WellFormed.image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.WellFormed.image

/-- info: 'Lanes.Parcel.receive_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Parcel.receive_send

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

/-- info: 'Lanes.Journal.turns_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turns_kernel

/-- info: 'Lanes.Journal.recover_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_kernel

/-- info: 'Lanes.Journal.recover_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_outputs

/-- info: 'Lanes.Kernel.exec_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_reachable

/-- info: 'Lanes.Kernel.exec_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_append

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

/-- info: 'Lanes.System.Inductive.of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Inductive.of_monotone

/-- info: 'Lanes.SysState.erase_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.erase_step

/-- info: 'Lanes.System.Invariant.of_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.of_ghost

/-- info: 'Lanes.System.Invariant.to_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.to_ghost

/-- info: 'Lanes.System.Monotone.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Monotone.invariant

/-- info: 'Lanes.System.Monotone.and' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Monotone.and

/-- info: 'Lanes.System.Monotone.timers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Monotone.timers

/-- info: 'Lanes.SysState.mem_seen_grow_of_mem' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.mem_seen_grow_of_mem

/-- info: 'Lanes.Quorum.majority_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Quorum.majority_inter

/-- info: 'Lanes.SysState.Equiv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Equiv.step

/-- info: 'Lanes.SysState.equiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.equiv_iff

/-- info: 'Lanes.World.Equiv.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.World.Equiv.next

/-- info: 'Lanes.Server.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Server.implements

/-- info: 'Lanes.Check.Monitor.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.sound

/-- info: 'Lanes.Check.Monitor.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.complete

/-- info: 'Lanes.Check.Monitor.ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.ok_iff

/-- info: 'Examples.Bank.balance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.balance_nonneg

/-- info: 'Examples.Bank.money_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.money_conserved

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

/-- info: 'Lanes.netEquiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.netEquiv_iff

/-- info: 'Lanes.Check.Node.beq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Node.beq_iff
/-- info: 'Examples.Election.election_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Election.election_safety

/-- info: 'Examples.Election.atMostOneLeaderPerTerm_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Election.atMostOneLeaderPerTerm_invariant
/-- info: 'Lanes.Scenario.reachable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Scenario.reachable_iff

/-- info: 'Lanes.Check.system_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.system_violated

/-- info: 'Lanes.Check.system_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.system_sound

/-- info: 'Lanes.Check.system_sound_of_respects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.system_sound_of_respects

/-- info: 'Lanes.Check.Monitor.beq_iff_abs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.beq_iff_abs_eq

/-- info: 'Lanes.Service.monitored_respects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Service.monitored_respects

/-- info: 'Lanes.Check.refines_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.refines_sound

/-- info: 'Lanes.Check.refines_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.refines_traces

/-- info: 'Lanes.Codec.extTreeMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Codec.extTreeMap

/-- info: 'Lanes.Frame.encode_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.encode_append

/-- info: 'Lanes.Frame.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_encode

/-- info: 'Lanes.Frame.decode_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_take

/-- info: 'Lanes.Frame.decode_take_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_take_eq

/-- info: 'Lanes.Frame.prefix_decode_encode_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.prefix_decode_encode_append

/-- info: 'Lanes.Frame.decode_extract_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_extract_prefix

/-- info: 'Lanes.Frame.decode_checksum_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_checksum_ne
/-- info: 'Lanes.System.Reachable.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.left

/-- info: 'Lanes.SysState.run_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.run_left

/-- info: 'Lanes.SysState.run_filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.run_filterMapIO

/-- info: 'Lanes.System.handled_le_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.handled_le_put

/-- info: 'Lanes.System.Invariant.filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.filterMapIO

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

/-- info: 'Lanes.System.Reachable.lossy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Reachable.lossy

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

/-- info: 'Lanes.Refines.of_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_invariant

/-- info: 'Lanes.Refines.of_lift' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_lift

/-- info: 'Lanes.System.Refines.of_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_ghost

/-- info: 'Lanes.System.Refines.to_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.to_ghost

/-- info: 'Lanes.System.Refines.of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_steps

/-- info: 'Lanes.SysState.Loses.settle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Loses.settle

/-- info: 'Tests.Batch.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements

/-- info: 'Tests.Batch.implements_withPast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements_withPast

/-- info: 'Lanes.Http.Request.fields_framing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.fields_framing

/-- info: 'Lanes.Http.Request.head_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.head_plain

/-- info: 'Lanes.Http.Response.read_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_ended

/-- info: 'Lanes.Http.Response.read_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_more

/-- info: 'Lanes.Http.Response.read_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_some

/-- info: 'Lanes.Http.Response.read_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_append

/-- info: 'Lanes.Http.Response.read_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wire

/-- info: 'Lanes.Http.Response.read_wire_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wire_extract

/-- info: 'Lanes.Http.Response.read_wireChunked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireChunked

/-- info: 'Lanes.Http.Response.read_wireChunked_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireChunked_extract

/-- info: 'Lanes.Http.Response.read_wireAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireAfter

/-- info: 'Lanes.Http.Response.read_wireAfter_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireAfter_extract

/-- info: 'Lanes.Http.Response.read_wireToEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireToEnd

/-- info: 'Lanes.Http.Response.read_wireToEnd_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireToEnd_open
