# Inventory

Every public definition of `Lanes` and `LanesCli`, with its status and the evidence for it.
Generated from the built modules by `lake exe lanes lint --fix` (`LanesCli/Inventory.lean`);
do not edit. What each status means, and what is not listed, is in
`docs/decisions/D47-the-inventory-is-computed.md`. The definitions of `Lanes/` with status
none are on `docs/inventory-none.md`, which only shrinks.

## Summary

| Area | Definitions | proved | trusted | checked | tested | spec | none |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Lanes/Actors` | 339 | 166 | 10 | 36 | 20 | 85 | 22 |
| `Lanes/Auth` | 27 | 7 | 0 | 0 | 16 | 1 | 3 |
| `Lanes/Behaviours` | 44 | 36 | 0 | 1 | 0 | 7 | 0 |
| `Lanes/Check` | 91 | 54 | 0 | 25 | 0 | 10 | 2 |
| `Lanes/Data` | 324 | 152 | 5 | 4 | 120 | 12 | 31 |
| `Lanes/Env` | 30 | 0 | 30 | 0 | 0 | 0 | 0 |
| `Lanes/Html` | 42 | 2 | 0 | 0 | 28 | 0 | 12 |
| `Lanes/Http` | 176 | 99 | 1 | 9 | 35 | 18 | 14 |
| `Lanes/Semantics` | 53 | 9 | 0 | 0 | 0 | 43 | 1 |
| `LanesCli` | 110 | 0 | 0 | 0 | 42 | 0 | 68 |
| All | 1236 | 525 | 46 | 75 | 261 | 176 | 153 |

## `Lanes/Actors/Actor.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Actor.run` | spec | used only in statements |
| `Actor.mapEff` | none |  |
| `Actor.comapMsg` | none |  |
| `Actor.Invariant` | spec | a predicate |

## `Lanes/Actors/Batch.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Batch.due` | proved | `Batch.due_iff`, `Batch.flush_save` |
| `Batch.put` | proved | `Batch.flush_save` |
| `Batch.work` | proved | through `Batch.flush`, `Batch.run` and 1 more: `Batch.flush_save`, `Batch.run_handed` and 5 more |
| `Batch.flush` | proved | `Batch.flush_save` |
| `Batch.scan` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_kernel` and 4 more |
| `Batch.finish` | proved | through `Batch.run`: `Batch.run_handed`, `Batch.run_kernel` and 3 more |
| `Batch.run` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.run_peek` and 2 more |
| `Batch.Act.ops` | proved | through `Batch.journal`: `Batch.run_handed`, `Batch.run_kernel` and 1 more |
| `Batch.Act.outputs` | proved | through `Batch.handed`: `Batch.run_handed` |
| `Batch.Act.events` | proved | through `Batch.recorded`: `Batch.run_handed` |
| `Batch.journal` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.settle_kernel` |
| `Batch.handed` | proved | `Batch.run_handed` |
| `Batch.recorded` | proved | `Batch.run_handed` |
| `Batch.Act.Sound` | spec | a predicate |
| `Batch.Sound` | spec | a predicate |
| `Batch.Command.idle?` | spec | used only in statements |
| `Batch.settle` | spec | used only in statements |

## `Lanes/Actors/Courier.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Courier.wire` | proved | `Peers.Courier.Reachable.queue_le`, `Peers.Courier.Reachable.write_not_busy` |
| `Peers.Courier.setWire` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.dial` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.enqueue` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.next` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.step` | proved | `Peers.Courier.Reachable.write_not_busy` |

## `Lanes/Actors/CourierSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Line.conn?` | none |  |
| `Peers.Line.until?` | spec | used only in statements |
| `Peers.Courier.exec` | spec | used only in statements |
| `Peers.Courier.Reachable` | spec | a predicate |
| `Peers.Courier.Status.close` | spec | used only in statements |
| `Peers.Courier.Status.written` | spec | used only in statements |
| `Peers.Courier.Status.next` | spec | used only in statements |
| `Peers.Courier.status` | spec | used only in statements |
| `Peers.Courier.Status.isOpen` | spec | used only in statements |
| `Peers.Courier.Stopped.next` | spec | used only in statements |
| `Peers.Courier.Watch.ready` | spec | used only in statements |
| `Peers.Courier.Watch.told` | spec | used only in statements |
| `Peers.Courier.Watch.next` | spec | used only in statements |
| `Peers.Courier.Watch.Holds` | spec | a predicate |
| `Peers.Courier.sentTo` | spec | used only in statements |
| `Peers.Courier.writtenTo` | spec | used only in statements |
| `Peers.Courier.Order.told` | spec | used only in statements |
| `Peers.Courier.Order.next` | spec | used only in statements |
| `Peers.Courier.Order.Holds` | spec | a predicate |
| `Peers.Courier.readPieces` | spec | used only in statements |
| `Peers.Event.receives` | spec | used only in statements |
| `Peers.Entry.closes` | spec | used only in statements |
| `Peers.Courier.receivedOn` | spec | used only in statements |
| `Peers.Courier.deliveredFrom` | spec | used only in statements |
| `Peers.Action.parcel?` | spec | used only in statements |
| `Peers.Courier.leftover` | spec | used only in statements |

## `Lanes/Actors/Deed.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.deed` | proved | through `deeds`, `handled`: `Http.Gate.answered_le_handled`, `Jobs.answered_le_handled` and 1 more |
| `deeds` | spec | used only in statements |
| `Deed.handles` | spec | used only in statements |
| `handled` | spec | used only in statements |
| `put` | spec | used only in statements |
| `Effect.Avoids` | spec | a predicate |

## `Lanes/Actors/Disk.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Disk.apply` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.save`, `Journal.Disk.Torn.mend` |
| `Journal.Disk.crash` | proved | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash` and 2 more |
| `Journal.Disk.Found.index` | proved | `Journal.Disk.Torn.read` |
| `Journal.Disk.read` | proved | `Journal.Disk.Torn.mend`, `Journal.Disk.Torn.mend_crash`, `Journal.Disk.Torn.read` and 1 more |
| `Journal.Disk.start` | proved | `Journal.Disk.read_of_start` |
| `Journal.Disk.mend` | proved | `Journal.Disk.Torn.mend`, `Journal.Disk.Torn.mend_crash` |
| `Journal.Disk.load` | proved | `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Torn.load` and 1 more |
| `Journal.appendWrites` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` |
| `Journal.saveWrites` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` |
| `Journal.memo` | spec | used only in statements |
| `Journal.Disk.Holds` | spec | a predicate |
| `Journal.Disk.Torn` | spec | a predicate |

## `Lanes/Actors/Equiv.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `onLink` | none |  |
| `System.Near` | spec | a predicate |

## `Lanes/Actors/FairScheduler.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.actor?` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `Effect.timeouts` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `SysState.arms` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `SysState.owed` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `SysState.maybeOwed` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.requeue` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.init` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.take` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.next` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.advance` | tested | `Tests/Fair.lean` |

## `Lanes/Actors/Ghost.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.withGhost` | proved | `SysState.erase_step`, `System.Invariant.of_ghost`, `System.Invariant.to_ghost` and 2 more |
| `SysState.erase` | spec | used only in statements |

## `Lanes/Actors/Inspect.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instHashableEmpty_lanes` | checked | `Tests/Election.lean`, `Tests/Join.lean` |
| `instReprEmpty_lanes` | none |  |
| `instHashableEnvelope` | checked | `Tests/Join.lean` |
| `instHashableEffect` | checked | `Tests/KV.lean` |
| `instReprEffect` | checked | `Tests/KV.lean` |
| `shortNames` | checked | `Tests/KV.lean` |
| `brief` | checked | `Tests/KV.lean` |
| `Envelope.render` | checked | `Tests/KV.lean` |
| `Event.render` | checked | `Tests/KV.lean` |
| `Event.kind` | none |  |
| `Event.kinds` | none |  |
| `SysState.candidates` | proved | through `SysState.successors`: `SysState.mem_successors_iff`, `SysState.step_of_mem_successors` |
| `SysState.successors` | proved | `SysState.mem_successors_iff`, `SysState.step_of_mem_successors` |
| `Slot.of` | checked | `Tests/Join.lean` |
| `Slot.find` | checked | `Tests/Join.lean` |
| `Slot.stateAt` | checked | `Tests/Join.lean` |
| `Slot.timersAt` | checked | `Tests/Join.lean` |
| `Slot.same` | none |  |
| `Slot.allSame` | none |  |
| `Slot.hash` | none |  |
| `Slots.of` | checked | `Tests/Join.lean` |
| `Slots.state` | checked | `Tests/Join.lean` |
| `Slots.up` | checked | `Tests/Join.lean` |
| `Slots.timers` | checked | `Tests/Join.lean` |
| `SysState.compactWith` | checked | `Tests/Join.lean` |
| `SysState.compact` | checked | `Tests/Join.lean` |
| `SysState.without` | proved | through `SysState.equiv`, `SysState.netEquiv`: `SysState.equiv_iff`, `netEquiv_iff` |
| `SysState.netEquiv` | proved | `netEquiv_iff` |
| `SysState.equiv` | proved | `SysState.equiv_iff` |
| `SysState.trafficHash` | checked | `Tests/Join.lean` |
| `SysState.hash` | checked | `Tests/Join.lean` |
| `SysState.render` | none |  |

## `Lanes/Actors/Join.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instDecidableEqJoinMsg` | proved | its type, `Decidable` |
| `joinSig` | proved | `Jobs.attach_active_leaves`, `Jobs.attach_within`, `SysState.exists_block` and 11 more |
| `Wiring.left` | proved | through `SysState.over`, `System.filterMapIO` and 3 more: `SysState.exists_block`, `SysState.run_filterMapIO` and 14 more |
| `Wiring.right` | proved | through `System.join`, `Wiring.leftView`: `SysState.exists_block`, `SysState.run_left` and 10 more |
| `System.join` | proved | `SysState.exists_block`, `SysState.run_left`, `System.Invariant.join_left` and 9 more |
| `Signature.withIO` | proved | `SysState.run_filterMapIO`, `System.Invariant.filterMapIO`, `System.LeadsTo.filterMapIO` and 1 more |
| `Effect.filterMapOut` | proved | through `SysState.over`, `System.filterMapIO` and 1 more: `SysState.run_filterMapIO`, `System.Invariant.filterMapIO` and 2 more |
| `System.filterMapIO` | proved | `SysState.run_filterMapIO`, `System.Invariant.filterMapIO`, `System.LeadsTo.filterMapIO` and 1 more |
| `System.mapIO` | checked | `Tests/Join.lean` |
| `instHashableSum_lanes` | checked | `Tests/Fronted.lean`, `Tests/Jobs.lean`, `Tests/Join.lean` |
| `Signature.Inspect.join` | checked | `Tests/Jobs.lean`, `Tests/Join.lean` |
| `System.Inspect.join` | checked | `Tests/Jobs.lean`, `Tests/Join.lean` |
| `Signature.Inspect.withIO` | checked | `Tests/Join.lean` |
| `System.Inspect.filterMapIO` | checked | `Tests/Join.lean` |
| `System.Inspect.mapIO` | checked | `Tests/Join.lean` |

## `Lanes/Actors/JoinSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Envelope.left?` | proved | through `SysState.left`, `SysState.thinLeft` and 1 more: `SysState.run_left`, `System.Invariant.join_left` and 4 more |
| `Envelope.right?` | proved | through `SysState.right`: `System.Invariant.join_right`, `System.Reachable.right` and 1 more |
| `EnvModel.left` | proved | `SysState.run_left`, `System.Invariant.join_left`, `System.LeadsTo.join_left` and 3 more |
| `EnvModel.right` | proved | `System.Invariant.join_right`, `System.Reachable.right`, `System.Reachable.right_of_quiet_boot` |
| `SysState.left` | proved | `SysState.run_left`, `System.Invariant.join_left`, `System.LeadsTo.join_left` and 1 more |
| `SysState.right` | proved | `System.Invariant.join_right`, `System.Reachable.right`, `System.Reachable.right_of_quiet_boot` |
| `SysState.thinLeft` | proved | `System.LeadsTo.join_left`, `System.Run.Fair.left` |
| `Event.left?` | proved | through `Event.leftDeed`, `Wiring.leftView`: `SysState.run_left`, `System.Run.Fair.left` and 1 more |
| `Event.leftDeed` | proved | `SysState.run_left`, `System.Run.Fair.left` |
| `Wiring.shown` | proved | `SysState.run_left`, `System.Run.Fair.left` |
| `Wiring.wired` | spec | used only in statements |

## `Lanes/Actors/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Entry.codec` | proved | its type, `Codec` |
| `Journal.Entry.bytes` | proved | through `Journal.Entry.fits`, `Journal.encode`: `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash` and 7 more |
| `Journal.Entry.ofBytes` | proved | through `Journal.open?`: `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.Entry.fits` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and 6 more |
| `Journal.write` | proved | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.load_cut` and 1 more |
| `Journal.read` | proved | through `Journal.open?`: `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.encode` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save_crash` |
| `Journal.header` | proved | `Journal.Disk.load_cut`, `Journal.Disk.torn_nil`, `Journal.open?_cut` and 1 more |
| `Journal.named?` | proved | through `Journal.open?`: `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.file` | proved | `Journal.Disk.load_cut`, `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.open?` | proved | `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.Entry.op?` | proved | through `Journal.ops`: `Journal.recover_handed`, `Journal.recover_kernel` and 2 more |
| `Journal.Entry.marks` | spec | used only in statements |
| `Journal.ops` | proved | `Journal.recover_handed`, `Journal.recover_kernel`, `Journal.recover_outputs` and 1 more |
| `Journal.replay1` | proved | through `Journal.recover`, `Journal.resume` and 1 more: `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash` and 9 more |
| `Journal.recover` | proved | `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and 7 more |
| `Journal.Entry.savedAt` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and 2 more |
| `Journal.since` | proved | through `Journal.resume`: `Journal.resume_eq_recover` |
| `Journal.resume` | proved | `Journal.resume_eq_recover` |
| `Journal.turn` | proved | through `Journal.turns`: `Journal.turns_kernel` |
| `Journal.turns` | spec | used only in statements |

## `Lanes/Actors/Kernel.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.cell` | proved | `Batch.run_peek`, `Kernel.WellFormed.runBatch_of_due`, `Kernel.WellFormed.step_of_due` and 3 more |
| `Kernel.setCell` | proved | through `Kernel.apply`, `Kernel.boot` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 24 more |
| `Kernel.abs` | proved | `Kernel.WellFormed.quiet_iff`, `Kernel.WellFormed.wait_forever`, `Kernel.abs_boot` and 7 more |
| `Kernel.env` | proved | `Kernel.abs_boot`, `Kernel.accept_sound`, `Kernel.exec_reachable` and 4 more |
| `Kernel.unschedule` | proved | through `Kernel.apply`, `Kernel.boot` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 24 more |
| `Kernel.perform` | proved | through `Kernel.apply`, `Kernel.boot` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 24 more |
| `Kernel.performAll` | proved | through `Kernel.apply`, `Kernel.boot` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 24 more |
| `Kernel.down` | proved | through `Kernel.apply`, `Kernel.boot` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 24 more |
| `Kernel.settle` | proved | through `Kernel.apply`, `Kernel.boot` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 24 more |
| `Kernel.rest` | proved | through `Kernel.apply`, `Kernel.exec` and 4 more: `Batch.run_handed`, `Batch.run_kernel` and 22 more |
| `Kernel.handle` | proved | through `Kernel.apply`, `Kernel.exec` and 4 more: `Batch.run_handed`, `Batch.run_kernel` and 22 more |
| `Kernel.startActor` | proved | through `Kernel.apply`, `Kernel.boot` and 4 more: `Batch.run_handed`, `Batch.run_kernel` and 23 more |
| `Kernel.boot` | proved | `Http.kernel_fronted_answered_le_arrived`, `Http.kernel_served_answered_le_arrived`, `Journal.recover_kernel` and 6 more |
| `Kernel.accept` | proved | `Kernel.accept_sound` |
| `Kernel.run1` | proved | `Kernel.run1_sound` |
| `Kernel.fire` | proved | `Kernel.fire_sound` |
| `Kernel.advance` | proved | through `Kernel.apply`, `Kernel.exec`: `Batch.run_handed`, `Batch.run_kernel` and 13 more |
| `Kernel.timerNext` | proved | through `Kernel.apply`, `Kernel.exec` and 2 more: `Batch.run_handed`, `Batch.run_kernel` and 20 more |
| `Kernel.step` | proved | `Kernel.WellFormed.runBatch_of_due`, `Kernel.WellFormed.step_events_ne_nil`, `Kernel.WellFormed.step_of_due` and 1 more |
| `Kernel.wait` | proved | `Kernel.WellFormed.step_events_ne_nil`, `Kernel.WellFormed.wait_for_ms`, `Kernel.WellFormed.wait_forever` and 1 more |
| `Kernel.runBatch` | proved | `Kernel.WellFormed.runBatch`, `Kernel.WellFormed.runBatch_of_due`, `Kernel.runBatch_outputs` and 1 more |
| `Kernel.quiet` | proved | `Batch.run_resolved`, `Kernel.WellFormed.quiet_iff` |
| `Kernel.image` | proved | `Batch.flush_save`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and 4 more |
| `Kernel.Image.kernel` | proved | `Batch.flush_save`, `Kernel.WellFormed.image`, `Kernel.abs_image_kernel` |
| `Kernel.apply` | proved | `Kernel.WellFormed.apply` |
| `Kernel.exec` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.settle_kernel` and 11 more |

## `Lanes/Actors/KernelSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.outputs` | spec | used only in statements |

## `Lanes/Actors/KernelTimers.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.Serves` | spec | a predicate |
| `Kernel.Fires` | spec | a predicate |

## `Lanes/Actors/Lossy.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `EnvModel.lossy` | spec | used only in statements |

## `Lanes/Actors/Mailbox.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Mailbox.offer` | proved | `Mailbox.Reachable.offer_full_iff` |
| `Mailbox.offerOrWait` | proved | through `Mailbox.Op.apply`, `Mailbox.boundedIn` and 2 more: `Mailbox.after_close`, `Mailbox.batch_since_take` and 3 more |
| `Mailbox.take` | proved | `Mailbox.Reachable.asleep_empty`, `Mailbox.batch_since_take`, `Mailbox.close_since_take` and 2 more |
| `Mailbox.rest` | proved | `Mailbox.rest_eq_false`, `Mailbox.woken_after_rest` |
| `Mailbox.close` | proved | `Mailbox.after_close`, `Mailbox.close_since_take` |

## `Lanes/Actors/MailboxSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Mailbox.Op.apply` | spec | used only in statements |
| `Mailbox.exec` | spec | used only in statements |
| `Mailbox.Reachable` | spec | a predicate |
| `Mailbox.Reply.admitted` | spec | used only in statements |
| `Mailbox.Reply.woken` | spec | used only in statements |
| `Mailbox.Op.boundedIn` | spec | used only in statements |
| `Mailbox.Op.waitedIn` | spec | used only in statements |
| `Mailbox.Op.resetsSleeper` | spec | used only in statements |
| `Mailbox.boundedIn` | spec | used only in statements |
| `Mailbox.waitedIn` | spec | used only in statements |

## `Lanes/Actors/MapIOSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Envelope.over` | spec | used only in statements |
| `Envelope.under` | spec | used only in statements |
| `EnvModel.under` | spec | used only in statements |
| `SysState.over` | spec | used only in statements |
| `Event.Under` | spec | a predicate |
| `Event.AllUnder` | spec | a predicate |

## `Lanes/Actors/Monotone.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `SysState.grow` | proved | `Account.Moves.grow`, `Account.Moves.handle`, `Account.implements` and 7 more |
| `SysState.Pending` | spec | a predicate |

## `Lanes/Actors/Outside.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Outside.any` | tested | `Tests/Jobs.lean` |
| `Outside.driver` | checked | `Tests/Clock.lean`, `Tests/HttpClient.lean`, `Tests/Jobs.lean` |
| `Outside.after` | tested | `Tests/Clock.lean`, `Tests/Fronted.lean`, `Tests/HttpClient.lean` and 2 more |
| `Outside.allows` | tested | `Tests/Clock.lean`, `Tests/Fronted.lean`, `Tests/HttpClient.lean` and 2 more |
| `Outside.both` | checked | `Tests/Clock.lean`, `Tests/HttpClient.lean`, `Tests/Jobs.lean` |

## `Lanes/Actors/Past.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Ghost.past` | spec | used only in statements |
| `System.withPast` | spec | used only in statements |
| `SysState.seen` | spec | used only in statements |

## `Lanes/Actors/Release.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.awake` | spec | used only in statements |
| `SysState.Same` | spec | a predicate |
| `SysState.release` | spec | used only in statements |
| `SysState.Leads` | spec | a predicate |

## `Lanes/Actors/Run.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Effect.sends` | proved | `Account.Moves.grow`, `Account.Moves.handle` |
| `Effect.armed` | none |  |
| `Effect.emits` | none |  |
| `Effect.retime` | spec | used only in statements |
| `Event.quiet` | spec | used only in statements |
| `SysState.startedWith` | spec | used only in statements |
| `SysState.started` | spec | used only in statements |

## `Lanes/Actors/Runtime.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Runtime.running` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.startWith` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.start` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.input` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.tryInput` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.idle` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.trace` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.state` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.stop` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.ended` | trusted | TRUSTED.md: The runtime shell |

## `Lanes/Actors/Scheduler.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Driver.silent` | checked | `Tests/Election.lean` |
| `Driver.script` | checked | `Tests/KV.lean` |
| `Driver.anyOrder` | checked | `Tests/Bank.lean`, `Tests/Batch.lean`, `Tests/Clients.lean` and 3 more |
| `World.init` | checked | `Tests/Bank.lean` |
| `World.next` | proved | `World.Equiv.next` |
| `simulate` | checked | `Tests/Bank.lean` |

## `Lanes/Actors/Service.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.start` | none |  |
| `Service.State.call` | none |  |
| `Service.apply` | none |  |
| `Service.State.ret` | none |  |
| `Service.State.fire` | none |  |

## `Lanes/Actors/Shard.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `shardSig` | proved | through `Event.merged?`, `Event.unsharded?`: `Shards.AtHome.step`, `SysState.AtHome.step` |
| `shardEffect` | tested | `Tests/Fronted.lean`, `Tests/Peers.lean` |
| `System.shard` | tested | `Tests/Fronted.lean`, `Tests/Peers.lean` |
| `Parcel.payload` | proved | `Parcel.receive_send` |
| `Parcel.ofPayload` | proved | through `Parcel.receive`: `Parcel.receive_send` |
| `Parcel.fits` | proved | `Parcel.receive_send` |
| `Parcel.send` | proved | `Parcel.receive_send` |
| `Parcel.receive` | proved | `Parcel.receive_send` |

## `Lanes/Actors/ShardSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instHashableSigma_lanes` | tested | `Tests/Split.lean` |
| `Signature.Inspect.shard` | tested | `Tests/Split.lean` |
| `System.Inspect.shard` | tested | `Tests/Split.lean` |
| `splitSig` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and 5 more |
| `shardWiring` | proved | through `System.split`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `System.split` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and 5 more |
| `Signature.Inspect.split` | tested | `Tests/Split.lean` |
| `System.Inspect.split` | tested | `Tests/Split.lean` |
| `Split.actorOf` | proved | through `EnvModel.split`, `Event.merged?` and 1 more: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Split.home` | spec | used only in statements |
| `Split.atHome` | proved | through `EnvModel.split`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 1 more |
| `Split.route` | tested | `Tests/Split.lean` |
| `Split.output?` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Split.msgOf` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Envelope.merged` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Envelope.atHome` | tested | `Tests/Split.lean` |
| `Event.merged?` | spec | used only in statements |
| `Event.routed` | proved | `SysState.AtHome.step` |
| `EnvModel.split` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.SplitReachable.merged_of_init` |
| `SysState.merged` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and 5 more |
| `System.SteadyBoot` | spec | a predicate |

## `Lanes/Actors/ShardsSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `joinAllSig` | proved | through `shardsSig`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `joinAllEffect` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `System.joinAll` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `shardsSig` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and 4 more |
| `shardsRoute` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `System.shards` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and 4 more |
| `Signature.Inspect.joinAll` | tested | `Tests/Split.lean` |
| `System.Inspect.joinAll` | tested | `Tests/Split.lean` |
| `Signature.Inspect.shards` | tested | `Tests/Split.lean` |
| `System.Inspect.shards` | tested | `Tests/Split.lean` |
| `Shards.atHome` | proved | through `EnvModel.shards`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 1 more |
| `Shards.route` | tested | `Tests/Split.lean` |
| `Shards.output?` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `Shards.routed` | proved | `Shards.AtHome.step` |
| `Envelope.unsharded` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `Envelope.atHomeAll` | tested | `Tests/Split.lean` |
| `Event.unsharded?` | spec | used only in statements |
| `EnvModel.shards` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.ShardsReachable.unsharded_of_init` |
| `SysState.unsharded` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and 4 more |
| `Shards.effect` | spec | used only in statements |

## `Lanes/Actors/Snapshot.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.Due.codec` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.cell` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.envelope` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.image` | proved | its type, `Codec` |
| `Journal.savedHeader` | proved | through `Journal.savedRecords`: `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and 1 more |
| `Journal.savedRecords` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` |
| `Journal.saved` | tested | `Tests/Durable.lean` |
| `Journal.saved?` | none |  |

## `Lanes/Actors/System.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Effect.isStop` | none |  |
| `Effect.instDecidableEq` | proved | its type, `Decidable` |
| `Envelope.instDecidableEq` | proved | `Account.Moves.handle`, `Account.implements`, `System.Refines.of_events` and 3 more |
| `Envelope.sameLink` | none |  |
| `Link.reliable` | proved | `Examples.Watchdog.exists_fair_run_never_barks`, `Examples.Watchdog.impatient_barks` |
| `Link.network` | checked | `Tests/Bank.lean`, `Tests/Election.lean`, `Tests/Join.lean` and 1 more |
| `Link.unordered` | checked | `Tests/Election.lean`, `Tests/Jobs.lean` |
| `EnvModel.reliable` | spec | used only in statements |
| `EnvModel.distributed` | none |  |

## `Lanes/Actors/World.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `update` | proved | through `SysState.down`, `SysState.init` and 4 more: `Account.implements`, `Check.system_violated` and 36 more |
| `Event.timed` | spec | used only in statements |
| `Event.visible` | spec | used only in statements |
| `SysState.blank` | proved | `System.Inductive.of_monotone`, `System.Monotone.and` |
| `SysState.hasMail` | proved | through `SysState.run`, `SysState.step` and 1 more: `Check.system_violated`, `Http.Gate.answered_le_handled` and 24 more |
| `SysState.perform` | proved | through `SysState.init`, `SysState.run` and 3 more: `Account.implements`, `Check.system_violated` and 35 more |
| `SysState.performAll` | proved | through `SysState.init`, `SysState.run` and 3 more: `Account.implements`, `Check.system_violated` and 35 more |
| `SysState.down` | proved | `Account.implements`, `System.Refines.of_events`, `linkMsgs_down` |
| `SysState.settle` | proved | `SysState.Loses.settle` |
| `SysState.handle` | proved | through `SysState.run`, `SysState.step` and 1 more: `Check.system_violated`, `Http.Gate.answered_le_handled` and 24 more |
| `SysState.startActor` | proved | through `SysState.init`, `SysState.run` and 2 more: `Account.implements`, `Check.system_violated` and 34 more |
| `SysState.deliverable` | proved | `Account.implements`, `System.Refines.of_events`, `linkMsgs_of_deliverable` |
| `SysState.step` | proved | `Http.Gate.answered_of_leaves`, `Http.Gate.deadline_not_restarted`, `Shards.AtHome.step` and 7 more |
| `SysState.init` | proved | `Account.implements`, `Check.system_violated`, `Http.Gate.answered_le_handled` and 19 more |
| `SysState.run` | proved | `Check.system_violated`, `Http.Gate.answered_le_handled`, `Http.fronted_answered_le_arrived` and 12 more |
| `System.Invariant` | spec | a predicate |

## `Lanes/Auth/Login.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Auth.instDecidableEqDigest` | proved | its type, `Decidable` |
| `Auth.instHashableDigest` | none |  |
| `Auth.instReprDigest` | none |  |
| `Auth.Digest.codec` | proved | its type, `Codec` |
| `Auth.instCodableDigest` | proved | its type, `Codable` |
| `Auth.Digest.hex` | tested | `Tests/Auth.lean` |
| `Auth.Digest.ofHex?` | tested | `Tests/Auth.lean` |
| `Auth.Password.salt` | tested | `Tests/Auth.lean` |
| `Auth.Password.digest` | tested | `Tests/Auth.lean` |
| `Auth.Attempts.codec` | proved | its type, `Codec` |
| `Auth.instCodableAttempts` | proved | its type, `Codable` |
| `Auth.Attempts.fail` | tested | `Tests/Auth.lean` |
| `Auth.Attempts.succeed` | tested | `Tests/Auth.lean` |
| `Auth.Attempts.unlock` | none |  |
| `Auth.Attempts.Bounded` | spec | a predicate |
| `Auth.Sessions.codec` | proved | its type, `Codec` |
| `Auth.instCodableSessions` | proved | its type, `Codable` |
| `Auth.Sessions.start` | tested | `Tests/Auth.lean` |
| `Auth.Sessions.close` | tested | `Tests/Auth.lean` |
| `Auth.Sessions.live` | tested | `Tests/Auth.lean` |

## `Lanes/Auth/Token.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hmac.Key.of` | tested | `Tests/Auth.lean` |
| `Hmac.Key.mac` | tested | `Tests/Auth.lean` |
| `Auth.tag` | tested | `Tests/Auth.lean` |
| `Auth.sign` | tested | `Tests/Auth.lean` |
| `Auth.verify` | tested | `Tests/Auth.lean` |
| `Auth.formToken` | tested | `Tests/Auth.lean` |
| `Auth.checkForm` | tested | `Tests/Auth.lean` |

## `Lanes/Behaviours/Jobs.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jobs.Phase.codec` | proved | its type, `Codec` |
| `Jobs.instCodablePhase` | proved | its type, `Codable` |
| `Jobs.Active.codec` | proved | its type, `Codec` |
| `Jobs.instCodableActive` | proved | its type, `Codable` |
| `Jobs.Outcome.codec` | proved | its type, `Codec` |
| `Jobs.instCodableOutcome` | proved | its type, `Codable` |
| `Jobs.Input.codec` | proved | its type, `Codec` |
| `Jobs.instCodableInput` | proved | its type, `Codable` |
| `Jobs.Output.codec` | proved | its type, `Codec` |
| `Jobs.instCodableOutput` | proved | its type, `Codable` |
| `Jobs.Msg.codec` | proved | its type, `Codec` |
| `Jobs.instCodableMsg` | proved | its type, `Codable` |
| `Jobs.Config.slots` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.Config.cap` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.Config.backoff` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.keys` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.attach_active_leaves` |
| `Jobs.entry` | proved | `Jobs.answer_of_leaves`, `Jobs.entry_step`, `Jobs.not_arms` and 1 more |
| `Jobs.put` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.remove` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.Within` | spec | a predicate |
| `Jobs.Attempts` | spec | a predicate |
| `Jobs.sig` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.actor_attempts` and 11 more |
| `Jobs.timer` | proved | `Jobs.not_arms` |
| `Jobs.fail` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.step` | proved | `Jobs.answer_of_leaves`, `Jobs.dispatch_active`, `Jobs.entry_step` and 2 more |
| `Jobs.rearm` | proved | through `Jobs.actor`, `Jobs.attach` and 1 more: `Jobs.active_answered`, `Jobs.active_leaves` and 8 more |
| `Jobs.actor` | proved | `Jobs.actor_attempts`, `Jobs.actor_within` |
| `Jobs.system` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.answered_le_handled` and 3 more |
| `Jobs.Use.wiring` | proved | through `Jobs.attach`: `Jobs.attach_active_leaves`, `Jobs.attach_within` |
| `Jobs.attach` | proved | `Jobs.attach_active_leaves`, `Jobs.attach_within` |
| `Jobs.pool` | checked | `Tests/Jobs.lean` |

## `Lanes/Behaviours/JobsSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jobs.left` | spec | used only in statements |
| `Jobs.Moved` | spec | a predicate |
| `Jobs.Armed` | spec | a predicate |
| `Jobs.answered` | spec | used only in statements |
| `Jobs.handled` | spec | used only in statements |

## `Lanes/Behaviours/Once.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Once.Memo.find?` | proved | through `Once.server`: `Once.server_implements` |
| `Once.Memo.record` | proved | through `Once.server`: `Once.server_implements` |
| `Once.Memo.seen` | proved | through `Once.server`: `Once.server_implements` |
| `Once.actor` | proved | through `Once.server`: `Once.server_implements` |
| `Once.server` | proved | `Once.server_implements` |

## `Lanes/Behaviours/Server.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Server.sig` | proved | `Once.server_implements`, `Server.implements` |
| `Server.actor` | proved | through `Server.system`: `Server.implements` |
| `Server.system` | proved | `Server.implements` |

## `Lanes/Check/Clients.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Driver.after` | checked | `Tests/Clients.lean` |

## `Lanes/Check/EquivDecide.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Matches` | spec | a predicate |

## `Lanes/Check/Fuzz.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.FuzzReport.ok` | checked | `Tests/Election.lean` |
| `Check.fuzz` | checked | `Tests/Election.lean` |
| `Check.FuzzReport.render` | none |  |

## `Lanes/Check/Monitor.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.State.equiv` | proved | through `Check.Monitor.after`, `Check.Monitor.candidates` and 2 more: `Check.Monitor.beq_iff_abs_eq`, `Check.Monitor.complete` and 5 more |
| `Service.State.hash` | proved | through `Check.Monitor.instHashable`: `Check.refines_sound`, `Check.refines_traces` |
| `Service.State.Distinct` | spec | a predicate |
| `Check.Monitor.insertAll` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.expand` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.freshFrom` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.closeStep` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.rounds` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.close` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.ok` | proved | `Check.Monitor.ok_iff`, `Check.refines_sound` |
| `Check.Monitor.instBEq` | proved | `Check.Monitor.beq_iff_abs_eq`, `Check.refines_sound`, `Check.refines_traces` and 1 more |
| `Check.Monitor.instHashable` | proved | `Check.refines_sound`, `Check.refines_traces` |
| `Check.Monitor.start` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.input` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.output` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.fire` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Service.monitored` | proved | `Check.refines_sound`, `Check.refines_traces`, `Service.monitored_respects` |
| `Check.refines` | proved | `Check.refines_sound`, `Check.refines_traces` |

## `Lanes/Check/MonitorEquiv.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Monitor.Within` | spec | a predicate |

## `Lanes/Check/Once.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.insertNew` | checked | `Tests/KV.lean` |
| `Check.sameSet` | checked | `Tests/KV.lean` |
| `Check.setHash` | checked | `Tests/KV.lean` |
| `Check.OnceState.equiv` | checked | `Tests/KV.lean` |
| `Check.OnceState.take` | checked | `Tests/KV.lean` |
| `Check.OnceState.hash` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.insertAll` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.expand` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.close` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.ok` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.instBEq` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.instHashable` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.start` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.input` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.output` | checked | `Tests/KV.lean` |
| `Check.refinesOnce` | checked | `Tests/KV.lean` |
| `Service.onceMonitored` | checked | `Tests/KV.lean` |

## `Lanes/Check/Search.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Property.name` | proved | `Check.search_unreached` |
| `Check.Property.holds` | proved | `Check.refines_sound`, `Check.refines_traces`, `Check.system_sound` and 1 more |
| `Check.Trace.last` | proved | `Check.search_deadlock`, `Check.search_reached`, `Check.search_violated` and 2 more |
| `Check.Trace.labels` | proved | `Check.system_violated` |
| `Check.Report.ok` | checked | `Tests/Bank.lean`, `Tests/Batch.lean`, `Tests/Clients.lean` and 13 more |
| `Check.Path.last` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Path.toTraceAux` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Path.toTrace` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.violation` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.witnessFor` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.witness` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.unwitnessed` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 8 more |
| `Check.Hashed.of` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Hashed.instBEq` | proved | through `Check.Search`, `Check.search`: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Hashed.instHashable` | proved | through `Check.Search`, `Check.search`: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.add` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.contains` | checked | `Tests/Join.lean` |
| `Check.Search.addInit` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 8 more |
| `Check.Search.start` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 8 more |
| `Check.Search.visit` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.successors` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.expandWith` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.expand` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.run` | proved | `Check.Search.explore_eq`, `Check.Search.runBatches_eq` |
| `Check.Search.expandAll` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.mapInTasks` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.taskSize` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.batchSize` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 10 more |
| `Check.Search.runBatches` | proved | `Check.Search.runBatches_eq` |
| `Check.Search.explore` | proved | `Check.Search.explore_eq` |
| `Check.Search.report` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 8 more |
| `Check.search` | proved | `Check.search_deadlock`, `Check.search_deadlock_free`, `Check.search_reached` and 7 more |

## `Lanes/Check/SearchSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Model.Steps` | spec | a predicate |
| `Check.Trace.Valid` | spec | a predicate |
| `Check.Path.Valid` | spec | a predicate |
| `Check.Failure.Found` | spec | a predicate |
| `Check.Search.Stored` | spec | a predicate |
| `Check.Search.Live` | spec | a predicate |

## `Lanes/Check/System.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Node.of` | proved | `Scenario.reachable_iff` |
| `Check.instBEqNodeOfInspect` | proved | `Check.Node.beq_iff` |
| `Check.instHashableNodeOfInspect` | proved | through `Check.system`: `Check.refines_sound`, `Check.refines_traces` and 3 more |
| `Check.Trace.map` | proved | through `Check.system`: `Check.refines_sound`, `Check.refines_traces` and 3 more |
| `Check.Report.map` | proved | through `Check.system`: `Check.refines_sound`, `Check.refines_traces` and 3 more |
| `Check.model` | proved | `Scenario.reachable_iff` |
| `Check.system` | proved | `Check.refines_sound`, `Check.refines_traces`, `Check.system_sound` and 2 more |
| `Check.Trace.render` | checked | `Tests/Election.lean` |
| `Check.Report.render` | checked | `Tests/Election.lean` |
| `Check.Report.renderSystem` | checked | `Tests/Election.lean` |

## `Lanes/Check/SystemSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.isInternal` | none |  |
| `World.quiet` | spec | used only in statements |

## `Lanes/Data/Base64.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Base64.Alphabet.last` | proved | through `Base64.decode`, `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 4 more |
| `Base64.Alphabet.code` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 2 more |
| `Base64.Alphabet.char` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 2 more |
| `Base64.Alphabet.valueOf` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.Alphabet.value?` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.Encoding.std` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.rawStd` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.url` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.rawUrl` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.sextet` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 2 more |
| `Base64.byte` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.pad` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 2 more |
| `Base64.encodeList` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 2 more |
| `Base64.full` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.tail1` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.tail2` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.decodeList` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.encode` | proved | `Base64.allowed_of_mem_encode`, `Base64.decode_encode`, `Base64.decode_eq_some_iff` and 1 more |
| `Base64.decode` | proved | `Base64.decode_encode`, `Base64.decode_eq_none_of_length`, `Base64.decode_eq_none_of_not_allowed` and 1 more |
| `Base64.Encoding.Allowed` | spec | a predicate |
| `Base64.encodedLength` | spec | used only in statements |

## `Lanes/Data/Civil.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Civil.isLeap` | proved | through `Civil.Date.toDays`, `Civil.DateTime` and 1 more: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 3 more |
| `Civil.daysInMonth` | proved | through `Civil.Date.toDays`, `Civil.DateTime` and 1 more: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 3 more |
| `Civil.Valid` | spec | a predicate |
| `Civil.instDecidableValid` | proved | its type, `Decidable` |
| `Civil.Date.mk?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Civil.marchMonth` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.ofMarchMonth` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.daysBefore` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.marchLength` | spec | used only in statements |
| `Civil.dayOfEra` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.daysFrom` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.Date.toDays` | proved | `Civil.ofDays_toDays`, `Civil.toDays_ofDays` |
| `Civil.yearOfEra` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.civilOf` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.civil` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 2 more |
| `Civil.LongYear` | spec | a predicate |
| `Civil.Date.ofDays` | proved | `Civil.ofDays_toDays`, `Civil.toDays_ofDays` |
| `Civil.Date.weekday` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Civil.TimeOfDay.seconds` | proved | through `Civil.DateTime.toUnix`: `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` |
| `Civil.TimeOfDay.ofSeconds` | proved | through `Civil.DateTime.ofUnix`: `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` |
| `Civil.DateTime.toUnix` | proved | `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` |
| `Civil.DateTime.ofUnix` | proved | `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` |

## `Lanes/Data/Codec.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Codec.bytes` | proved | its type, `Codec` |
| `Codec.unit` | proved | its type, `Codec` |
| `Codec.string` | proved | its type, `Codec` |
| `Codec.nat` | proved | its type, `Codec` |
| `Codec.pair` | proved | its type, `Codec` |
| `Codec.map` | proved | its type, `Codec` |
| `Codec.sigma` | proved | its type, `Codec` |
| `Codec.subtype` | proved | its type, `Codec` |
| `Codec.bool` | proved | its type, `Codec` |
| `Codec.fin` | proved | its type, `Codec` |
| `Codec.int` | proved | its type, `Codec` |
| `Codec.sum` | proved | its type, `Codec` |
| `Codec.option` | proved | its type, `Codec` |
| `Codec.readMany` | tested | `Tests/Codec.lean`, `Tests/Durable.lean` |
| `Codec.list` | proved | its type, `Codec` |
| `Codec.extTreeMap` | proved | its type, `Codec` |
| `Codable.instByteArray` | proved | its type, `Codable` |
| `Codable.instUnit` | proved | its type, `Codable` |
| `Codable.instString` | proved | its type, `Codable` |
| `Codable.instNat` | proved | its type, `Codable` |
| `Codable.instBool` | proved | its type, `Codable` |
| `Codable.instInt` | proved | its type, `Codable` |
| `Codable.instFin` | proved | its type, `Codable` |
| `Codable.instOption` | proved | its type, `Codable` |
| `Codable.instList` | proved | its type, `Codable` |
| `Codable.instProd` | proved | its type, `Codable` |
| `Codable.instSum` | proved | its type, `Codable` |
| `Codable.instSubtypeOfDecidablePred` | proved | its type, `Codable` |
| `Codable.instSigma` | proved | its type, `Codable` |
| `Codable.instExtTreeMapOfTransCmpOfLawfulEqCmp` | proved | its type, `Codable` |
| `Codec.of` | proved | its type, `Codec` |
| `Codec.fresh` | none |  |
| `Codec.tuple` | none |  |
| `Codec.product` | none |  |
| `Codec.inject` | none |  |

## `Lanes/Data/Declare.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Enum.ofEquiv` | proved | its type, `Enum` |
| `Declare.params` | none |  |
| `Declare.classBinders` | none |  |
| `Declare.productType` | none |  |
| `Declare.sumType` | none |  |
| `Declare.splitDeriving` | none |  |
| `Declare.leanDeriving` | none |  |
| `Declare.codable` | none |  |
| `Declare.conjunction` | none |  |
| `Declare.fieldwise` | none |  |
| `Declare.comparedByBEq` | none |  |
| `Declare.independent` | none |  |
| `Declare.enum` | none |  |

## `Lanes/Data/Digits.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Digits.join` | proved | `Digits.join_split` |
| `Digits.split` | proved | `Digits.join_split` |
| `Digits.digits` | proved | through `Digits.toChars`: `Digits.head_toChars`, `Digits.ofChars?_toChars` |
| `Digits.char` | proved | through `Digits.fixed`, `Digits.toChars`: `Digits.head_toChars`, `Digits.ofChars?_fixed` and 1 more |
| `Digits.valueOf` | proved | through `Digits.ofChars?`: `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.value?` | proved | through `Digits.ofChars?`: `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.lower` | spec | used only in statements |
| `Digits.values?` | proved | through `Digits.ofChars?`: `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.ofChars?` | proved | `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.toChars` | proved | `Digits.head_toChars`, `Digits.ofChars?_toChars` |
| `Digits.fixed` | proved | `Digits.ofChars?_fixed` |

## `Lanes/Data/Enum.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Enum.instEmpty` | proved | its type, `Enum` |
| `Enum.instUnit` | proved | its type, `Enum` |
| `Enum.instBool` | proved | its type, `Enum` |
| `Enum.instFin` | proved | its type, `Enum` |
| `Enum.instOption` | proved | its type, `Enum` |
| `Enum.instSum` | proved | its type, `Enum` |
| `Enum.instProd` | proved | its type, `Enum` |
| `Enum.instSubtypeOfDecidablePred` | proved | its type, `Enum` |
| `Enum.funBEq` | checked | `Tests/Clients.lean`, `Tests/KV.lean` |
| `Enum.funHashable` | checked | `Tests/Clients.lean`, `Tests/KV.lean` |
| `Enum.funRepr` | checked | `Tests/Clients.lean`, `Tests/KV.lean` |

## `Lanes/Data/Fifo.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Fifo.toList` | proved | `Kernel.WellFormed.step_of_queued` |
| `Fifo.push` | none |  |
| `Fifo.pop?` | none |  |
| `Fifo.filter` | none |  |
| `Fifo.length` | proved | `Peers.Courier.Reachable.queue_le` |
| `Fifo.isEmpty` | checked | `Tests/Courier.lean`, `Tests/Kernel.lean`, `Tests/Release.lean` |

## `Lanes/Data/Frame.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Frame.fits` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` and 4 more |
| `Frame.checksum` | proved | `Frame.decode_checksum_ne` |
| `Frame.stamped` | proved | `Frame.decode_checksum_ne` |
| `Frame.one` | proved | through `Frame.encode`: `Frame.decode_checksum_ne`, `Frame.decode_encode` and 4 more |
| `Frame.encode` | proved | `Frame.decode_checksum_ne`, `Frame.decode_encode`, `Frame.decode_take` and 3 more |
| `Frame.decode` | proved | `Frame.decode_checksum_ne`, `Frame.decode_encode`, `Frame.decode_extract_prefix` and 3 more |
| `Frame.whole` | proved | `Frame.decode_take_eq`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and 3 more |
| `Frame.span` | proved | `Journal.open?_cut`, `Parcel.receive_send` |
| `Frame.unfinished` | none |  |

## `Lanes/Data/Hmac.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hmac.blockOf` | tested | `Tests/Crypto.lean` |
| `Hmac.Pads.of` | tested | `Tests/Crypto.lean` |
| `Hmac.reference` | tested | `Tests/Crypto.lean` |
| `Bytes.sameReference` | tested | `Tests/Crypto.lean` |
| `Bytes.hexDigit` | tested | `Tests/Crypto.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` and 1 more |
| `Bytes.hex` | tested | `Tests/Crypto.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` and 1 more |
| `Bytes.nibble?` | tested | `Tests/Crypto.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Bytes.unhexList` | tested | `Tests/Crypto.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Bytes.unhex?` | tested | `Tests/Crypto.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |

## `Lanes/Data/Ip.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Ip.octet?` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.parse4` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.print4` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 2 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 3 more |
| `Ip.hexGroup?` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.groups?` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.expand` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.fields?` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.parse6` | proved | through `Ip.Prefix.parse`, `Ip.parse`: `Ip.Prefix.parse_print`, `Ip.parse_print` |
| `Ip.parse` | proved | `Ip.parse_print` |
| `Ip.zeroRun` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.runAt` | proved | `Ip.longestZeroRun_none`, `Ip.longestZeroRun_some` |
| `Ip.longestZeroRun` | proved | `Ip.longestZeroRun_none`, `Ip.longestZeroRun_some` |
| `Ip.withEllipsis` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 2 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 3 more |
| `Ip.hexFields` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 2 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 3 more |
| `Ip.fields` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 2 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 3 more |
| `Ip.mappedPrefix` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 2 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 3 more |
| `Ip.print6` | proved | through `Ip.Prefix.bits`, `Ip.Prefix.masked` and 2 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 3 more |
| `Ip.print` | proved | `Ip.parse_print` |
| `Ip.Found` | spec | a predicate |
| `Ip.Addr.width` | proved | `Ip.Prefix.contains_iff` |
| `Ip.Addr.toNat` | spec | used only in statements |
| `Ip.mask` | proved | through `Ip.Prefix.contains`, `Ip.Prefix.masked`: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 1 more |
| `Ip.Addr.masked` | proved | through `Ip.Prefix.contains`, `Ip.Prefix.masked`: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 1 more |
| `Ip.Prefix.masked` | proved | `Ip.Prefix.contains_masked`, `Ip.Prefix.masked_masked` |
| `Ip.Prefix.contains` | proved | `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` |
| `Ip.Prefix.print` | proved | `Ip.Prefix.parse_print` |
| `Ip.decimal?` | proved | through `Ip.Prefix.parse`: `Ip.Prefix.parse_print` |
| `Ip.Prefix.parse` | proved | `Ip.Prefix.parse_print` |

## `Lanes/Data/Json/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `JsonNumber.ofDecimal` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 1 more |
| `JsonNumber.fromInt` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 1 more |
| `JsonNumber.fromNat` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 1 more |
| `JsonNumber.ofScientific` | tested | `Tests/Json.lean` |
| `JsonNumber.instCoeNat` | none |  |
| `JsonNumber.instCoeInt` | none |  |
| `JsonNumber.instOfNat` | tested | `Tests/Json.lean` |
| `JsonNumber.instInhabited` | none |  |
| `JsonNumber.instOfScientific` | tested | `Tests/Json.lean` |
| `JsonNumber.instNeg` | tested | `Tests/Json.lean` |
| `JsonNumber.instHashable` | tested | `Tests/Json.lean` |
| `JsonNumber.toInt?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `JsonNumber.toNat?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `JsonNumber.maxLeadingZeros` | none |  |
| `JsonNumber.toString` | none |  |
| `JsonNumber.instToString` | none |  |
| `JsonNumber.instRepr` | tested | `Tests/Json.lean` |
| `Json.decEq` | proved | its type, `Decidable` |
| `Json.decEqArray` | proved | its type, `Decidable` |
| `Json.decEqList` | proved | its type, `Decidable` |
| `Json.decEqFields` | proved | its type, `Decidable` |
| `Json.decEqFieldList` | proved | its type, `Decidable` |
| `Json.decEqField` | proved | its type, `Decidable` |
| `Json.instDecidableEq` | proved | its type, `Decidable` |
| `Json.hash` | tested | `Tests/Json.lean` |
| `Json.instHashable` | tested | `Tests/Json.lean` |
| `Json.reprPrec` | tested | `Tests/Json.lean` |
| `Json.instRepr` | tested | `Tests/Json.lean` |
| `Json.instCoeNat` | none |  |
| `Json.instCoeInt` | none |  |
| `Json.instCoeString` | none |  |
| `Json.instCoeBool` | none |  |
| `Json.instOfNat` | tested | `Tests/Json.lean` |
| `Json.sortFields` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 2 more |
| `Json.dedupFields` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 2 more |
| `Json.duplicateKey?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.mkObj` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 2 more |
| `Json.mkObj?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.isNull` | tested | `Tests/Json.lean` |
| `Json.getObj?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 1 more |
| `Json.getArr?` | tested | `Tests/Json.lean` |
| `Json.getStr?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.getNum?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Json.getNat?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Json.getInt?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Json.getBool?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.getObjVal?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 1 more |
| `Json.getArrVal?` | tested | `Tests/Json.lean` |
| `Json.getObjValD` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 1 more |

## `Lanes/Data/Json/Classes.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instFromJsonJson` | tested | `Tests/Json.lean` |
| `instToJsonJson` | tested | `Tests/Json.lean` |
| `instFromJsonJsonNumber` | tested | `Tests/Json.lean` |
| `instToJsonJsonNumber` | tested | `Tests/Json.lean` |
| `instFromJsonUnit` | tested | `Tests/Json.lean` |
| `instToJsonUnit` | tested | `Tests/Json.lean` |
| `instFromJsonBool` | tested | `Tests/Json.lean` |
| `instToJsonBool` | tested | `Tests/Json.lean` |
| `instFromJsonNat` | tested | `Tests/Json.lean` |
| `instToJsonNat` | tested | `Tests/Json.lean` |
| `instFromJsonInt` | tested | `Tests/Json.lean` |
| `instToJsonInt` | tested | `Tests/Json.lean` |
| `instFromJsonString` | tested | `Tests/Json.lean` |
| `instToJsonString` | tested | `Tests/Json.lean` |
| `instFromJsonFin` | tested | `Tests/Json.lean` |
| `instToJsonFin` | tested | `Tests/Json.lean` |
| `instFromJsonArray` | tested | `Tests/Json.lean` |
| `instToJsonArray` | tested | `Tests/Json.lean` |
| `instFromJsonList` | tested | `Tests/Json.lean` |
| `instToJsonList` | tested | `Tests/Json.lean` |
| `instFromJsonOption` | tested | `Tests/Json.lean` |
| `instToJsonOption` | tested | `Tests/Json.lean` |
| `instFromJsonProd` | tested | `Tests/Json.lean` |
| `instToJsonProd` | tested | `Tests/Json.lean` |
| `Json.getObjValAs?` | tested | `Tests/Json.lean` |
| `Json.opt` | tested | `Tests/Json.lean` |

## `Lanes/Data/Json/Parser.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Json.Parser.fail` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.next?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.accept` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.skipWsFrom` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.skipWs` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.acceptAll` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.hexDigit?` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.hexDigit` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.hex4` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.lowSurrogate` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.escape` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.strFrom` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.str` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.digitsFrom` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.whole` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.fraction` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.exponent` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.num` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.literal` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.key` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.value` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.Parser.elements` | spec | used only in statements |
| `Json.Parser.fields` | spec | used only in statements |
| `Json.Parser.document` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.parse` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |

## `Lanes/Data/Json/Printer.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Json.needsEscape` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.escapeChar` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.escape` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.renderString` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.separate` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.compressTo` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.compress` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` |
| `Json.newline` | tested | `Tests/Json.lean` |
| `Json.prettyTo` | tested | `Tests/Json.lean` |
| `Json.pretty` | tested | `Tests/Json.lean` |
| `Json.instToString` | none |  |

## `Lanes/Data/List/Prefix.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `afterFirst` | spec | used only in statements |

## `Lanes/Data/Quorum.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Quorum.isMajority` | proved | `Quorum.majority_inter` |

## `Lanes/Data/Sha256.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Sha256.roundConstants` | tested | `Tests/Crypto.lean` |
| `Sha256.initial` | tested | `Tests/Crypto.lean` |
| `Sha256.rotr` | tested | `Tests/Crypto.lean` |
| `Sha256.schedule` | tested | `Tests/Crypto.lean` |
| `Sha256.compress` | tested | `Tests/Crypto.lean` |
| `Sha256.wordAt` | tested | `Tests/Crypto.lean` |
| `Sha256.blockAt` | tested | `Tests/Crypto.lean` |
| `Sha256.padding` | tested | `Tests/Crypto.lean` |
| `Sha256.absorb` | tested | `Tests/Crypto.lean` |
| `Sha256.digestFrom` | tested | `Tests/Crypto.lean` |
| `Sha256.State.bytes` | tested | `Tests/Crypto.lean` |
| `Sha256.reference` | tested | `Tests/Crypto.lean` |

## `Lanes/Data/Sodium.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Sha256.hash` | trusted | TRUSTED.md: The C |
| `hmac` | trusted | TRUSTED.md: The C |
| `Bytes.same` | trusted | TRUSTED.md: The C |
| `randomBytes` | trusted | TRUSTED.md: The C |
| `Argon2id.hash` | trusted | TRUSTED.md: The C |

## `Lanes/Data/TimeFormat.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `TimeFormat.isDigit` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.num?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.Timestamp.toUnix` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `TimeFormat.d2` | proved | through `TimeFormat.printHttpDate?`, `TimeFormat.printRfc3339?`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.d4` | proved | through `TimeFormat.printHttpDate?`, `TimeFormat.printRfc3339?`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.clock` | proved | through `TimeFormat.printHttpDate?`, `TimeFormat.printRfc3339?`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.trimZeros` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.fractionChars` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.offsetChars` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.rfc3339Chars` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.InRange` | spec | a predicate |
| `TimeFormat.instDecidableInRange` | proved | its type, `Decidable` |
| `TimeFormat.printRfc3339?` | proved | `TimeFormat.parseRfc3339_print` |
| `TimeFormat.clock?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.fraction?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.offset?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.parseRfc3339` | proved | `TimeFormat.parseRfc3339_print` |
| `TimeFormat.dayNames` | proved | through `TimeFormat.printHttpDate?`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.longDayNames` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.monthNames` | proved | through `TimeFormat.printHttpDate?`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.nameOf?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.imfChars` | proved | through `TimeFormat.printHttpDate?`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.printHttpDate?` | proved | `TimeFormat.parseHttpDate_print` |
| `TimeFormat.checked` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.imf?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.fullYear` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.rfc850?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.asctime?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.parseHttpDate` | proved | `TimeFormat.parseHttpDate_print` |

## `Lanes/Env/Clock.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Clock.outside` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.latest` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.Wall.start` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.Wall.now` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.handler` | trusted | TRUSTED.md: The clock adapter's handler |

## `Lanes/Env/Http.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.serveWith` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.serveFronted` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.ServerConfig.journalName` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.serve` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.port` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.stop` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.inFlight` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.trace` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.wait` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.tryInput` | trusted | TRUSTED.md: The HTTP adapter's IO |

## `Lanes/Env/HttpClient.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Client.outside` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.exchange` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.handler` | trusted | TRUSTED.md: The HTTP client adapter's handler |

## `Lanes/Env/Jobs.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jobs.Port.alone` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.handler` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.compute` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.withHeader` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.call` | trusted | TRUSTED.md: The jobs pool |

## `Lanes/Env/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.fsync` | trusted | TRUSTED.md: The journal's files |
| `Journal.Store.open` | trusted | TRUSTED.md: The journal's files |

## `Lanes/Env/Node.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.serveShard` | trusted | TRUSTED.md: A process with a front and peers |

## `Lanes/Env/Peers.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.start` | trusted | TRUSTED.md: The transport between processes |
| `Peers.send` | trusted | TRUSTED.md: The transport between processes |
| `Peers.stop` | trusted | TRUSTED.md: The transport between processes |
| `Peers.shard` | trusted | TRUSTED.md: The transport between processes |

## `Lanes/Html/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Html.empty` | none |  |
| `Html.instInhabited` | none |  |
| `Html.escapeChar` | proved | through `Html.escape`: `Html.escape_safe` |
| `Html.escape` | proved | `Html.escape_safe` |
| `Html.safeName` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.voidTags` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.urlAttrs` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.blockedUrl` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.safeUrl` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.Attr.render` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.render` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.renderAll` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Html.classes` | tested | `Tests/Html.lean` |
| `Html.document` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToHtmlHtml` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToHtmlString` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToHtmlNat` | tested | `Tests/Html.lean` |
| `instToHtmlInt` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToHtmlList` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToHtmlArray` | none |  |
| `instToHtmlOption` | none |  |
| `instToAttrString` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToAttrListString` | tested | `Tests/Html.lean` |
| `instToAttrNat` | tested | `Tests/Html.lean` |
| `instToAttrInt` | none |  |
| `instToAttrBool` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `instToAttrOption` | none |  |

## `Lanes/Html/Htmx.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hx.methodAttr` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Hx.request` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Hx.target` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Hx.Swap.name` | tested | `Tests/Html.lean` |
| `Hx.swap` | tested | `Tests/Html.lean` |
| `Hx.eventName` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Hx.Trigger.render` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Hx.trigger` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Hx.confirm` | none |  |
| `Hx.boost` | none |  |
| `Hx.pushUrl` | none |  |
| `Hx.indicator` | none |  |
| `Http.Request.isHtmx` | none |  |
| `Http.Response.trigger` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Response.hxRedirect` | none |  |

## `Lanes/Http/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.reprBody` | checked | `Tests/HttpClient.lean` |
| `Http.Method.codec` | proved | its type, `Codec` |
| `Http.Request.codec` | proved | its type, `Codec` |
| `Http.hexValue?` | proved | through `Http.Request.hexByte`, `Http.percentDecode`: `Http.Request.read_badChunkSize`, `Http.percentDecode_percentEncode` |
| `Http.percentDecodeBytes` | proved | through `Http.percentDecode`: `Http.percentDecode_percentEncode` |
| `Http.percentDecode` | proved | `Http.percentDecode_percentEncode` |
| `Http.hexDigit` | proved | through `Http.percentEncode`: `Http.percentDecode_percentEncode` |
| `Http.unreserved` | proved | through `Http.percentEncode`: `Http.percentDecode_percentEncode` |
| `Http.percentEncodeByte` | proved | through `Http.percentEncode`: `Http.percentDecode_percentEncode` |
| `Http.percentEncode` | proved | `Http.percentDecode_percentEncode` |
| `Http.parseForm` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.encodeForm` | tested | `Tests/Html.lean` |
| `Http.Request.param?` | none |  |
| `Http.Request.header?` | none |  |
| `Http.Request.text?` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Request.form` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Request.field?` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Response.ofText` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `Http.Response.text` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `Http.Response.html` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Response.json` | none |  |
| `Http.Response.empty` | tested | `Tests/Auth.lean` |
| `Http.Response.redirect` | none |  |
| `Http.Response.withHeader` | none |  |

## `Lanes/Http/Cookie.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.SameSite.name` | tested | `Tests/Auth.lean` |
| `Http.cookieOctet` | tested | `Tests/Auth.lean` |
| `Http.Cookie.valid` | tested | `Tests/Auth.lean` |
| `Http.Cookie.header` | tested | `Tests/Auth.lean` |
| `Http.Cookie.expired` | tested | `Tests/Auth.lean` |
| `Http.parseCookies` | tested | `Tests/Auth.lean` |
| `Http.Request.cookies` | tested | `Tests/Auth.lean` |
| `Http.Request.cookie?` | tested | `Tests/Auth.lean` |
| `Http.Request.sameOrigin` | tested | `Tests/Auth.lean` |
| `Http.Request.bodyWithin` | none |  |
| `Http.Response.setCookie` | tested | `Tests/Auth.lean` |
| `Http.Response.clearCookie` | tested | `Tests/Auth.lean` |
| `Http.Response.noStore` | none |  |

## `Lanes/Http/Front.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.gateSig` | proved | `Http.Gate.answered_le_handled`, `Http.Gate.answered_of_leaves`, `Http.Gate.deadline_not_restarted` and 12 more |
| `Http.gateActor` | proved | `Http.gateActor_bounded` |
| `Http.gateSystem` | proved | `Http.Gate.answered_le_handled`, `Http.Gate.answered_of_leaves`, `Http.Gate.deadline_not_restarted` and 3 more |
| `Http.frontWiring` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and 10 more |
| `Http.frontedSig` | proved | `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup`, `Http.fronted_deadlines_armed` and 3 more |
| `Http.frontedInput` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and 10 more |
| `Http.frontedOutput` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and 10 more |
| `Http.fronted` | proved | `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup`, `Http.fronted_deadlines_armed` and 3 more |
| `Http.servedSig` | proved | `Http.kernel_served_answered_le_arrived`, `Http.served_answered_le_arrived`, `Http.served_answered_nodup` and 3 more |
| `Http.served` | proved | `Http.kernel_served_answered_le_arrived`, `Http.served_answered_le_arrived`, `Http.served_answered_nodup` and 3 more |
| `Signature.Inspect.gate` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `System.Inspect.gate` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `Signature.Inspect.fronted` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `System.Inspect.fronted` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `Signature.Inspect.served` | checked | `Tests/Gate.lean` |
| `System.Inspect.served` | checked | `Tests/Gate.lean` |
| `Http.Bridge.shard` | tested | `Tests/Fronted.lean` |
| `Http.frontedActors` | tested | `Tests/Fronted.lean` |
| `Http.servedActors` | none |  |
| `Http.frontedOutside` | tested | `Tests/Fronted.lean`, `Tests/Web.lean` |
| `Http.servedOutside` | tested | `Tests/Web.lean` |

## `Lanes/Http/FrontSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Gate.answered` | spec | used only in statements |
| `Http.Gate.handled` | spec | used only in statements |
| `Http.Gate.Armed` | spec | a predicate |
| `Http.Fronted.arrived` | spec | used only in statements |
| `Http.Fronted.answered` | spec | used only in statements |
| `Http.Fronted.Armed` | spec | a predicate |
| `Http.Served.arrived` | spec | used only in statements |
| `Http.Served.answered` | spec | used only in statements |
| `Http.Served.Armed` | spec | a predicate |

## `Lanes/Http/Gate.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.instHashableGateMsgOfOut` | proved | through `Http.Gate.step`: `Http.Gate.step_bounded` |
| `Http.instReprGateMsgOfOut` | none |  |
| `Http.busy` | proved | through `Http.Gate.step`: `Http.Gate.step_bounded` |
| `Http.timedOut` | proved | through `Http.Gate.step`: `Http.Gate.step_bounded` |
| `Http.Gate.step` | proved | `Http.Gate.step_bounded` |

## `Lanes/Http/ReadRequest.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Refusal.status` | tested | `Tests/ReadRequest.lean` |
| `Http.matchAt` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.find` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.pieces` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.Limits.message_max` | spec | used only in statements |
| `Http.Request.elements` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.version?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.method?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.pchar` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.targetChar` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.hostChar` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.segments?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.queryPart?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.pair?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.query?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.target?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.fieldLine?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.host?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.tabbedFraming` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.framing?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Request.readHead_headWire`, `Http.Request.read_append` and 12 more |
| `Http.Request.parseHead` | proved | `Http.Request.readHead_headWire` |
| `Http.Request.readHead` | proved | `Http.Request.readHead_headWire`, `Http.Request.read_badChunkSize` |
| `Http.Request.chunkSize` | proved | through `Http.Request.read`: `Http.Request.read_append`, `Http.Request.read_badChunkSize` and 11 more |
| `Http.Request.chunks` | proved | through `Http.Request.read`: `Http.Request.read_append`, `Http.Request.read_badChunkSize` and 11 more |
| `Http.Request.Head.close` | proved | through `Http.Request.read`: `Http.Request.read_append`, `Http.Request.read_badChunkSize` and 11 more |
| `Http.Request.Head.expectsContinue` | tested | `Tests/ReadRequest.lean` |
| `Http.Request.Head.incoming` | proved | through `Http.Request.read`: `Http.Request.read_append`, `Http.Request.read_badChunkSize` and 11 more |
| `Http.Request.read` | proved | `Http.Request.read_append`, `Http.Request.read_badChunkSize`, `Http.Request.read_bareCR` and 10 more |

## `Lanes/Http/ReadRequestSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Request.fits` | proved | `Http.Request.read_wire`, `Http.Request.read_wire_extract` |
| `Http.Request.sent` | proved | `Http.Request.read_wire` |
| `Http.Request.headWire` | spec | used only in statements |
| `Http.findL` | spec | used only in statements |
| `Http.encodedChar` | spec | used only in statements |
| `Http.Request.fieldName` | spec | used only in statements |
| `Http.Request.hexByte` | spec | used only in statements |

## `Lanes/Http/Route.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Segment.Clean` | spec | a predicate |
| `Http.instDecidableClean` | proved | its type, `Decidable` |
| `Http.Slug.ofString?` | tested | `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Slug.instToString` | none |  |
| `Http.Slug.instDecidableEq` | proved | its type, `Decidable` |
| `Http.Path.seg` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Path.slug` | tested | `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Path.nat` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Path.root` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Path.append` | none |  |
| `Http.Path.pre` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Route.get` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Route.post` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Route.put` | none |  |
| `Http.Route.patch` | none |  |
| `Http.Route.delete` | none |  |
| `Http.Route.match?` | proved | `Http.Route.match?_link` |
| `Http.Route.link` | tested | `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.Route.handle` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |
| `Http.dispatch` | tested | `Tests/Fronted.lean`, `Tests/Html.lean`, `Tests/Web.lean` |

## `Lanes/Http/Waiting.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Waiting.start` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.wait` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.releases` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.release` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.answer` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.drain` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.Trace.apply` | spec | used only in statements |
| `Http.Waiting.exec` | spec | used only in statements |

## `Lanes/Http/Wire.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.tokenChar` | proved | through `Http.Request.fields`, `Http.Request.wire` and 2 more: `Http.Request.fields_framing`, `Http.Request.head_plain` and 14 more |
| `Http.token` | proved | through `Http.Request.fields`, `Http.Request.wire` and 2 more: `Http.Request.fields_framing`, `Http.Request.head_plain` and 14 more |
| `Http.plain` | proved | `Http.Request.head_plain` |
| `Http.visible` | proved | through `Http.Request.wire`: `Http.Request.head_plain`, `Http.Request.read_wire` and 1 more |
| `Http.ows` | proved | `Http.Request.read_blankInName` |
| `Http.frames` | proved | `Http.Request.fields_framing` |
| `Http.Request.target` | proved | through `Http.Request.wire`: `Http.Request.head_plain`, `Http.Request.read_wire` and 1 more |
| `Http.Request.kept` | proved | through `Http.Request.fields`, `Http.Request.wire`: `Http.Request.fields_framing`, `Http.Request.head_plain` and 2 more |
| `Http.Request.fields` | proved | `Http.Request.fields_framing` |
| `Http.Request.head` | proved | `Http.Request.head_plain` |
| `Http.Request.wire` | proved | `Http.Request.head_plain`, `Http.Request.read_wire`, `Http.Request.read_wire_extract` |
| `Http.Reading.map` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.headEnd` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.crlf` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.skip` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.hex` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.chunkSizeDigits_max` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.chunkExtensionBytes_max` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.sizeLineEnd` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.chunkHead` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.dechunk` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.decimal?` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.splitLines` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.statusLine?` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.trimOws` | proved | through `Http.Request.fieldName`, `Http.Response.read` and 1 more: `Http.Request.read_lengthAndCoding`, `Http.Request.read_twoLengths` and 12 more |
| `Http.headerLine?` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.head?` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.framing?` | proved | through `Http.Response.read`, `Http.readFrom`: `Http.Response.read_append`, `Http.Response.read_ended` and 10 more |
| `Http.readFrom` | proved | `Http.Response.read_some` |
| `Http.Response.read` | proved | `Http.Response.read_append`, `Http.Response.read_ended`, `Http.Response.read_more` and 9 more |
| `Http.Response.parse` | trusted | TRUSTED.md: The HTTP wire format |

## `Lanes/Http/WireSpec.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Response.kept` | proved | through `Http.Response.writable`: `Http.Response.read_wire`, `Http.Response.read_wireAfter` and 6 more |
| `Http.Response.lowered` | proved | `Http.Response.read_wire`, `Http.Response.read_wireAfter`, `Http.Response.read_wireChunked` and 1 more |
| `Http.Response.writable` | proved | `Http.Response.read_wire`, `Http.Response.read_wireAfter`, `Http.Response.read_wireAfter_extract` and 5 more |
| `Http.Response.headWire` | proved | through `Http.Response.wire`, `Http.Response.wireAfter` and 2 more: `Http.Response.read_wire`, `Http.Response.read_wireAfter` and 6 more |
| `Http.Response.wire` | proved | `Http.Response.read_wire`, `Http.Response.read_wire_extract` |
| `Http.Response.chunk` | proved | through `Http.Response.wireChunked`: `Http.Response.read_wireChunked`, `Http.Response.read_wireChunked_extract` |
| `Http.Response.wireChunked` | proved | `Http.Response.read_wireChunked`, `Http.Response.read_wireChunked_extract` |
| `Http.Response.interim` | proved | `Http.Response.read_wireAfter`, `Http.Response.read_wireAfter_extract` |
| `Http.Response.wireAfter` | proved | `Http.Response.read_wireAfter`, `Http.Response.read_wireAfter_extract` |
| `Http.Response.wireToEnd` | proved | `Http.Response.read_wireToEnd`, `Http.Response.read_wireToEnd_open` |

## `Lanes/Semantics/Account.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.run` | spec | used only in statements |
| `Account.pending` | proved | `Account.Moves.of_le` |
| `Account.owed` | proved | `Account.Moves.of_le` |
| `Account.Sim` | spec | a predicate |
| `Account.Moves` | spec | a predicate |
| `Account.Handles` | spec | a predicate |

## `Lanes/Semantics/FairJoin.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Obligation.inl` | spec | used only in statements |
| `Wiring.leftView` | spec | used only in statements |
| `SysState.unhidden` | spec | used only in statements |
| `SysState.hidden` | spec | used only in statements |
| `System.underView` | spec | used only in statements |

## `Lanes/Semantics/FairRuns.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Obligation.instDecidableDue` | proved | its type, `Decidable` |
| `FairScheduler.Complete` | spec | a predicate |
| `System.fairChoice` | spec | used only in statements |
| `System.fairSchedule` | spec | used only in statements |
| `System.Run.fairAfter` | spec | used only in statements |

## `Lanes/Semantics/Link.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Envelope.on` | spec | used only in statements |
| `linkMsgs` | spec | used only in statements |

## `Lanes/Semantics/Liveness.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Spec.stutter` | proved | through `System.Run`, `System.Run.event` and 2 more: `Examples.Watchdog.exists_fair_run_never_barks`, `Examples.Watchdog.impatient_barks` and 13 more |
| `Obligation.event` | proved | `System.LeadsTo.ensures_of_invariant` |
| `Obligation.Due` | spec | a predicate |
| `Obligation.Restarted` | spec | a predicate |
| `System.Run.idle` | none |  |
| `System.Run.Restarts` | spec | a predicate |
| `System.Run.WeakFair` | spec | a predicate |
| `System.Run.Fair` | spec | a predicate |
| `System.Run.Impatient` | spec | a predicate |
| `System.LeadsTo` | spec | a predicate |

## `Lanes/Semantics/Monitor.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.State.toAbs` | proved | `Check.Monitor.complete`, `Check.Monitor.sound` |
| `Check.Monitor.observe` | spec | used only in statements |
| `Check.Monitor.after` | spec | used only in statements |

## `Lanes/Semantics/MonitorSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Monitor.abs` | spec | used only in statements |

## `Lanes/Semantics/Once.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.Once.take` | spec | used only in statements |
| `Service.once` | spec | used only in statements |
| `System.ImplementsOnce` | spec | a predicate |
| `Once.Server.Covered` | spec | a predicate |

## `Lanes/Semantics/Projection.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.Run.blockStart` | spec | used only in statements |
| `System.Run.blockOf` | spec | used only in statements |
| `System.Run.ofBlocks` | spec | used only in statements |
| `SysState.RestartsAlong` | spec | a predicate |

## `Lanes/Semantics/Refinement.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Spec.lts` | proved | `Check.Monitor.complete`, `Check.Monitor.ok_iff`, `Check.Monitor.sound` and 8 more |
| `Spec.Reachable` | spec | a predicate |
| `Spec.Invariant` | spec | a predicate |
| `Refines` | spec | a predicate |

## `Lanes/Semantics/Service.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.spec` | proved | `Account.implements`, `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 8 more |
| `Service.Stable` | spec | a predicate |
| `Service.Only` | spec | a predicate |
| `Service.Took` | spec | a predicate |
| `System.Implements` | spec | a predicate |
| `Server.abs` | spec | used only in statements |

## `Lanes/Semantics/Simulation.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.Stops` | spec | a predicate |

## `Lanes/Semantics/System.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.sem` | proved | `Account.implements`, `Examples.KV.caching_not_implements`, `Examples.KV.implements` and 12 more |
| `System.Refines` | spec | a predicate |

## `LanesCli/Generated.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Generated.instAppendPlan` | none |  |
| `Cli.Generated.lineCount` | none |  |
| `Cli.Generated.readIfExists` | none |  |
| `Cli.Generated.sortStrings` | none |  |
| `Cli.Generated.charsFrom` | none |  |
| `Cli.Generated.occursIn` | tested | `Tests/Lint.lean` |
| `Cli.Generated.replaceName` | tested | `Tests/Lint.lean` |
| `Cli.Generated.writeIfChanged` | none |  |
| `Cli.Generated.stale` | none |  |
| `Cli.Generated.markdownIn` | none |  |
| `Cli.Generated.parseCount` | none |  |
| `Cli.Generated.isTrustedSource` | none |  |
| `Cli.Generated.trustedSizes` | none |  |
| `Cli.Generated.rewriteSizes` | none |  |
| `Cli.Generated.withCommas` | tested | `Tests/Lint.lean` |
| `Cli.Generated.roundedTotal` | tested | `Tests/Lint.lean` |
| `Cli.Generated.rewriteTotal` | none |  |
| `Cli.Generated.trustedPlan` | none |  |
| `Cli.Generated.decisionsDir` | none |  |
| `Cli.Generated.parseDecisionName` | none |  |
| `Cli.Generated.parseHeading` | none |  |
| `Cli.Generated.readDecisions` | none |  |
| `Cli.Generated.indexLine` | none |  |
| `Cli.Generated.indexText` | none |  |
| `Cli.Generated.textFiles` | none |  |
| `Cli.Generated.numberPlan` | none |  |
| `Cli.Generated.decisionsPlan` | none |  |
| `Cli.Generated.statusDir` | none |  |
| `Cli.Generated.rowsMarker?` | none |  |
| `Cli.Generated.limitsMarker` | none |  |
| `Cli.Generated.generatedNote` | tested | `Tests/Lint.lean` |
| `Cli.Generated.splitFragment` | none |  |
| `Cli.Generated.statusPlan` | none |  |
| `Cli.Generated.plan` | none |  |
| `Cli.Generated.Edit.describe` | none |  |
| `Cli.Generated.apply` | none |  |
| `Cli.Generated.fix` | none |  |

## `LanesCli/Inventory.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Inventory.Status.label` | none |  |
| `Cli.Inventory.Status.all` | none |  |
| `Cli.Inventory.inventoryFile` | none |  |
| `Cli.Inventory.noneFile` | none |  |
| `Cli.Inventory.sortStrings` | none |  |
| `Cli.Inventory.moduleOfPath` | none |  |
| `Cli.Inventory.pathOfModule` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.modulesIn` | none |  |
| `Cli.Inventory.imports` | none |  |
| `Cli.Inventory.gates` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.trustedRows` | none |  |
| `Cli.Inventory.owner` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.shapeOf` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.specTypes` | none |  |
| `Cli.Inventory.reportTypes` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.libraryRoots` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isLibrary` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.ranges` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.inDeriving` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.generatedParsers` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.ofTheorem` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.readFacts` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isProp` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isType` | none |  |
| `Cli.Inventory.usersOf` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.specs` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.covers` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.statement` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.provedBy` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isOutside` | none |  |
| `Cli.Inventory.reach` | none |  |
| `Cli.Inventory.exercised` | none |  |
| `Cli.Inventory.display` | none |  |
| `Cli.Inventory.listOf` | none |  |
| `Cli.Inventory.entries` | none |  |
| `Cli.Inventory.area` | none |  |
| `Cli.Inventory.cell` | none |  |
| `Cli.Inventory.summary` | none |  |
| `Cli.Inventory.render` | none |  |
| `Cli.Inventory.allowed` | none |  |
| `Cli.Inventory.check` | none |  |
| `Cli.Inventory.load` | none |  |
| `Cli.Inventory.counts` | none |  |
| `Cli.Inventory.run` | none |  |

## `LanesCli/Lint.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Lint.stripCommentsAndStrings` | tested | `Tests/Lint.lean` |
| `Cli.Lint.isWordChar` | tested | `Tests/Lint.lean` |
| `Cli.Lint.hasWord` | tested | `Tests/Lint.lean` |
| `Cli.Lint.trustedWords` | tested | `Tests/Lint.lean` |
| `Cli.Lint.proofDirs` | tested | `Tests/Lint.lean` |
| `Cli.Lint.isProofFile` | tested | `Tests/Lint.lean` |
| `Cli.Lint.importsProofModule` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkFile` | tested | `Tests/Lint.lean` |
| `Cli.Lint.sourceFiles` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkC` | tested | `Tests/Lint.lean` |
| `Cli.Lint.codeSpans` | tested | `Tests/Lint.lean` |
| `Cli.Lint.firstBraces` | tested | `Tests/Lint.lean` |
| `Cli.Lint.expandBraces` | tested | `Tests/Lint.lean` |
| `Cli.Lint.citedPaths` | tested | `Tests/Lint.lean` |
| `Cli.Lint.citingDocs` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkLinks` | tested | `Tests/Lint.lean` |
| `Cli.Lint.parseFinding` | tested | `Tests/Lint.lean` |
| `Cli.Lint.inventory` | tested | `Tests/Lint.lean` |
| `Cli.Lint.lint` | tested | `Tests/Lint.lean` |
| `Cli.Lint.run` | none |  |

## `LanesCli/Main.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `usage` | none |  |
| `flag?` | none |  |
| `main` | none |  |

## `LanesCli/New.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.New.Source.toToml` | none |  |
| `Cli.New.moduleName` | none |  |
| `Cli.New.validName` | none |  |
| `Cli.New.files` | none |  |
| `Cli.New.fill` | none |  |
| `Cli.New.run` | none |  |
