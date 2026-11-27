/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Outside/`. -/

-- Lanes.Outside.Basic
/-- info: 'Lanes.Outside.after_invariant' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Outside.after_invariant

/-- info: 'Lanes.Outside.after_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Outside.after_both

-- Lanes.Outside.Rpc
/-- info: 'Lanes.Rpc.server_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Rpc.server_invariant

/-- info: 'Lanes.Rpc.answered_le_called' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Rpc.answered_le_called

-- Lanes.Outside.Idempotent
/-- info: 'Lanes.Idempotent.keys_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Idempotent.keys_nodup

/-- info: 'Lanes.Idempotent.at_most_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Idempotent.at_most_once

/-- info: 'Lanes.Idempotent.answer_repeat' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Idempotent.answer_repeat

-- Lanes.Outside.ObjectStore
/-- info: 'Lanes.ObjectStore.read_sent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.ObjectStore.read_sent

-- Lanes.Outside.Events
/-- info: 'Lanes.Events.deliveries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Events.deliveries_le

-- Lanes.Outside.Effects.Basic
/-- info: 'Lanes.Effects.at_most_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.at_most_once

-- Lanes.Outside.Effects.Payments
/-- info: 'Lanes.Payments.final' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Payments.final

-- Lanes.Outside.Effects.Email
/-- info: 'Lanes.Email.final' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Email.final

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

-- Lanes.Outside.Clock
/-- info: 'Lanes.Clock.outside_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Clock.outside_ge

/-- info: 'Lanes.Clock.wall_latest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Clock.wall_latest_le

/-- info: 'Lanes.Clock.wall_back_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Clock.wall_back_le

-- Lanes.Outside.Queue
/-- info: 'Lanes.Queue.received_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Queue.received_le

/-- info: 'Lanes.Queue.fifo_received_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Queue.fifo_received_le

/-- info: 'Lanes.Queue.deleted_not_received' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Queue.deleted_not_received

-- Lanes.Outside.Cache
/-- info: 'Lanes.Cache.fill_unleased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Cache.fill_unleased

/-- info: 'Lanes.Cache.read_sent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Cache.read_sent

-- Lanes.Outside.Throttle
/-- info: 'Lanes.Throttle.throttled_inner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Throttle.throttled_inner

/-- info: 'Lanes.Throttle.within_not_throttled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Throttle.within_not_throttled

/-- info: 'Lanes.Throttle.wait_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Throttle.wait_le
