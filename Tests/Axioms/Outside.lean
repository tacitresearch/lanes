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

/-- info: 'Lanes.Outside.run_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Outside.run_induction

-- Lanes.Outside.Rpc
/-- info: 'Lanes.Rpc.allow_answer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Rpc.allow_answer

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

/-- info: 'Lanes.ObjectStore.held_sent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.ObjectStore.held_sent

-- Lanes.Outside.Events
/-- info: 'Lanes.Events.deliveries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Events.deliveries_le

-- Lanes.Outside.Effects.Basic
/-- info: 'Lanes.Effects.at_most_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.at_most_once

/-- info: 'Lanes.Effects.Lifecycle.reaches_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.Lifecycle.reaches_terminal

/-- info: 'Lanes.Effects.sound_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.sound_after

/-- info: 'Lanes.Effects.Sound.allow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.Sound.allow

/-- info: 'Lanes.Effects.Sound.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.Sound.observe

/-- info: 'Lanes.Effects.Sound.shows_reply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.Sound.shows_reply

/-- info: 'Lanes.Effects.Sound.shows_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.Sound.shows_report

/-- info: 'Lanes.Effects.allow_requests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.allow_requests

/-- info: 'Lanes.Effects.observe_routes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Effects.observe_routes

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

-- Lanes.Outside.FileSystem.Basic
/-- info: 'Lanes.FileSystem.Fs.crash_mem_crashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.Fs.crash_mem_crashes

-- Lanes.Outside.FileSystem.Replace
/-- info: 'Lanes.FileSystem.Replace.crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.Replace.crash

/-- info: 'Lanes.FileSystem.Replace.failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.Replace.failed

/-- info: 'Lanes.FileSystem.Replace.done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.Replace.done

-- Lanes.Outside.FileSystem.Log
/-- info: 'Lanes.FileSystem.Log.crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.Log.crash

/-- info: 'Lanes.FileSystem.Log.failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.Log.failed

-- Lanes.Outside.FileSystem
/-- info: 'Lanes.FileSystem.server_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.FileSystem.server_same

-- Lanes.Outside.Environment
/-- info: 'Lanes.Environment.Reader.run_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Environment.Reader.run_bind

/-- info: 'Lanes.Environment.Reader.run_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Environment.Reader.run_congr

/-- info: 'Lanes.Environment.secret_problems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Environment.secret_problems

/-- info: 'Lanes.Environment.field_secret_problems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Environment.field_secret_problems
