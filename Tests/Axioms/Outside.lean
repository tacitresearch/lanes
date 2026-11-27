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
