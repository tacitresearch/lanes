/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Net/`. -/

-- Lanes.Net.CourierSound
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
