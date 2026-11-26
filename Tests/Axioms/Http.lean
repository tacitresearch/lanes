/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Http/`. -/

-- Lanes.Http.Basic
/-- info: 'Lanes.Http.percentDecode_percentEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.percentDecode_percentEncode

-- Lanes.Http.Front
/-- info: 'Lanes.Http.gateActor_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.gateActor_bounded

-- Lanes.Http.FrontSound
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

/-- info: 'Lanes.Http.served_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_answered_le_arrived

/-- info: 'Lanes.Http.served_answered_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_answered_nodup

/-- info: 'Lanes.Http.kernel_served_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.kernel_served_answered_le_arrived

/-- info: 'Lanes.Http.served_deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_deadlines_armed

-- Lanes.Http.Gate
/-- info: 'Lanes.Http.Gate.step_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.step_bounded

-- Lanes.Http.Route
/-- info: 'Lanes.Http.Route.match?_link' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Http.Route.match?_link

-- Lanes.Http.Waiting
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

-- Lanes.Http.Wire
/-- info: 'Lanes.Http.Request.fields_framing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.fields_framing

/-- info: 'Lanes.Http.Request.head_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.head_plain

/-- info: 'Lanes.Http.Response.read_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_ended

-- Lanes.Http.WireSound
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
