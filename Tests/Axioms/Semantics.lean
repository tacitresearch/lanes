/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Semantics/`. -/

-- Lanes.Semantics.Account
/-- info: 'Lanes.Service.takes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Service.takes

/-- info: 'Lanes.Account.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.implements

/-- info: 'Lanes.Account.Moves.of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.Moves.of_le

/-- info: 'Lanes.Account.Moves.handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.Moves.handle

/-- info: 'Lanes.Account.Moves.grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.Moves.grow

/-- info: 'Lanes.Account.implements_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.implements_timed

/-- info: 'Lanes.Account.Holds.passes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.Holds.passes

/-- info: 'Lanes.Account.Fires.handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.Fires.handle

/-- info: 'Lanes.Account.Fires.grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Account.Fires.grow

-- Lanes.Semantics.FairJoin
/-- info: 'Lanes.Wiring.leftView_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Wiring.leftView_projects

/-- info: 'Lanes.System.Run.Fair.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.left

/-- info: 'Lanes.System.LeadsTo.join_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.join_left

/-- info: 'Lanes.Obligation.right?_inr' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Obligation.right?_inr

/-- info: 'Lanes.Obligation.Due.of_thinRight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Obligation.Due.of_thinRight

/-- info: 'Lanes.Wiring.rightView_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Wiring.rightView_projects

/-- info: 'Lanes.System.Run.Fair.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.right

/-- info: 'Lanes.System.LeadsTo.join_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.join_right

/-- info: 'Lanes.System.underView_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.underView_projects

/-- info: 'Lanes.System.LeadsTo.filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.filterMapIO

/-- info: 'Lanes.System.Run.Fair.handled_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.handled_right

/-- info: 'Lanes.System.Run.Fair.handled_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.handled_left

/-- info: 'Lanes.System.Run.Fair.routed_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.routed_right

/-- info: 'Lanes.System.Run.Fair.routed_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.routed_left

/-- info: 'Lanes.SysState.step_left_state' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.step_left_state

-- Lanes.Semantics.FairRuns
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

-- Lanes.Semantics.Front
/-- info: 'Lanes.Http.Gate.pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.pending_leaves

/-- info: 'Lanes.Http.Gate.pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.pending_answered

/-- info: 'Lanes.Http.fronted_pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_pending_leaves

/-- info: 'Lanes.Http.fronted_pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_pending_answered

/-- info: 'Lanes.Http.Gate.deadline_not_restarted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.deadline_not_restarted

/-- info: 'Lanes.Http.Gate.answered_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.answered_of_leaves

/-- info: 'Lanes.Http.served_pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_pending_leaves

/-- info: 'Lanes.Http.served_pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_pending_answered

/-- info: 'Lanes.Http.Gate.always_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.always_up

/-- info: 'Lanes.Http.fronted_gate_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_gate_up

/-- info: 'Lanes.Http.served_gate_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_gate_up

/-- info: 'Lanes.Http.fronted_handle_arrive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_handle_arrive

/-- info: 'Lanes.Http.served_handle_arrive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_handle_arrive

/-- info: 'Lanes.Http.fronted_arrival_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_arrival_answered

/-- info: 'Lanes.Http.served_arrival_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_arrival_answered

-- Lanes.Semantics.History
/-- info: 'Lanes.System.Implements.history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Implements.history

/-- info: 'Lanes.System.Implements.produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Implements.produced

-- Lanes.Semantics.Jobs
/-- info: 'Lanes.Jobs.active_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.active_leaves

/-- info: 'Lanes.Jobs.active_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.active_answered

/-- info: 'Lanes.Jobs.submitted_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.submitted_answered

/-- info: 'Lanes.Jobs.attach_active_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.attach_active_leaves

-- Lanes.Semantics.Link
/-- info: 'Lanes.linkMsgs_of_deliverable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.linkMsgs_of_deliverable

/-- info: 'Lanes.linkMsgs_erase_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.linkMsgs_erase_self

/-- info: 'Lanes.linkMsgs_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.linkMsgs_down

-- Lanes.Semantics.Liveness
/-- info: 'Lanes.System.LeadsTo.ensures_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.ensures_of_invariant

/-- info: 'Lanes.System.LeadsTo.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.trans

/-- info: 'Lanes.System.Run.Fair.output_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.output_taken

/-- info: 'Lanes.System.Run.Fair.delivered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.delivered

/-- info: 'Lanes.System.Run.Fair.handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.handled

/-- info: 'Lanes.System.Run.Impatient.fair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Impatient.fair

/-- info: 'Lanes.System.LeadsTo.induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.induction

/-- info: 'Lanes.System.LeadsTo.exists_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.exists_left

-- Lanes.Semantics.Monitor
/-- info: 'Lanes.Check.Monitor.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.sound

/-- info: 'Lanes.Check.Monitor.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.complete

/-- info: 'Lanes.Check.Monitor.ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.ok_iff

-- Lanes.Semantics.MonitorSound
/-- info: 'Lanes.Check.Monitor.beq_iff_abs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.beq_iff_abs_eq

/-- info: 'Lanes.Service.monitored_respects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Service.monitored_respects

/-- info: 'Lanes.Check.refines_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.refines_sound

/-- info: 'Lanes.Check.refines_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.refines_traces

-- Lanes.Semantics.Once
/-- info: 'Lanes.Once.server_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Once.server_implements

/-- info: 'Lanes.System.Refines.filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.filterMapIO

-- Lanes.Semantics.Projection
/-- info: 'Lanes.System.View.Projects.fair_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.View.Projects.fair_run

/-- info: 'Lanes.System.View.Projects.leadsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.View.Projects.leadsTo

-- Lanes.Semantics.Refinement
/-- info: 'Lanes.Refines.of_map' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_map

/-- info: 'Lanes.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Refines.trans

/-- info: 'Lanes.Refines.traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Refines.traces

-- Lanes.Semantics.Sent
/-- info: 'Lanes.System.traced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.traced

-- Lanes.Semantics.Service
/-- info: 'Lanes.Server.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Server.implements

-- Lanes.Semantics.Simulation
/-- info: 'Lanes.Refines.of_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_invariant

/-- info: 'Lanes.Refines.of_lift' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_lift

/-- info: 'Lanes.System.Refines.of_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_ghost

/-- info: 'Lanes.System.Refines.to_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.to_ghost

/-- info: 'Lanes.System.Refines.of_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_events

/-- info: 'Lanes.System.Refines.of_timed_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_timed_events

/-- info: 'Lanes.System.Refines.of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_steps

/-- info: 'Lanes.System.Refines.of_handles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_handles

-- Lanes.Semantics.System
/-- info: 'Lanes.System.reachable_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.reachable_iff

/-- info: 'Lanes.System.Refines.traces_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.traces_of_run

-- Lanes.Semantics.Schedule
/-- info: 'Lanes.Schedule.held_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.held_leaves

/-- info: 'Lanes.Schedule.held_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.held_ends

/-- info: 'Lanes.Schedule.every_noticed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.every_noticed

/-- info: 'Lanes.Schedule.attach_held_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attach_held_leaves

/-- info: 'Lanes.Schedule.attachBy_held_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attachBy_held_leaves

/-- info: 'Lanes.Schedule.attach_end_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attach_end_handled

/-- info: 'Lanes.Schedule.attach_answer_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attach_answer_handled
