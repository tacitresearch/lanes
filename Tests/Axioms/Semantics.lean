/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Semantics/`. -/

-- Lanes.Semantics.FairJoin
/-- info: 'Lanes.Wiring.leftView_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Wiring.leftView_projects

/-- info: 'Lanes.System.Run.Fair.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.left

/-- info: 'Lanes.System.LeadsTo.join_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.join_left

/-- info: 'Lanes.System.underView_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.underView_projects

/-- info: 'Lanes.System.LeadsTo.filterMapIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.filterMapIO

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

-- Lanes.Semantics.FrontLive
/-- info: 'Lanes.Http.Gate.pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.pending_leaves

/-- info: 'Lanes.Http.Gate.pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.pending_answered

/-- info: 'Lanes.Http.fronted_pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_pending_leaves

/-- info: 'Lanes.Http.fronted_pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_pending_answered

-- Lanes.Semantics.GateLive
/-- info: 'Lanes.Http.deadline_not_restarted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.deadline_not_restarted

/-- info: 'Lanes.Http.pending_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.pending_leaves

/-- info: 'Lanes.Http.answered_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.answered_of_leaves

/-- info: 'Lanes.Http.pending_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.pending_answered

-- Lanes.Semantics.Liveness
/-- info: 'Lanes.System.LeadsTo.ensures_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.ensures_of_invariant

/-- info: 'Lanes.System.LeadsTo.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.LeadsTo.trans

/-- info: 'Lanes.System.Run.Fair.output_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Fair.output_taken

/-- info: 'Lanes.System.Run.Impatient.fair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Run.Impatient.fair

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

/-- info: 'Lanes.System.Refines.of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.of_steps

-- Lanes.Semantics.System
/-- info: 'Lanes.System.reachable_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.reachable_iff

/-- info: 'Lanes.System.Refines.traces_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Refines.traces_of_run
