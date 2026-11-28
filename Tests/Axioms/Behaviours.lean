/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Behaviours/`. -/

-- Lanes.Behaviours.Jobs.Basic
/-- info: 'Lanes.Jobs.actor_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.actor_within

/-- info: 'Lanes.Jobs.actor_attempts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.actor_attempts

/-- info: 'Lanes.Jobs.dispatch_active' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.dispatch_active

/-- info: 'Lanes.Jobs.retry_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.retry_same

-- Lanes.Behaviours.Jobs.Sound
/-- info: 'Lanes.Jobs.within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.within

/-- info: 'Lanes.Jobs.armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.armed

/-- info: 'Lanes.Jobs.answered_le_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.answered_le_handled

/-- info: 'Lanes.Jobs.attach_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.attach_within

/-- info: 'Lanes.Jobs.entry_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.entry_step

/-- info: 'Lanes.Jobs.not_arms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.not_arms

/-- info: 'Lanes.Jobs.answer_of_leaves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.answer_of_leaves

-- Lanes.Behaviours.Once.Check
/-- info: 'Lanes.Check.OnceMonitor.withinFrom_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.OnceMonitor.withinFrom_eq

-- Lanes.Behaviours.Schedule.Sound
/-- info: 'Lanes.Schedule.actor_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.actor_within

/-- info: 'Lanes.Schedule.actor_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.actor_attempts

/-- info: 'Lanes.Schedule.within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.within

/-- info: 'Lanes.Schedule.attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attempts

/-- info: 'Lanes.Schedule.armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.armed

/-- info: 'Lanes.Schedule.now_le_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.now_le_step

/-- info: 'Lanes.Schedule.dispatch_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.dispatch_due

/-- info: 'Lanes.Schedule.retry_waits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.retry_waits

/-- info: 'Lanes.Schedule.attempt_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attempt_ends

/-- info: 'Lanes.Schedule.succeeded_replied' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Schedule.succeeded_replied

/-- info: 'Lanes.Schedule.told_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.told_of_leaves

/-- info: 'Lanes.Schedule.leaves_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.leaves_answered

/-- info: 'Lanes.Schedule.calls_le_scheduled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.calls_le_scheduled

/-- info: 'Lanes.Schedule.attach_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schedule.attach_within
