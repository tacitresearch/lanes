/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Behaviours/`. -/

-- Lanes.Behaviours.Jobs
/-- info: 'Lanes.Jobs.actor_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.actor_within

/-- info: 'Lanes.Jobs.actor_attempts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.actor_attempts

/-- info: 'Lanes.Jobs.dispatch_active' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.dispatch_active

/-- info: 'Lanes.Jobs.retry_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jobs.retry_same

-- Lanes.Behaviours.JobsSound
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
