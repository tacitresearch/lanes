/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Reminders.Proofs

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Reminders.keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reminders.keeps

/-- info: 'Reminders.delivered_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reminders.delivered_committed

/-- info: 'Reminders.delivered_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reminders.delivered_once
