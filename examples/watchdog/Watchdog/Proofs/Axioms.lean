/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Watchdog.Proofs

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Watchdog.exists_fair_run_never_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Watchdog.exists_fair_run_never_barks

/-- info: 'Watchdog.impatient_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Watchdog.impatient_barks
