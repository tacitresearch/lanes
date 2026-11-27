/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos

/-!
The axiom gate (Lanes rule 5.5): each theorem depends only on Lean's standard axioms. If a
`sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Videos.register_again' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.register_again

/-- info: 'Videos.register_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.register_lookup
