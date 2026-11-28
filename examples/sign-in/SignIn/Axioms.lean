/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SignIn

/-!
The axiom gate (Lanes rule 5.5): each theorem depends only on Lean's standard axioms. If a
`sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'SignIn.register_again' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SignIn.register_again

/-- info: 'SignIn.register_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SignIn.register_lookup
