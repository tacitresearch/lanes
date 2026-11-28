import Rookery.Proofs

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Rookery.others_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.others_kept

/-- info: 'Rookery.bounded_always' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.bounded_always

/-- info: 'Rookery.handler_name' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.handler_name

/-- info: 'Rookery.api_again' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.api_again
