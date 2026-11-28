import Chat.Proofs

/-!
The axiom gate (rule 5.5): each headline theorem depends only on Lean's three standard axioms.
If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Chat.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chat.implements

/-- info: 'Chat.system_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chat.system_bounded

/-- info: 'Chat.step_say' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chat.step_say

/-- info: 'Chat.step_leave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Chat.step_leave
