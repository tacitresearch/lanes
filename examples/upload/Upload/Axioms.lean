import Upload.Proofs

/-!
The axiom gate (rule 5.5): each headline theorem depends only on Lean's three standard axioms.
If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Upload.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Upload.implements

/-- info: 'Upload.system_uploads_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Upload.system_uploads_le

/-- info: 'Upload.step_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Upload.step_piece

/-- info: 'Upload.take_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Upload.take_take

/-- info: 'Upload.start_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Upload.start_take
