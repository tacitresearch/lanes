import Ledger.Proofs.Book
import Ledger.Proofs.Actors

/-!
The axiom gate (rule 5.5): each headline theorem depends only on Lean's three standard axioms.
If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Ledger.book_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ledger.book_invariant

/-- info: 'Ledger.serve_onlyOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ledger.serve_onlyOf

/-- info: 'Ledger.serve_from_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ledger.serve_from_owner

/-- info: 'Ledger.user_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ledger.user_bounded

/-- info: 'Lanes.Auth.verify_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_sign

/-- info: 'Lanes.Bytes.same_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Bytes.same_iff
