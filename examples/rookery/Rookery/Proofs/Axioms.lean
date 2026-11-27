import Rookery.Proofs.Refines

/-!
The axiom gate (rule 5.5): each headline theorem depends only on Lean's three standard axioms.
If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Rookery.Board.run_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.run_keeps

/-- info: 'Rookery.Board.handle_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.handle_accepts

/-- info: 'Rookery.Board.handle_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.handle_keeps

/-- info: 'Rookery.Board.handle_get?_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.handle_get?_ne

/-- info: 'Rookery.Board.gone_of_removed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.gone_of_removed

/-- info: 'Rookery.Board.Gone.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.Gone.run

/-- info: 'Rookery.Board.handle_feed_gone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.handle_feed_gone

/-- info: 'Rookery.Board.mem_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.mem_feed

/-- info: 'Rookery.Board.mem_timeline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.mem_timeline

/-- info: 'Rookery.Board.sorted_timeline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.sorted_timeline

/-- info: 'Rookery.Board.length_timeline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.length_timeline

/-- info: 'Rookery.Board.timeline_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.timeline_complete

/-- info: 'Rookery.Board.rate_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.rate_limit

/-- info: 'Rookery.Board.handle_api_again' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.handle_api_again

/-- info: 'Rookery.Board.handle_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.handle_secret

/-- info: 'Rookery.Board.Bounded.handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.Board.Bounded.handle

/-- info: 'Rookery.board_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.board_invariant

/-- info: 'Rookery.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rookery.implements
