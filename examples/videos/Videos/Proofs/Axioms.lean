/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Gone
import Videos.Proofs.Confirmed
import Videos.Proofs.Likes
import Videos.Proofs.Private

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Videos.private_to_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.private_to_owner

/-- info: 'Videos.Site.handle_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.handle_private

/-- info: 'Videos.Site.deleted_never_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.deleted_never_served

/-- info: 'Videos.Site.Gone.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.Gone.run

/-- info: 'Videos.Site.listed_confirmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.listed_confirmed

/-- info: 'Videos.likes_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.likes_distinct

/-- info: 'Videos.count_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.count_distinct

/-- info: 'Videos.Site.shows_handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.shows_handle
