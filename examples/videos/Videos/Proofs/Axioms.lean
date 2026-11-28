/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Proofs.Gone
import Videos.Proofs.Confirmed
import Videos.Proofs.Likes
import Videos.Proofs.Private
import Videos.Proofs.Jobs
import Videos.Proofs.Ready
import Videos.Proofs.Reads

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Videos.private_to_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.private_to_owner

/-- info: 'Videos.Site.read_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.read_private

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

/-- info: 'Videos.Site.shows_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.shows_read

/-- info: 'Videos.Site.quiet_handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.quiet_handle

/-- info: 'Videos.jobs_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.jobs_bounded

/-- info: 'Videos.job_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.job_ends

/-- info: 'Videos.Site.delete_schedules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.delete_schedules

/-- info: 'Videos.Site.delete_reported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.delete_reported

/-- info: 'Videos.Site.listed_transcoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.listed_transcoded

/-- info: 'Videos.Site.report_names' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.report_names

/-- info: 'Videos.Site.report_leaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Site.report_leaves

/-- info: 'Videos.report_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.report_settles

/-- info: 'Videos.Web.view_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Videos.Web.view_answers
