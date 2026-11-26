/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Election
import RaftKV.Proofs.Log
import RaftKV.Proofs.Commit
import RaftKV.Proofs.Applied

/-!
The axiom gate (rule 5.5). Each headline theorem may depend only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one of them, this file stops compiling.
-/

/-- info: 'RaftKV.election_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.election_safety

/-- info: 'RaftKV.electionSafety_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.electionSafety_invariant

/-- info: 'RaftKV.one_leader_per_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.one_leader_per_term

/-- info: 'RaftKV.applied_le_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.applied_le_commit

/-- info: 'RaftKV.appliedWithinCommit_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.appliedWithinCommit_invariant

/-- info: 'RaftKV.entryTermsWithinTerm_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.entryTermsWithinTerm_invariant

/-- info: 'RaftKV.entry_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.entry_term_le

/-- info: 'RaftKV.append_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.append_bounded

/-- info: 'RaftKV.appendsBounded_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.appendsBounded_invariant

/-- info: 'RaftKV.leader_append_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.leader_append_only

/-- info: 'RaftKV.leader_log_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.leader_log_grows

/-- info: 'RaftKV.log_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.log_matching

/-- info: 'RaftKV.logMatching_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.logMatching_invariant

/-- info: 'RaftKV.leader_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.leader_completeness

/-- info: 'RaftKV.committed_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.committed_chosen

/-- info: 'RaftKV.commit_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.commit_le_length

/-- info: 'RaftKV.commitWithinLog_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.commitWithinLog_invariant

/-- info: 'RaftKV.committed_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.committed_agree

/-- info: 'RaftKV.committedAgree_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.committedAgree_invariant

/-- info: 'RaftKV.leader_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.leader_complete

/-- info: 'RaftKV.leaderComplete_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.leaderComplete_invariant

/-- info: 'RaftKV.step_serves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.step_serves

/-- info: 'RaftKV.recover_serves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.recover_serves

/-- info: 'RaftKV.applied_eq_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.applied_eq_commit

/-- info: 'RaftKV.machine_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.machine_eq_run

/-- info: 'RaftKV.applied_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.applied_agree

/-- info: 'RaftKV.applied_agree_over_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.applied_agree_over_time

/-- info: 'RaftKV.applied_same_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.applied_same_entry

/-- info: 'RaftKV.requests_from_clients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.requests_from_clients

/-- info: 'RaftKV.requestsFromClients_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.requestsFromClients_invariant

/-- info: 'RaftKV.appliedAllCommitted_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.appliedAllCommitted_invariant

/-- info: 'RaftKV.machinesRun_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RaftKV.machinesRun_invariant
