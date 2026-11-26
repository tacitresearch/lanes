/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Protocol
import RaftKV.Properties

/-!
What the proofs know of the step function: what its helpers leave alone, and what one step of a
node can do to its term, vote, role and log (`Moves`).
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] in
theorem isLeader_iff {s : Node N C M} :
    isLeader s = true ↔ ∃ matched, s.role = .leader matched := by
  unfold isLeader
  split <;> simp_all

section Helpers

variable (config : Config) (nodes : List N) (machine : Machine C R M) (self : N)

theorem applyCommitted_eq (s : Node N C M) :
    ∃ (m : M) (outs : List (Response R)), applyCommitted machine self s =
      ({ s with
          machine := m
          applied := s.applied + ((s.log.take s.commit).drop s.applied).length },
        outs.map (Effect.emit (σ := sig N C R) (self := self))) := by
  unfold applyCommitted
  generalize (s.log.take s.commit).drop s.applied = todo
  show ∃ m outs, List.foldl _
    (s, ([] : List (Response R)).map (Effect.emit (σ := sig N C R) (self := self))) todo = _
  generalize ([] : List (Response R)) = outs
  induction todo generalizing s outs with
  | nil => exact ⟨s.machine, outs, rfl⟩
  | cons entry todo ih =>
    rw [List.foldl_cons]
    by_cases horigin : entry.origin = self
    · obtain ⟨m, outs', h⟩ := ih { s with
        machine := (machine.apply s.machine entry.cmd).1, applied := s.applied + 1 }
        (outs ++ [⟨entry.req, (machine.apply s.machine entry.cmd).2⟩])
      refine ⟨m, outs', ?_⟩
      simp only [horigin, ite_true, List.map_append, List.map_cons, List.map_nil] at h ⊢
      rw [h]
      simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]
    · obtain ⟨m, outs', h⟩ := ih { s with
        machine := (machine.apply s.machine entry.cmd).1, applied := s.applied + 1 } outs
      refine ⟨m, outs', ?_⟩
      simp only [horigin, ite_false] at h ⊢
      rw [h]
      simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

@[simp] theorem applyCommitted_term (s : Node N C M) :
    (applyCommitted machine self s).1.term = s.term := by
  obtain ⟨m, outs, h⟩ := applyCommitted_eq machine self s
  rw [h]

@[simp] theorem applyCommitted_votedFor (s : Node N C M) :
    (applyCommitted machine self s).1.votedFor = s.votedFor := by
  obtain ⟨m, outs, h⟩ := applyCommitted_eq machine self s
  rw [h]

@[simp] theorem applyCommitted_log (s : Node N C M) :
    (applyCommitted machine self s).1.log = s.log := by
  obtain ⟨m, outs, h⟩ := applyCommitted_eq machine self s
  rw [h]

@[simp] theorem applyCommitted_commit (s : Node N C M) :
    (applyCommitted machine self s).1.commit = s.commit := by
  obtain ⟨m, outs, h⟩ := applyCommitted_eq machine self s
  rw [h]

@[simp] theorem applyCommitted_role (s : Node N C M) :
    (applyCommitted machine self s).1.role = s.role := by
  obtain ⟨m, outs, h⟩ := applyCommitted_eq machine self s
  rw [h]

theorem applyCommitted_applied_le (s : Node N C M) :
    (applyCommitted machine self s).1.applied ≤ max s.applied s.commit := by
  obtain ⟨m, outs, heq⟩ := applyCommitted_eq machine self s
  rw [heq]
  simp only [List.length_drop, List.length_take]
  omega

/-- The answers `applyCommitted` gives to clients. -/
def answers (s : Node N C M) : List (Response R) :=
  Effect.emits (applyCommitted machine self s).2

@[simp] theorem applyCommitted_snd (s : Node N C M) :
    (applyCommitted machine self s).2 =
      (answers machine self s).map (Effect.emit (σ := sig N C R) (self := self)) := by
  obtain ⟨m, outs, h⟩ := applyCommitted_eq machine self s
  rw [answers, h, Effect.emits_map_emit]

omit [DecidableEq C] in
theorem advanceCommit_eq (s : Node N C M) (matched : List (N × Nat)) :
    ∃ commit, s.commit ≤ commit ∧
      advanceCommit config nodes self s matched = { s with commit := commit } := by
  simp only [advanceCommit]
  split
  · next index h =>
    have := List.mem_of_find?_eq_some h
    simp only [List.mem_reverse, List.mem_range'_1] at this
    exact ⟨index, by omega, rfl⟩
  · exact ⟨s.commit, Nat.le_refl _, rfl⟩

omit [DecidableEq C] in
@[simp] theorem advanceCommit_term (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).term = s.term := by
  obtain ⟨commit, _, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]

omit [DecidableEq C] in
@[simp] theorem advanceCommit_votedFor (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).votedFor = s.votedFor := by
  obtain ⟨commit, _, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]

omit [DecidableEq C] in
@[simp] theorem advanceCommit_log (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).log = s.log := by
  obtain ⟨commit, _, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]

omit [DecidableEq C] in
@[simp] theorem advanceCommit_role (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).role = s.role := by
  obtain ⟨commit, _, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]

omit [DecidableEq C] in
@[simp] theorem advanceCommit_applied (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).applied = s.applied := by
  obtain ⟨commit, _, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]

omit [DecidableEq C] in
theorem commit_le_advanceCommit (s : Node N C M) (matched : List (N × Nat)) :
    s.commit ≤ (advanceCommit config nodes self s matched).commit := by
  obtain ⟨commit, hle, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]
  exact hle

omit [DecidableEq C] in
theorem advanceCommit_spec (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).commit = s.commit ∨
      (s.commit < (advanceCommit config nodes self s matched).commit ∧
        (advanceCommit config nodes self s matched).commit ≤ s.log.length ∧
        Quorum.isMajority nodes
          (holders self matched (advanceCommit config nodes self s matched).commit) = true ∧
        (config.commitsOwnTermOnly = true →
          termAt s.log (advanceCommit config nodes self s matched).commit = s.term)) := by
  simp only [advanceCommit]
  split
  · next index h =>
    have hmem := List.mem_of_find?_eq_some h
    have hok := List.find?_some h
    simp only [List.mem_reverse, List.mem_range'_1] at hmem
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok
    refine .inr ⟨?_, ?_, hok.1, fun hown => hok.2.resolve_right (by simp [hown])⟩ <;>
      dsimp only <;> omega
  · exact .inl rfl

theorem applied_le_advanceCommit (s : Node N C M) (matched : List (N × Nat))
    (h : s.applied ≤ s.commit) :
    (applyCommitted machine self (advanceCommit config nodes self s matched)).1.applied
      ≤ (advanceCommit config nodes self s matched).commit := by
  have := applyCommitted_applied_le machine self (advanceCommit config nodes self s matched)
  have := commit_le_advanceCommit config nodes self s matched
  simp only [advanceCommit_applied] at *
  omega

end Helpers

/-- What a node in state `s` may send and arm. -/
def Sent (i : N) (s : Node N C M) : Effect (sig N C R) i → Prop
  | .send _ (.requestVote term candidate lastIndex last) =>
    candidate = i ∧ term = s.term ∧ (∃ votes, s.role = .candidate votes)
      ∧ lastIndex = s.log.length ∧ last = lastTerm s.log
  | .send dst (.vote term voter) => voter = i ∧ term = s.term ∧ s.votedFor = some dst
  | .send _ (.append term _ prev prevTerm entries commit) =>
    isLeader s = true ∧ term = s.term ∧ prev ≤ s.log.length ∧ prevTerm = termAt s.log prev
      ∧ entries <+: s.log.drop prev ∧ commit = s.commit
  | .after _ msg => msg = .electionTimeout ∨ msg = .heartbeat
  | _ => True

/-- What one transition of a node can do, as far as the invariants can tell. `msg` is the
message handled, and `none` for a recovery. -/
structure Moves (config : Config) (nodes : List N) (i : N) (s : Node N C M)
    (msg : Option (Msg N C)) (s' : Node N C M) (effs : List (Effect (sig N C R) i)) : Prop where
  term_le : s.term ≤ s'.term
  keeps : s'.term = s.term → ∀ candidate, s.votedFor = some candidate →
    s'.votedFor = some candidate
  /-- A vote is one the node had cast in this term, or its own on starting a term, or one it
  grants to a candidate whose log is not behind its own. -/
  vote : ∀ candidate, s'.votedFor = some candidate →
    (s'.term = s.term ∧ s.votedFor = some candidate) ∨
    (s'.term = s.term + 1 ∧ candidate = i ∧ s'.log = s.log) ∨
    (∃ lastIndex last, msg = some (.requestVote s'.term candidate lastIndex last) ∧
      s'.log = s.log ∧ (config.votesForUpToDateOnly = true →
        lastTerm s.log < last ∨ (last = lastTerm s.log ∧ s.log.length ≤ lastIndex)))
  /-- A candidate has just started its term with its own vote, or was a candidate of this term
  and has counted at most the vote it handled. -/
  candidate : ∀ votes, s'.role = .candidate votes →
    (s'.term = s.term + 1 ∧ votes = [i] ∧ s'.votedFor = some i ∧ s'.log = s.log) ∨
    (s'.term = s.term ∧ s'.log = s.log ∧ ∃ votes₀, s.role = .candidate votes₀ ∧
      ∀ v ∈ votes, v ∈ votes₀ ∨ msg = some (.vote s.term v))
  /-- A leader has just started its term as a majority of one, or was a candidate of this term
  with a majority among the votes it had and the one it handled, or led it already and has kept
  its log. -/
  leader : isLeader s' = true →
    (s'.term = s.term + 1 ∧ Quorum.isMajority nodes [i] = true ∧ s'.votedFor = some i ∧
      s'.log = s.log) ∨
    (s'.term = s.term ∧ s'.log = s.log ∧ ∃ votes₀ votes, s.role = .candidate votes₀ ∧
      Quorum.isMajority nodes votes = true ∧
        ∀ v ∈ votes, v ∈ votes₀ ∨ msg = some (.vote s.term v)) ∨
    (s'.term = s.term ∧ isLeader s = true ∧ s.log <+: s'.log)
  /-- A new leader knows of no follower's log. One that stays has learnt at most what the
  acknowledgement it handled says. -/
  matched : ∀ matched', s'.role = .leader matched' → matched' = [] ∨
    (s'.term = s.term ∧ ∃ matched, s.role = .leader matched ∧ (matched' = matched ∨
      ∃ follower index, msg = some (.appended s.term follower index) ∧
        matched' = raise matched follower index))
  /-- The log is as it was, or a leader's with one entry of its term added, or a follower's
  merged with the entries of an `append` of its term that fits at `prev`. -/
  log : s'.log = s.log ∨
    (isLeader s' = true ∧ ∃ entry, entry.term = s'.term ∧ s'.log = s.log ++ [entry]) ∨
    (s'.role = .follower ∧ ∃ leader prev entries commit,
      msg = some (.append s'.term leader prev (termAt s.log prev) entries commit) ∧
        prev ≤ s.log.length ∧ s'.log = s.log.take prev ++ merge (s.log.drop prev) entries)
  /-- The commit index is as it was, or a leader's moved to an entry a majority is known to
  hold, or a follower's raised to what the `append` it took says. -/
  commit : s'.commit = s.commit ∨
    (s.commit < s'.commit ∧ s'.commit ≤ s'.log.length ∧
      (∃ matched, s'.role = .leader matched ∧
        Quorum.isMajority nodes (holders i matched s'.commit) = true) ∧
      (config.commitsOwnTermOnly = true → termAt s'.log s'.commit = s'.term)) ∨
    (∃ leader prev entries commit,
      msg = some (.append s'.term leader prev (termAt s.log prev) entries commit) ∧
        prev ≤ s.log.length ∧ s'.log = s.log.take prev ++ merge (s.log.drop prev) entries ∧
        s'.commit = max s.commit (min commit (prev + entries.length)))
  applied_le : s.applied ≤ s.commit → s'.applied ≤ s'.commit
  /-- Only a follower that has taken an `append` acknowledges, and what it acknowledges is where
  the entries it was sent end. -/
  acked : ∀ dst term follower index,
    Effect.send (σ := sig N C R) dst (.appended term follower index) ∈ effs →
      follower = i ∧ term = s'.term ∧ ∃ leader prev entries commit,
        msg = some (.append s'.term leader prev (termAt s.log prev) entries commit) ∧
          index = prev + entries.length ∧ prev ≤ s.log.length ∧
          s'.log = s.log.take prev ++ merge (s.log.drop prev) entries
  sent : ∀ eff ∈ effs, Sent i s' eff
  batch : ∀ dst term leader prev prevTerm entries commit,
    Effect.send (σ := sig N C R) dst (.append term leader prev prevTerm entries commit) ∈ effs →
      entries.length ≤ max 1 config.maxAppend

section Step

variable (config : Config) (nodes : List N) (machine : Machine C R M) (self : N)

/-- Proves `Moves` of one branch of a handler. -/
local macro "moves" : tactic => `(tactic|
  (constructor <;>
    simp [Sent, armElection, broadcast, abreast, appendTo, appendFrom, lead, isLeader] <;>
    first
    | grind [applyCommitted_applied_le, advanceCommit_spec]
    | exact fun h => applied_le_advanceCommit _ _ _ _ _ _ h))

theorem onElectionTimeout_moves (s : Node N C M) :
    Moves config nodes self s (some .electionTimeout)
      (onElectionTimeout config nodes machine self s).1
      (onElectionTimeout config nodes machine self s).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onElectionTimeout] <;> (repeat' split) <;> moves

theorem onRequestVote_moves (s : Node N C M) (term : Nat) (candidate : N) (lastIndex last : Nat) :
    Moves config nodes self s (some (.requestVote term candidate lastIndex last))
      (onRequestVote (R := R) config self s term candidate lastIndex last).1
      (onRequestVote (R := R) config self s term candidate lastIndex last).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onRequestVote, enterTerm] <;> (repeat' split) <;> moves

theorem onVote_moves (s : Node N C M) (term : Nat) (voter : N) :
    Moves config nodes self s (some (.vote term voter))
      (onVote config nodes machine self s term voter).1
      (onVote config nodes machine self s term voter).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onVote] <;> (repeat' split) <;> moves

theorem onAppend_moves (s : Node N C M) (term : Nat) (leader : N) (prev prevTerm : Nat)
    (entries : List (Entry N C)) (commit : Nat) :
    Moves config nodes self s (some (.append term leader prev prevTerm entries commit))
      (onAppend config machine self s term leader prev prevTerm entries commit).1
      (onAppend config machine self s term leader prev prevTerm entries commit).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onAppend, enterTerm] <;> (repeat' split) <;> moves

theorem onAppended_moves (s : Node N C M) (term : Nat) (follower : N) (index : Nat) :
    Moves config nodes self s (some (.appended term follower index))
      (onAppended config nodes machine self s term follower index).1
      (onAppended config nodes machine self s term follower index).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onAppended] <;> (repeat' split) <;> moves

theorem onPropose_moves (s : Node N C M) (req : ReqId) (cmd : C) :
    Moves config nodes self s (some (.propose req cmd))
      (onPropose config nodes machine self s req cmd).1
      (onPropose config nodes machine self s req cmd).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onPropose] <;> (repeat' split) <;> moves

theorem step_moves (s : Node N C M) (msg : Msg N C) :
    Moves config nodes self s (some msg) ((node config nodes machine self).step s msg).1
      ((node config nodes machine self).step s msg).2 := by
  cases msg with
  | electionTimeout => exact onElectionTimeout_moves config nodes machine self s
  | heartbeat =>
    obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
    cases role <;> simp only [node] <;> moves
  | requestVote term candidate lastIndex last =>
    exact onRequestVote_moves config nodes self s term candidate lastIndex last
  | vote term voter => exact onVote_moves config nodes machine self s term voter
  | append term leader prev prevTerm entries commit =>
    exact onAppend_moves config nodes machine self s term leader prev prevTerm entries commit
  | appended term follower index =>
    exact onAppended_moves config nodes machine self s term follower index
  | propose req cmd => exact onPropose_moves config nodes machine self s req cmd

theorem recover_moves (s : Node N C M) :
    Moves config nodes self s none ((node config nodes machine self).recover s).1
      ((node config nodes machine self).recover s).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [node] <;> moves

end Step

end RaftKV
