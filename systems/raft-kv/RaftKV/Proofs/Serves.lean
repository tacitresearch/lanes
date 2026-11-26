/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Basic

/-!
# What a node does for its clients

`Moves` says what one step does to a node's term, vote, role and log, which is what the safety
proofs need. The proof that the cluster is the machine needs the rest (`Serves`): an entry is
added only by the node that handles a `propose`, and is that request; a node applies exactly the
entries between what it had applied and what it has now committed, in order; and it answers
exactly those it took from a client itself, each with the result of applying it to the machine
after the entries before it.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]

namespace Machine

variable (machine : Machine C R M)

/-- The answers `self` gives while `entries` are applied from `m`: one for each entry it took
from a client. -/
def replies (self : N) (m : M) : List (Entry N C) → List (Response R)
  | [] => []
  | entry :: entries =>
    (if entry.origin = self then [⟨entry.req, (machine.apply m entry.cmd).2⟩] else [])
      ++ replies self (machine.apply m entry.cmd).1 entries

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] in
@[simp] theorem run_nil (m : M) : machine.run m ([] : List (Entry N C)) = m := rfl

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] in
theorem run_append (m : M) (a b : List (Entry N C)) :
    machine.run m (a ++ b) = machine.run (machine.run m a) b :=
  List.foldl_append

omit [DecidableEq C] [DecidableEq R] in
theorem replies_append (self : N) (m : M) (a b : List (Entry N C)) :
    machine.replies self m (a ++ b) =
      machine.replies self m a ++ machine.replies self (machine.run m a) b := by
  induction a generalizing m with
  | nil => rfl
  | cons entry a ih => simp [replies, run, ih, List.foldl_cons]

end Machine

section Helpers

variable (config : Config) (nodes : List N) (machine : Machine C R M) (self : N)

theorem applyCommitted_eq_run (s : Node N C M) :
    applyCommitted machine self s =
      ({ s with
          machine := machine.run s.machine ((s.log.take s.commit).drop s.applied)
          applied := s.applied + ((s.log.take s.commit).drop s.applied).length },
        (machine.replies self s.machine ((s.log.take s.commit).drop s.applied)).map
          (Effect.emit (σ := sig N C R) (self := self))) := by
  unfold applyCommitted
  generalize (s.log.take s.commit).drop s.applied = todo
  suffices h : ∀ (s : Node N C M) (effs : List (Eff self (N := N) (C := C) (R := R))),
      List.foldl (fun (acc : Node N C M × List (Eff self (N := N) (C := C) (R := R))) entry =>
        ({ acc.1 with machine := (machine.apply acc.1.machine entry.cmd).1,
                      applied := acc.1.applied + 1 },
          if entry.origin = self then
            acc.2 ++ [.emit ⟨entry.req, (machine.apply acc.1.machine entry.cmd).2⟩]
          else acc.2)) (s, effs) todo =
        ({ s with machine := machine.run s.machine todo, applied := s.applied + todo.length },
          effs ++ (machine.replies self s.machine todo).map
            (Effect.emit (σ := sig N C R) (self := self))) by
    simpa using h s []
  intro s effs
  induction todo generalizing s effs with
  | nil => simp [Machine.replies]
  | cons entry todo ih =>
    rw [List.foldl_cons, ih]
    by_cases horigin : entry.origin = self <;>
      simp [horigin, Machine.run, Machine.replies, Nat.add_assoc, Nat.add_comm 1]

omit [DecidableEq C] in
@[simp] theorem advanceCommit_machine (s : Node N C M) (matched : List (N × Nat)) :
    (advanceCommit config nodes self s matched).machine = s.machine := by
  obtain ⟨commit, _, h⟩ := advanceCommit_eq config nodes self s matched
  rw [h]

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] in
theorem getElem?_merge {own sent : List (Entry N C)} {j : Nat} {entry : Entry N C}
    (h : (merge own sent)[j]? = some entry) : own[j]? = some entry ∨ sent[j]? = some entry := by
  fun_induction merge own sent generalizing j <;> grind

end Helpers

/-- What one transition of a node does for its clients. `msg` is the message handled, and `none`
for a recovery. -/
structure Serves (machine : Machine C R M) (i : N) (s : Node N C M) (msg : Option (Msg N C))
    (s' : Node N C M) (effs : List (Effect (sig N C R) i)) : Prop where
  /-- The log is as it was, or has one more entry, which is the `propose` handled, or is merged
  with the entries of the `append` handled. -/
  log : s'.log = s.log ∨
    (∃ req cmd, msg = some (.propose req cmd) ∧ s'.log = s.log ++ [⟨s.term, i, req, cmd⟩]) ∨
    (∃ term leader prev prevTerm entries commit,
      msg = some (.append term leader prev prevTerm entries commit) ∧ prev ≤ s.log.length ∧
        s'.log = s.log.take prev ++ merge (s.log.drop prev) entries)
  /-- A node that had applied all it had committed applies what it has now committed past
  that, and answers those entries it took from a client. -/
  applies : s.commit ≤ s.applied →
    s'.machine = machine.run s.machine ((s'.log.take s'.commit).drop s.applied) ∧
    s'.applied = s.applied + ((s'.log.take s'.commit).drop s.applied).length ∧
    Effect.emits effs = machine.replies i s.machine ((s'.log.take s'.commit).drop s.applied)
  /-- Requests come from clients only. -/
  proposes : ∀ dst req cmd, Effect.send (σ := sig N C R) dst (.propose req cmd) ∉ effs

section Step

variable (config : Config) (nodes : List N) (machine : Machine C R M) (self : N)

/-- Proves `Serves` of one branch of a handler. -/
local macro "serves" : tactic => `(tactic|
  (refine ⟨?_, fun h => ?_, ?_⟩
   · simp [applyCommitted_eq_run, lead] <;> grind
   · simp [applyCommitted_eq_run, lead, armElection, broadcast, appendTo, Effect.emits_map,
       Effect.emits_nil, Effect.emits_append, Effect.emits_cons, drop_take_of_le _ h, Machine.replies]
   · simp [applyCommitted_eq_run, lead, armElection, broadcast, appendTo]))

theorem onElectionTimeout_serves (s : Node N C M) :
    Serves machine self s (some .electionTimeout)
      (onElectionTimeout config nodes machine self s).1
      (onElectionTimeout config nodes machine self s).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onElectionTimeout] <;> (repeat' split) <;> serves

theorem onRequestVote_serves (s : Node N C M) (term : Nat) (candidate : N)
    (lastIndex last : Nat) :
    Serves machine self s (some (.requestVote term candidate lastIndex last))
      (onRequestVote (R := R) config self s term candidate lastIndex last).1
      (onRequestVote (R := R) config self s term candidate lastIndex last).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onRequestVote, enterTerm] <;> (repeat' split) <;> serves

theorem onVote_serves (s : Node N C M) (term : Nat) (voter : N) :
    Serves machine self s (some (.vote term voter))
      (onVote config nodes machine self s term voter).1
      (onVote config nodes machine self s term voter).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onVote] <;> (repeat' split) <;> serves

theorem onAppend_serves (s : Node N C M) (term : Nat) (leader : N) (prev prevTerm : Nat)
    (entries : List (Entry N C)) (commit : Nat) :
    Serves machine self s (some (.append term leader prev prevTerm entries commit))
      (onAppend config machine self s term leader prev prevTerm entries commit).1
      (onAppend config machine self s term leader prev prevTerm entries commit).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onAppend, enterTerm] <;> (repeat' split) <;> serves

theorem onAppended_serves (s : Node N C M) (term : Nat) (follower : N) (index : Nat) :
    Serves machine self s (some (.appended term follower index))
      (onAppended config nodes machine self s term follower index).1
      (onAppended config nodes machine self s term follower index).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onAppended] <;> (repeat' split) <;> serves

theorem onPropose_serves (s : Node N C M) (req : ReqId) (cmd : C) :
    Serves machine self s (some (.propose req cmd))
      (onPropose config nodes machine self s req cmd).1
      (onPropose config nodes machine self s req cmd).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [onPropose] <;> (repeat' split) <;> serves

theorem step_serves (s : Node N C M) (msg : Msg N C) :
    Serves machine self s (some msg) ((node config nodes machine self).step s msg).1
      ((node config nodes machine self).step s msg).2 := by
  cases msg with
  | electionTimeout => exact onElectionTimeout_serves config nodes machine self s
  | heartbeat =>
    obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
    cases role <;> simp only [node] <;> serves
  | requestVote term candidate lastIndex last =>
    exact onRequestVote_serves config machine self s term candidate lastIndex last
  | vote term voter => exact onVote_serves config nodes machine self s term voter
  | append term leader prev prevTerm entries commit =>
    exact onAppend_serves config machine self s term leader prev prevTerm entries commit
  | appended term follower index =>
    exact onAppended_serves config nodes machine self s term follower index
  | propose req cmd => exact onPropose_serves config nodes machine self s req cmd

theorem recover_serves (s : Node N C M) :
    Serves machine self s none ((node config nodes machine self).recover s).1
      ((node config nodes machine self).recover s).2 := by
  obtain ⟨t, voted, log, commit, applied, m, role⟩ := s
  cases role <;> simp only [node] <;> serves

end Step

end RaftKV
