/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Basic

/-!
# At most one leader per term

`Check.lean` checks election safety on three nodes and two terms. Here it is proved for any
finite set of nodes, any machine, any `Config` and any environment model: links may lose,
duplicate and reorder messages, and nodes may crash and restart at any time.

A node forgets its vote when its term moves on and its role when it restarts, so the proof lets
each node remember every state it has left (`past`). The invariant (`Votes`) says that the
states a node has been in name one candidate per term, and that every vote in flight, every vote
a candidate has counted and a majority behind every node that was ever a leader are votes some
state of the voter holds. Two leaders of one term, at any two times, then share a voter, and
that voter's states name them both.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

abbrev past (config : Config) (machine : Machine C R M) : Ghost (cluster N config machine) where
  Hist _ := List (Node N C M)
  init _ := []
  step _ hist s _ := s :: hist
  recover _ hist s := s :: hist

abbrev recording (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]
    [Enum N] (config : Config) (machine : Machine C R M) : System (sig N C R) :=
  (cluster N config machine).withGhost (past config machine)

/-- Every state node `v` has been in, the present one first. -/
def seen (c : SysState (recording N config machine)) (v : N) : List (Node N C M) :=
  (c.state v).1 :: (c.state v).2

def VotedFor (c : SysState (recording N config machine)) (voter : N) (term : Nat)
    (candidate : N) : Prop :=
  ∃ p ∈ seen c voter, p.term = term ∧ p.votedFor = some candidate

omit [Enum N] in
theorem Moves.refl (nodes : List N) (i : N) (s : Node N C M) :
    Moves (R := R) nodes i s none s [] := by
  constructor <;> simp +contextual

/-- The states a node has left are of terms up to its own, and those of its own term voted as
it does now, if they voted. All its states of one term name one candidate. -/
structure OneVote (s : Node N C M) (hist : List (Node N C M)) : Prop where
  bound : ∀ p ∈ hist, p.term ≤ s.term ∧
    (p.term = s.term → ∀ candidate, p.votedFor = some candidate → s.votedFor = some candidate)
  once : ∀ p ∈ s :: hist, ∀ q ∈ s :: hist, p.term = q.term →
    ∀ a b, p.votedFor = some a → q.votedFor = some b → a = b

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem OneVote.nil (s : Node N C M) : OneVote s [] :=
  ⟨by simp, by simp +contextual⟩

omit [Enum N] in
theorem Moves.oneVote {nodes : List N} {i : N} {s s' : Node N C M} {hist : List (Node N C M)}
    {msg : Option (Msg N C)} {effs : List (Effect (sig N C R) i)}
    (h : Moves nodes i s msg s' effs) (hs : OneVote s hist) : OneVote s' (s :: hist) := by
  have hterm := h.term_le
  have hbound : ∀ p ∈ s :: hist, p.term ≤ s'.term ∧
      (p.term = s'.term → ∀ candidate, p.votedFor = some candidate →
        s'.votedFor = some candidate) := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hterm, fun ht candidate hvoted => h.keeps ht.symm candidate hvoted⟩
    · obtain ⟨hle, heq⟩ := hs.bound p hp
      exact ⟨by omega, fun ht candidate hvoted =>
        h.keeps (by omega) candidate (heq (by omega) candidate hvoted)⟩
  refine ⟨hbound, fun p hp q hq ht a b ha hb => ?_⟩
  rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
  · exact Option.some.inj (ha.symm.trans hb)
  · exact Option.some.inj (ha.symm.trans ((hbound q hq').2 ht.symm b hb))
  · exact Option.some.inj (((hbound p hp').2 ht a ha).symm.trans hb)
  · exact hs.once p hp' q hq' ht a b ha hb

/--
The inductive invariant. Every clause reads the states nodes have been in, which are never
forgotten, and quantifies over all messages in flight and all armed timers, so no loss,
duplication or crash can break it.
-/
structure Votes (c : SysState (recording N config machine)) : Prop where
  oneVote : ∀ v, OneVote (c.state v).1 (c.state v).2
  sent : ∀ src dst term voter,
    (⟨src, dst, .vote term voter⟩ : Envelope (sig N C R)) ∈ c.net → VotedFor c voter term dst
  counted : ∀ a votes, (c.state a).1.role = .candidate votes →
    ∀ v ∈ votes, VotedFor c v (c.state a).1.term a
  elected : ∀ a, ∀ p ∈ seen c a, isLeader p = true →
    ∃ quorum, Quorum.isMajority Enum.all quorum = true ∧ ∀ v ∈ quorum, VotedFor c v p.term a
  /-- Without this a `vote` could arrive as a timer, where `sent` says nothing about it. -/
  timers : ∀ i msg, msg ∈ c.timers i → msg = .electionTimeout ∨ msg = .heartbeat

section Grow

variable {c : SysState (recording N config machine)} {i : N} {s' : Node N C M}
  {effs : List (Effect (sig N C R) i)}

theorem mem_seen_grow {v : N} {p : Node N C M} :
    p ∈ seen (c.grow i ((s', seen c i), effs)) v ↔ p ∈ seen c v ∨ (v = i ∧ p = s') := by
  by_cases hv : v = i
  · subst hv
    simp [seen, or_comm]
  · simp [seen, hv]

theorem VotedFor.grow {voter candidate : N} {term : Nat} (h : VotedFor c voter term candidate) :
    VotedFor (c.grow i ((s', seen c i), effs)) voter term candidate :=
  h.elim fun p hp => ⟨p, mem_seen_grow.mpr (.inl hp.1), hp.2⟩

end Grow

namespace Votes

variable {c : SysState (recording N config machine)}

theorem blank : Votes (SysState.blank (recording N config machine)) := by
  constructor <;>
    simp [SysState.blank, recording, System.withGhost, node, OneVote.nil, seen, isLeader]

theorem below {c' : SysState (recording N config machine)} (hc : Votes c) (hbelow : c'.Below c) :
    Votes c' := by
  obtain ⟨hstate, hnet, htimers, _⟩ := hbelow
  refine ⟨?_, ?_, ?_, ?_, fun i msg h => hc.timers i msg (htimers i msg h)⟩ <;>
    simp only [VotedFor, seen, hstate]
  · exact hc.oneVote
  · exact fun src dst term voter h => hc.sent src dst term voter (hnet _ h)
  · exact hc.counted
  · exact hc.elected

theorem input (hc : Votes c) (x : Request N C) :
    Votes { c with net := c.net ++ [⟨none, x.via, .propose x.req x.cmd⟩] } := by
  refine ⟨hc.oneVote, fun src dst term voter h => ?_, hc.counted, hc.elected, hc.timers⟩
  rcases List.mem_append.mp h with h | h
  · exact hc.sent src dst term voter h
  · simp at h

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- The votes a candidate has counted, and the one it is handling, are still votes once it has
moved. -/
theorem backed (hc : Votes c)
    (hgranted : ∀ v, msg = some (.vote (c.state i).1.term v) →
      VotedFor c v (c.state i).1.term i)
    {votes₀ votes : List N} (hrole : (c.state i).1.role = .candidate votes₀)
    (hfrom : ∀ v ∈ votes, v ∈ votes₀ ∨ msg = some (.vote (c.state i).1.term v)) :
    ∀ v ∈ votes, VotedFor (c.grow i ((s', seen c i), effs)) v (c.state i).1.term i :=
  fun v hv => (hfrom v hv).elim (fun hold => (hc.counted i votes₀ hrole v hold).grow)
    fun hnew => (hgranted v hnew).grow

theorem elected_moved (hc : Votes c) (hmoves : Moves Enum.all i (c.state i).1 msg s' effs)
    (hgranted : ∀ v, msg = some (.vote (c.state i).1.term v) →
      VotedFor c v (c.state i).1.term i)
    (hleader : isLeader s' = true) :
    ∃ quorum, Quorum.isMajority Enum.all quorum = true ∧
      ∀ v ∈ quorum, VotedFor (c.grow i ((s', seen c i), effs)) v s'.term i := by
  rcases hmoves.leader hleader with ⟨_, hmajority, hvoted⟩ |
    ⟨hterm, votes₀, votes, hrole₀, hmajority, hfrom⟩ | ⟨hterm, hleader₀, _⟩
  · refine ⟨[i], hmajority, fun v hv => ?_⟩
    obtain rfl := List.mem_singleton.mp hv
    exact ⟨s', mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩), rfl, hvoted⟩
  · exact ⟨votes, hmajority, hterm ▸ hc.backed hgranted hrole₀ hfrom⟩
  · obtain ⟨quorum, hmajority, hvotes⟩ := hc.elected i _ List.mem_cons_self hleader₀
    exact ⟨quorum, hmajority, fun v hv => hterm ▸ (hvotes v hv).grow⟩

theorem grow (hc : Votes c) (hmoves : Moves Enum.all i (c.state i).1 msg s' effs)
    (hgranted : ∀ v, msg = some (.vote (c.state i).1.term v) →
      VotedFor c v (c.state i).1.term i) :
    Votes (c.grow i ((s', seen c i), effs)) := by
  have hself : s' ∈ seen (c.grow i ((s', seen c i), effs)) i := mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩)
  refine ⟨fun v => ?_, fun src dst term voter hmem => ?_, fun a votes hrole v hv => ?_,
    fun a p hp hleader => ?_, fun j m hmem => ?_⟩
  · by_cases hv : v = i
    · subst hv
      simpa [seen] using hmoves.oneVote (hc.oneVote v)
    · simpa [hv] using hc.oneVote v
  · rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact (hc.sent src dst term voter hold).grow
    · obtain ⟨rfl, rfl, hvoted⟩ := hmoves.sent _ hnew
      exact ⟨s', hself, rfl, hvoted⟩
  · by_cases ha : a = i
    · subst ha
      rw [SysState.grow_state_self] at hrole ⊢
      rcases hmoves.candidate votes hrole with ⟨_, rfl, hvoted⟩ | ⟨hterm, votes₀, hrole₀, hfrom⟩
      · obtain rfl := List.mem_singleton.mp hv
        exact ⟨s', hself, rfl, hvoted⟩
      · exact hterm ▸ hc.backed hgranted hrole₀ hfrom v hv
    · rw [SysState.grow_state_of_ne _ _ ha] at hrole ⊢
      exact (hc.counted a votes hrole v hv).grow
  · rcases mem_seen_grow.mp hp with hold | ⟨rfl, rfl⟩
    · obtain ⟨quorum, hmajority, hvotes⟩ := hc.elected a p hold hleader
      exact ⟨quorum, hmajority, fun v hv => (hvotes v hv).grow⟩
    · exact hc.elected_moved hmoves hgranted hleader
  · rcases SysState.mem_grow_timers.mp hmem with hold | ⟨rfl, delay, hnew⟩
    · exact hc.timers j m hold
    · exact hmoves.sent _ hnew

/-- A term has one leader, over all time. -/
theorem leader_unique (hc : Votes c) {a b : N} {p q : Node N C M} (hp : p ∈ seen c a)
    (hq : q ∈ seen c b) (ha : isLeader p = true) (hb : isLeader q = true)
    (hterm : p.term = q.term) : a = b := by
  obtain ⟨quorumA, hmajorityA, hvotesA⟩ := hc.elected a p hp ha
  obtain ⟨quorumB, hmajorityB, hvotesB⟩ := hc.elected b q hq hb
  obtain ⟨v, hvA, hvB⟩ := Quorum.majority_inter hmajorityA hmajorityB
  obtain ⟨p', hp', htermA, hvotedA⟩ := hvotesA v hvA
  obtain ⟨q', hq', htermB, hvotedB⟩ := hvotesB v hvB
  exact (hc.oneVote v).once p' hp' q' hq' (by omega) a b hvotedA hvotedB

end Votes

theorem Votes.step {c : SysState (recording N config machine)} (hc : Votes c) (i : N)
    (msg : Msg N C) (hpending : (∃ src, ⟨src, i, msg⟩ ∈ c.net) ∨ msg ∈ c.timers i) :
    Votes (c.grow i (((recording N config machine).actor i).step (c.state i) msg)) := by
  refine hc.grow (step_moves config Enum.all machine i _ msg) ?_
  intro v hmsg
  obtain rfl := Option.some.inj hmsg
  rcases hpending with ⟨src, hnet⟩ | htimer
  · exact hc.sent src i _ v hnet
  · exact nomatch hc.timers i _ htimer

theorem Votes.recover {c : SysState (recording N config machine)} (hc : Votes c) (i : N) :
    Votes (c.grow i (((recording N config machine).actor i).recover (c.state i))) :=
  hc.grow (recover_moves config Enum.all machine i _) nofun

theorem votes_inductive (env : EnvModel (sig N C R)) :
    (recording N config machine).Inductive env Votes :=
  .of_monotone env .blank (fun _ _ => .below) (fun _ x hc => hc.input x)
    (fun _ i msg hc => hc.step i msg) fun _ i hc => hc.recover i

theorem election_safety (config : Config) (machine : Machine C R M) (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c =>
      ∀ a b matchedA matchedB, (c.state a).role = .leader matchedA →
        (c.state b).role = .leader matchedB → (c.state a).term = (c.state b).term → a = b := by
  refine .of_ghost (past config machine) fun c hc a b matchedA matchedB ha hb hterm => ?_
  exact ((votes_inductive env).invariant c hc).leader_unique (p := (c.state a).1)
    (q := (c.state b).1) List.mem_cons_self List.mem_cons_self (isLeader_iff.mpr ⟨_, ha⟩)
    (isLeader_iff.mpr ⟨_, hb⟩) hterm

theorem electionSafety_invariant (config : Config) (machine : Machine C R M)
    (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c => electionSafety c = true := by
  intro c hc
  have hsafe := election_safety config machine env c hc
  simp only [electionSafety, pairs, List.all_eq_true]
  intro a _ b _
  have := hsafe a b
  have := isLeader_iff (s := c.state a)
  have := isLeader_iff (s := c.state b)
  grind

end RaftKV
