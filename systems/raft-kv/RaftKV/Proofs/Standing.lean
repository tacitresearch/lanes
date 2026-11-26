/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Log

/-!
# What candidates say and what followers acknowledge

The proof of commitment (`Proofs/Commit.lean`) rests on two exchanges being truthful, for every
`Config`. A request for a vote tells the length and last term of the log its candidate stands
with, and a candidate stands in a term with one log, none of whose entries is of that term. An
acknowledgement, in flight or counted by a leader in its `matched`, is of entries the follower
held while in the leader's term (`Held`). `Standing` is the invariant that says so, as one more
layer on `Replicating`.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

section Lists

omit [DecidableEq C] [DecidableEq R] [Enum N]

theorem matchedOf_mem (matched : List (N × Nat)) (f : N) :
    matchedOf matched f = 0 ∨ (f, matchedOf matched f) ∈ matched := by
  induction matched with
  | nil => exact .inl rfl
  | cons pair matched ih =>
    obtain ⟨g, m⟩ := pair
    by_cases hg : f = g
    · subst hg
      exact .inr (by simp [matchedOf, List.lookup])
    · have hne : (f == g) = false := by simpa using hg
      rcases ih with h | h
      · exact .inl (by simpa [matchedOf, List.lookup, hne] using h)
      · exact .inr (List.mem_cons_of_mem _ (by simpa [matchedOf, List.lookup, hne] using h))

theorem mem_raise {matched : List (N × Nat)} {f g : N} {index m : Nat}
    (h : (g, m) ∈ raise matched f index) :
    (g = f ∧ m = max index (matchedOf matched f)) ∨ (g, m) ∈ matched := by
  simp only [raise, List.mem_cons, Prod.mk.injEq, List.mem_filter] at h
  exact h.imp id (·.1)

end Lists

/-- The message a node is handling is in flight to it, or is one of its two timers. -/
def Pending (c : SysState (recording N config machine)) (i : N) (msg : Option (Msg N C)) : Prop :=
  ∀ m, msg = some m →
    (∃ src, (⟨src, i, m⟩ : Envelope (sig N C R)) ∈ c.net) ∨ m = .electionTimeout ∨ m = .heartbeat

/-- Node `v` had, while in `term`, a log that starts with `pfx`. -/
def Held (c : SysState (recording N config machine)) (v : N) (term : Nat)
    (pfx : List (Entry N C)) : Prop :=
  ∃ q ∈ c.seen v, q.term = term ∧ pfx <+: q.log

def IsCandidate (s : Node N C M) : Prop :=
  ∃ votes, s.role = .candidate votes

section Basics

variable {c : SysState (recording N config machine)} {i : N} {msg : Option (Msg N C)}
  {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

theorem pending_none : Pending c i none :=
  nofun

theorem Timers.pending (ht : Timers c) {m : Msg N C}
    (h : (∃ src, (⟨src, i, m⟩ : Envelope (sig N C R)) ∈ c.net) ∨ m ∈ c.timers i) :
    Pending c i (some m) := by
  intro m' hm
  obtain rfl := Option.some.inj hm
  exact h.imp id (ht i _)

theorem Logs.cut_of_pending (hc : Logs c) (h : Pending c i msg) : Logs.Cut c msg := by
  intro term leader prev prevTerm entries commit hmsg
  rcases h _ hmsg with ⟨src, hnet⟩ | h | h
  · exact hc.appends src i term leader prev prevTerm entries commit hnet
  · cases h
  · cases h

theorem Votes.seen_term_le (hv : Votes c) {v : N} {p : Node N C M} (hp : p ∈ c.seen v) :
    p.term ≤ (c.state v).1.term := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact Nat.le_refl _
  · exact ((hv.oneVote v).bound p hp).1

theorem grow_term_le (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (a : N) :
    (c.state a).1.term ≤ ((c.grow i ((s', c.seen i), effs)).state a).1.term := by
  by_cases ha : a = i
  · subst ha
    simpa using hmoves.term_le
  · simp [ha]

theorem Held.grow {v : N} {term : Nat} {pfx : List (Entry N C)} (h : Held c v term pfx) :
    Held (c.grow i ((s', c.seen i), effs)) v term pfx :=
  h.elim fun q hq => ⟨q, mem_seen_grow.mpr (.inl hq.1), hq.2⟩

theorem Held.mono {v : N} {term : Nat} {pfx pfx' : List (Entry N C)} (h : Held c v term pfx)
    (hp : pfx' <+: pfx) : Held c v term pfx' :=
  h.elim fun q hq => ⟨q, hq.1, hq.2.1, hp.trans hq.2.2⟩

/-- The logs a node had as leader of the term it leads now are in its log. -/
theorem Logs.led_prefix (hv : Votes c) (hc : Logs c) {a : N}
    (hleader : isLeader (c.state a).1 = true) {l : List (Entry N C)}
    (hled : Led c (c.state a).1.term l) : l <+: (c.state a).1.log := by
  obtain ⟨b, p, hp, hpleader, hterm, rfl⟩ := hled
  obtain rfl := hv.leader_unique hp (c.mem_seen_self a) hpleader hleader hterm
  rcases (hc.grows b p hp hpleader).2 hterm with h | h
  · simp [isLeader, h] at hleader
  · exact h.2

/-- A vote after a move is one from before, or the one the node that moved now holds. -/
theorem VotedFor.of_grow {voter candidate : N} {term : Nat}
    (h : VotedFor (c.grow i ((s', c.seen i), effs)) voter term candidate) :
    VotedFor c voter term candidate ∨
      (voter = i ∧ s'.term = term ∧ s'.votedFor = some candidate) := by
  obtain ⟨p, hp, hterm, hvoted⟩ := h
  rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
  · exact .inl ⟨p, hp, hterm, hvoted⟩
  · exact .inr ⟨rfl, hterm, hvoted⟩

end Basics

/-- The invariant, given `Replicating`. -/
structure Standing (c : SysState (recording N config machine)) : Prop where
  /-- A candidate holds no entry of the term it stands in. -/
  behind : ∀ a, ∀ p ∈ c.seen a, IsCandidate p → ∀ entry ∈ p.log, entry.term < p.term
  /-- A node stands in a term with one log. -/
  oneLog : ∀ a, ∀ p ∈ c.seen a, ∀ q ∈ c.seen a, IsCandidate p → IsCandidate q →
    p.term = q.term → p.log = q.log
  requests : ∀ src dst term candidate lastIndex last,
    (⟨src, dst, .requestVote term candidate lastIndex last⟩ : Envelope (sig N C R)) ∈ c.net →
      ∃ p ∈ c.seen candidate, p.term = term ∧ IsCandidate p ∧ lastIndex = p.log.length ∧
        last = lastTerm p.log
  /-- Nobody has voted for a node in a term that node has not reached. -/
  reached : ∀ voter term candidate, VotedFor c voter term candidate →
    term ≤ (c.state candidate).1.term
  acks : ∀ src dst term follower index,
    (⟨src, dst, .appended term follower index⟩ : Envelope (sig N C R)) ∈ c.net →
      ∃ l, Led c term l ∧ index ≤ l.length ∧ Held c follower term (l.take index)
  matched : ∀ a matched, (c.state a).1.role = .leader matched → ∀ f index, (f, index) ∈ matched →
    index ≤ (c.state a).1.log.length ∧
      Held c f (c.state a).1.term ((c.state a).1.log.take index)

namespace Standing

variable {c : SysState (recording N config machine)}

theorem blank : Standing (SysState.blank (recording N config machine)) := by
  constructor <;>
    simp [SysState.blank, recording, System.withPast, System.withGhost, node, SysState.seen,
      IsCandidate, VotedFor]

theorem below {c' : SysState (recording N config machine)} (hc : Standing c)
    (hbelow : c'.Below c) : Standing c' := by
  obtain ⟨hstate, hnet, _, _⟩ := hbelow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Held, Led, VotedFor, SysState.seen, hstate]
  · exact hc.behind
  · exact hc.oneLog
  · exact fun src dst term candidate lastIndex last h =>
      hc.requests src dst term candidate lastIndex last (hnet _ h)
  · exact hc.reached
  · exact fun src dst term follower index h => hc.acks src dst term follower index (hnet _ h)
  · exact hc.matched

theorem input (hc : Standing c) (x : Request N C) :
    Standing { c with net := c.net ++ [⟨none, x.via, .propose x.req x.cmd⟩] } := by
  refine ⟨hc.behind, hc.oneLog, fun src dst term candidate lastIndex last h => ?_, hc.reached,
    fun src dst term follower index h => ?_, hc.matched⟩
  · rcases List.mem_append.mp h with h | h
    · exact hc.requests src dst term candidate lastIndex last h
    · simp at h
  · rcases List.mem_append.mp h with h | h
    · exact hc.acks src dst term follower index h
    · simp at h

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

theorem behind_moved (hterms : Terms c) (hc : Standing c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcandidate : IsCandidate s') :
    ∀ entry ∈ s'.log, entry.term < s'.term := by
  obtain ⟨votes, hrole⟩ := hcandidate
  intro entry hentry
  rcases hmoves.candidate votes hrole with ⟨hterm, _, _, hlog⟩ | ⟨hterm, hlog, votes₀, hrole₀, _⟩
  · have := hterms.logs i entry (hlog ▸ hentry)
    omega
  · exact hterm ▸ hc.behind i _ (c.mem_seen_self i) ⟨votes₀, hrole₀⟩ entry (hlog ▸ hentry)

theorem oneLog_moved (hv : Votes c) (hc : Standing c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcandidate : IsCandidate s')
    {q : Node N C M} (hq : q ∈ c.seen i) (hqcandidate : IsCandidate q) (hterm : q.term = s'.term) :
    q.log = s'.log := by
  obtain ⟨votes, hrole⟩ := hcandidate
  rcases hmoves.candidate votes hrole with ⟨hnew, _⟩ | ⟨hsame, hlog, votes₀, hrole₀, _⟩
  · have := hv.seen_term_le hq
    omega
  · exact hlog ▸ hc.oneLog i q hq _ (c.mem_seen_self i) hqcandidate ⟨votes₀, hrole₀⟩
      (hterm.trans hsame)

theorem reached_moved (hv : Votes c) (hc : Standing c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    {candidate : N} (hvoted : s'.votedFor = some candidate) :
    s'.term ≤ ((c.grow i ((s', c.seen i), effs)).state candidate).1.term := by
  have hgrown := grow_term_le hmoves candidate
  rcases hmoves.vote candidate hvoted with ⟨hterm, hkept⟩ | ⟨_, rfl, _⟩ |
    ⟨lastIndex, last, hmsg, _⟩
  · have := hc.reached i _ candidate ⟨_, c.mem_seen_self i, rfl, hkept⟩
    omega
  · simp
  · rcases hpending _ hmsg with ⟨src, hnet⟩ | h | h
    · obtain ⟨p, hp, hterm, _⟩ := hc.requests src i _ candidate lastIndex last hnet
      have := hv.seen_term_le hp
      omega
    · cases h
    · cases h

/-- What a follower acknowledges on taking an `append`, it holds. -/
theorem acked_moved (hv : Votes c) (hl : Logs c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    {dst follower : N} {term index : Nat}
    (hsent : Effect.send (σ := sig N C R) dst (.appended term follower index) ∈ effs) :
    ∃ l, Led (c.grow i ((s', c.seen i), effs)) term l ∧ index ≤ l.length ∧
      Held (c.grow i ((s', c.seen i), effs)) follower term (l.take index) := by
  obtain ⟨rfl, rfl, leader, prev, entries, commit, hmsg, rfl, hprev, hlog⟩ :=
    hmoves.acked dst term follower index hsent
  obtain ⟨l, hled, hlen, hterm, rfl⟩ := hl.cut_of_pending hpending _ leader prev _ _ commit hmsg
  have hindex : prev + (l.drop prev).length = l.length := by
    rw [List.length_drop]
    omega
  have hprefix : l <+: s'.log := by
    rcases hl.accepted hv hled hprev hlen hterm hlog with h | h
    · exact h.2 ▸ h.1
    · exact h.2 ▸ List.prefix_refl _
  refine ⟨l, hled.grow, by omega, s', mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩), rfl, ?_⟩
  rw [hindex, List.take_length]
  exact hprefix

theorem matched_moved (hv : Votes c) (hl : Logs c) (hc : Standing c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    {matched' : List (N × Nat)} (hrole : s'.role = .leader matched') {f : N} {index : Nat}
    (hmem : (f, index) ∈ matched') :
    index ≤ s'.log.length ∧ Held c f s'.term (s'.log.take index) := by
  rcases hmoves.matched matched' hrole with rfl | ⟨hterm, matched, hrole₀, hfrom⟩
  · simp at hmem
  have hleader₀ : isLeader (c.state i).1 = true := isLeader_iff.mpr ⟨matched, hrole₀⟩
  have hgrows : (c.state i).1.log <+: s'.log := by
    rcases hmoves.leader_grows hterm hleader₀ with h | h
    · simp [h] at hrole
    · exact h.2
  have hkept : ∀ index, index ≤ (c.state i).1.log.length →
      Held c f (c.state i).1.term ((c.state i).1.log.take index) →
        index ≤ s'.log.length ∧ Held c f s'.term (s'.log.take index) := by
    intro index hle hheld
    obtain ⟨rest, hrest⟩ := hgrows
    rw [hterm, ← hrest, List.take_append_of_le_length hle]
    exact ⟨by simp; omega, hheld⟩
  have hold : ∀ index, (f, index) ∈ matched →
      index ≤ s'.log.length ∧ Held c f s'.term (s'.log.take index) := fun index h =>
    hkept index (hc.matched i matched hrole₀ f index h).1 (hc.matched i matched hrole₀ f index h).2
  rcases hfrom with rfl | ⟨follower, acked, hmsg, rfl⟩
  · exact hold index hmem
  rcases mem_raise hmem with ⟨rfl, rfl⟩ | hmem
  · by_cases hle : matchedOf matched f ≤ acked
    · rw [Nat.max_eq_left hle]
      rcases hpending _ hmsg with ⟨src, hnet⟩ | h | h
      · obtain ⟨l, hled, hlen, hheld⟩ := hc.acks src i _ f acked hnet
        obtain ⟨rest, hrest⟩ := hl.led_prefix hv hleader₀ hled
        refine hkept acked (by rw [← hrest]; simp; omega) ?_
        rwa [← hrest, List.take_append_of_le_length hlen]
      · cases h
      · cases h
    · rw [Nat.max_eq_right (by omega)]
      rcases matchedOf_mem matched f with hzero | hmem
      · omega
      · exact hold _ hmem
  · exact hold index hmem

theorem grow (hv : Votes c) (hterms : Terms c) (hl : Logs c) (hc : Standing c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg) :
    Standing (c.grow i ((s', c.seen i), effs)) := by
  have hself : s' ∈ (c.grow i ((s', c.seen i), effs)).seen i := mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩)
  refine ⟨fun a p hp hcandidate => ?_, fun a p hp q hq hpc hqc hterm => ?_,
    fun src dst term candidate lastIndex last hmem => ?_, fun voter term candidate hvoted => ?_,
    fun src dst term follower index hmem => ?_, fun a matched hrole f index hmem => ?_⟩
  · rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
    · exact hc.behind a p hp hcandidate
    · exact hc.behind_moved hterms hmoves hcandidate
  · rcases mem_seen_grow.mp hp with hp' | ⟨rfl, rfl⟩
    · rcases mem_seen_grow.mp hq with hq' | ⟨rfl, rfl⟩
      · exact hc.oneLog a p hp' q hq' hpc hqc hterm
      · exact hc.oneLog_moved hv hmoves hqc hp' hpc hterm
    · rcases mem_seen_grow.mp hq with hq' | ⟨_, rfl⟩
      · exact (hc.oneLog_moved hv hmoves hpc hq' hqc hterm.symm).symm
      · rfl
  · rcases SysState.mem_grow_net.mp hmem with hmem | ⟨_, hnew⟩
    · obtain ⟨p, hp, h⟩ := hc.requests src dst term candidate lastIndex last hmem
      exact ⟨p, mem_seen_grow.mpr (.inl hp), h⟩
    · obtain ⟨rfl, rfl, h⟩ := hmoves.sent _ hnew
      exact ⟨s', hself, rfl, h⟩
  · rcases hvoted.of_grow with hold | ⟨rfl, rfl, hnew⟩
    · exact Nat.le_trans (hc.reached voter term candidate hold) (grow_term_le hmoves candidate)
    · exact hc.reached_moved hv hmoves hpending hnew
  · rcases SysState.mem_grow_net.mp hmem with hmem | ⟨_, hnew⟩
    · obtain ⟨l, hled, hlen, hheld⟩ := hc.acks src dst term follower index hmem
      exact ⟨l, hled.grow, hlen, hheld.grow⟩
    · exact acked_moved hv hl hmoves hpending hnew
  · by_cases ha : a = i
    · subst ha
      rw [SysState.grow_state_self] at hrole ⊢
      exact (hc.matched_moved hv hl hmoves hpending hrole hmem).imp_right Held.grow
    · rw [SysState.grow_state_of_ne _ _ ha] at hrole ⊢
      exact (hc.matched a matched hrole f index hmem).imp_right Held.grow

end Standing

theorem standing_monotone :
    (recording N config machine).Monotone fun c => Replicating c ∧ Standing c := by
  refine replicating_monotone.and .blank (fun _ _ _ hc => hc.below)
    (fun _ x _ hc => hc.input x) ?_ ?_
  · exact fun c i msg hp _ hc hpending => hc.grow hp.1.1.2 hp.1.2 hp.2
      (step_moves config Enum.all machine i _ msg) (hp.1.1.1.pending hpending)
  · exact fun c i hp _ hc => hc.grow hp.1.1.2 hp.1.2 hp.2
      (recover_moves config Enum.all machine i _) pending_none

end RaftKV
