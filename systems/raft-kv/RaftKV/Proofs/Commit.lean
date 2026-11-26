/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Standing

/-!
# What is committed stays

With both switches of `Config` on, for every finite set of nodes, every machine and every
environment model: a node has committed no more than it has (`commit_le_length`), what two nodes
have both committed is the same (`committed_agree`), and a leader has what every node no further
on in terms has committed (`leader_complete`). In terms of the history: what a majority held in a
term is in the log of every leader of a later term (`leader_completeness`).

Ongaro's argument takes the first later leader without a committed entry and finds a
contradiction in the voter it shares with the majority that held the entry. Here it is an
invariant (`Safe`), which has to say something before an entry is committed, since a vote may be
cast while the majority is still forming. So it speaks of what is *choosable*: a start of a
leader's log, ending in an entry of the leader's term, that some majority has held in that term
or may yet, because it has not moved on. Whatever is choosable is in every later leader's log,
in the log of every node that held it, and in the log of every candidate such a node votes for.
Once no majority can hold it any more, nothing is claimed. The induction over terms disappears:
an entry of a later term in a candidate's log names, through `Logs.sourced`, a leader of that
term in the history, of which the invariant already speaks.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

section Lists

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]

theorem termAt_mem {log : List (Entry N C)} {k : Nat} (hk : 0 < k) (hlen : k ≤ log.length) :
    ∃ entry ∈ log, entry.term = termAt log k := by
  have h : k - 1 < log.length := by omega
  exact ⟨log[k - 1], List.getElem_mem h, by simp [termAt, Nat.ne_of_gt hk, h]⟩

theorem termAt_mono {log : List (Entry N C)} (hsorted : log.Pairwise (·.term ≤ ·.term))
    {j k : Nat} (hj : 0 < j) (hjk : j ≤ k) (hk : k ≤ log.length) :
    termAt log j ≤ termAt log k := by
  have hj' : j - 1 < log.length := by omega
  have hk' : k - 1 < log.length := by omega
  rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
  · exact Nat.le_refl _
  · have := List.pairwise_iff_getElem.mp hsorted (j - 1) (k - 1) hj' hk' (by omega)
    simpa [termAt, Nat.ne_of_gt hj, Nat.ne_of_gt (Nat.lt_of_lt_of_le hj hjk), hj', hk'] using this

theorem take_eq_of_take_prefix {α : Type} {a l : List α} {n : Nat} (hn : n ≤ a.length)
    (h : a.take n <+: l) : n ≤ l.length ∧ l.take n = a.take n := by
  have hlen := h.length_le
  have htake := List.prefix_iff_eq_take.mp h
  rw [List.length_take, Nat.min_eq_left hn] at hlen htake
  exact ⟨hlen, htake.symm⟩

end Lists

section Chosen

variable {c : SysState (recording N config machine)} {i : N} {msg : Option (Msg N C)}
  {s' : Node N C M} {effs : List (Effect (sig N C R) i)} {term : Nat} {pfx : List (Entry N C)}

/-- `pfx` is the start of a leader's log up to an entry of the leader's term, and some majority
has held it in that term or may yet. -/
def Choosable (c : SysState (recording N config machine)) (term : Nat)
    (pfx : List (Entry N C)) : Prop :=
  pfx ≠ [] ∧ termAt pfx pfx.length = term ∧ Within c term pfx ∧
    ∃ quorum, Quorum.isMajority Enum.all quorum = true ∧
      ∀ v ∈ quorum, Held c v term pfx ∨ (c.state v).1.term ≤ term

/-- A majority has held `pfx` in `term`: it is committed, whether or not anyone knows. -/
def Chosen (c : SysState (recording N config machine)) (term : Nat)
    (pfx : List (Entry N C)) : Prop :=
  pfx ≠ [] ∧ termAt pfx pfx.length = term ∧ Within c term pfx ∧
    ∃ quorum, Quorum.isMajority Enum.all quorum = true ∧ ∀ v ∈ quorum, Held c v term pfx

theorem Chosen.choosable (h : Chosen c term pfx) : Choosable c term pfx :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.imp fun _ hq => ⟨hq.1, fun v hv => .inl (hq.2 v hv)⟩⟩

theorem Chosen.grow (h : Chosen c term pfx) :
    Chosen (c.grow i ((s', c.seen i), effs)) term pfx :=
  ⟨h.1, h.2.1, h.2.2.1.grow, h.2.2.2.imp fun _ hq => ⟨hq.1, fun v hv => (hq.2 v hv).grow⟩⟩

/-- What is committed as far as a node in `term` can know: a start of something chosen in a term
up to its own. -/
def Committed (c : SysState (recording N config machine)) (term : Nat)
    (pfx : List (Entry N C)) : Prop :=
  pfx = [] ∨ ∃ chosenTerm chosen, chosenTerm ≤ term ∧ Chosen c chosenTerm chosen ∧ pfx <+: chosen

theorem Committed.grow (h : Committed c term pfx) :
    Committed (c.grow i ((s', c.seen i), effs)) term pfx :=
  h.imp id fun ⟨chosenTerm, chosen, hle, hchosen, hp⟩ => ⟨chosenTerm, chosen, hle, hchosen.grow, hp⟩

theorem Committed.mono (h : Committed c term pfx) {pfx' : List (Entry N C)} (hp : pfx' <+: pfx) :
    Committed c term pfx' :=
  h.elim (fun hnil => .inl (List.prefix_nil.mp (hnil ▸ hp)))
    fun ⟨chosenTerm, chosen, hle, hchosen, hpc⟩ => .inr ⟨chosenTerm, chosen, hle, hchosen, hp.trans hpc⟩

theorem Committed.later (h : Committed c term pfx) {later : Nat} (hle : term ≤ later) :
    Committed c later pfx :=
  h.imp id fun ⟨chosenTerm, chosen, hct, hchosen, hp⟩ =>
    ⟨chosenTerm, chosen, Nat.le_trans hct hle, hchosen, hp⟩

/-- The one way something becomes choosable: a leader adds an entry, and its whole log is the
new thing. -/
def Appended (s s' : Node N C M) (term : Nat) (pfx : List (Entry N C)) : Prop :=
  isLeader s = true ∧ s'.term = s.term ∧ s.term = term ∧ pfx = s'.log ∧
    ∃ entry, entry.term = term ∧ s'.log = s.log ++ [entry]

theorem Choosable.of_grow (hr : Replicating c) (hs : Standing c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (h : Choosable (c.grow i ((s', c.seen i), effs)) term pfx) :
    Choosable c term pfx ∨ Appended (c.state i).1 s' term pfx := by
  obtain ⟨hne, hlast, ⟨l, ⟨a, p, hp, hleader, hterm, rfl⟩, hprefix⟩, quorum, hmajority, hheld⟩ := h
  have hquorum : ∀ v ∈ quorum, Held c v term pfx ∨ (c.state v).1.term ≤ term := by
    intro v hv
    rcases hheld v hv with ⟨q, hq, hqterm, hqlog⟩ | hable
    · rcases mem_seen_grow.mp hq with hq | ⟨rfl, rfl⟩
      · exact .inl ⟨q, hq, hqterm, hqlog⟩
      · exact .inr (hqterm ▸ hmoves.term_le)
    · exact .inr (Nat.le_trans (grow_term_le hmoves v) hable)
  have hfrom : ∀ l, Led c term l → pfx <+: l → Choosable c term pfx := fun l hled hpl =>
    ⟨hne, hlast, ⟨l, hled, hpl⟩, quorum, hmajority, hquorum⟩
  rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
  · exact .inl (hfrom _ ⟨a, p, hp, hleader, hterm, rfl⟩ hprefix)
  obtain ⟨entry, hentry, hentryTerm⟩ := termAt_mem (List.length_pos_iff.mpr hne) (Nat.le_refl _)
  have hin : entry ∈ p.log := hprefix.mem hentry
  rcases hmoves.leader hleader with ⟨hnew, _, _, hlog⟩ | ⟨hsame, hlog, votes₀, _, hrole₀, _⟩ |
    ⟨hsame, hleader₀, _⟩
  · have := hr.terms.logs a entry (hlog ▸ hin)
    omega
  · have := hs.behind a _ (c.mem_seen_self a) ⟨votes₀, hrole₀⟩ entry (hlog ▸ hin)
    omega
  · have hled₀ : Led c term (c.state a).1.log :=
      ⟨a, _, c.mem_seen_self a, hleader₀, hsame.symm.trans hterm, rfl⟩
    rcases hmoves.log with hlog | ⟨_, added, _, hlog⟩ | ⟨hrole, _⟩
    · exact .inl (hfrom _ hled₀ (hlog ▸ hprefix))
    · rcases List.prefix_concat_iff.mp (hlog ▸ hprefix) with heq | hpl
      · refine .inr ⟨hleader₀, hsame, hsame.symm.trans hterm, heq.trans hlog.symm, added, ?_, hlog⟩
        rw [heq, List.length_append, List.length_singleton, termAt_append_length] at hlast
        exact hlast
      · exact .inl (hfrom _ hled₀ hpl)
    · simp [isLeader, hrole] at hleader

/-- No log anywhere has an entry of a leader's term past the end of that leader's log. -/
theorem Logs.none_beyond (hv : Votes c) (hl : Logs c) {a v : N}
    (hleader : isLeader (c.state a).1 = true) {q : Node N C M} (hq : q ∈ c.seen v) {k : Nat}
    (hk : (c.state a).1.log.length < k) (hlen : k ≤ q.log.length)
    (hterm : termAt q.log k = (c.state a).1.term) : False := by
  obtain ⟨l, hled, htake⟩ := hl.sourced v q hq k (by omega) hlen
  have hprefix := (hl.led_prefix hv hleader (hterm ▸ hled)).length_le
  have := congrArg List.length htake
  simp only [List.length_take] at this
  omega

/-- Only the leader that added an entry holds it yet. -/
theorem Appended.held (hr : Replicating c) (h : Appended (c.state i).1 s' term pfx) {v : N}
    (hheld : Held (c.grow i ((s', c.seen i), effs)) v term pfx) : v = i := by
  obtain ⟨hleader, _, hterm, rfl, entry, hentry, hlog⟩ := h
  obtain ⟨q, hq, _, hqlog⟩ := hheld
  rcases mem_seen_grow.mp hq with hq | ⟨rfl, _⟩
  · have hlen : (c.state i).1.log.length + 1 ≤ q.log.length := by
      simpa [hlog] using hqlog.length_le
    refine (hr.logs.none_beyond hr.votes hleader hq (Nat.lt_succ_self _) hlen ?_).elim
    rw [← termAt_of_prefix hqlog (by simp [hlog]), hlog, termAt_append_length, hentry, hterm]
  · rfl

end Chosen

/-- The invariant, given `Replicating` and `Standing`: what is choosable stays. -/
structure Safe (c : SysState (recording N config machine)) : Prop where
  leaders : ∀ term pfx, Choosable c term pfx → ∀ a, ∀ p ∈ c.seen a, isLeader p = true →
    term < p.term → pfx <+: p.log
  holders : ∀ term pfx, Choosable c term pfx → ∀ v, Held c v term pfx →
    pfx <+: (c.state v).1.log
  /-- A node that held it votes, in a later term, only for a candidate that has it. -/
  voters : ∀ term pfx, Choosable c term pfx → ∀ v, Held c v term pfx → ∀ later candidate,
    term < later → VotedFor c v later candidate → ∀ p ∈ c.seen candidate, p.term = later →
      IsCandidate p → pfx <+: p.log

namespace Safe

variable {c : SysState (recording N config machine)} {term : Nat} {pfx : List (Entry N C)}

theorem blank : Safe (SysState.blank (recording N config machine)) := by
  have hnone : ∀ term pfx, ¬Choosable (SysState.blank (recording N config machine)) term pfx := by
    rintro term pfx ⟨_, _, ⟨l, ⟨a, p, hp, hleader, _⟩, _⟩, _⟩
    obtain rfl := List.mem_singleton.mp hp
    simp [isLeader, SysState.blank, recording, System.withPast, System.withGhost, node] at hleader
  exact ⟨fun term pfx h => (hnone term pfx h).elim, fun term pfx h => (hnone term pfx h).elim,
    fun term pfx h => (hnone term pfx h).elim⟩

/-- A leader's log, of a term no earlier, has what is choosable or is itself the start of it. -/
theorem prefix_of_led (hr : Replicating c) (hk : Safe c) (hch : Choosable c term pfx) {later : Nat}
    {l : List (Entry N C)} (hled : Led c later l) (hle : term ≤ later) :
    pfx <+: l ∨ l <+: pfx := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · obtain ⟨l₀, hled₀, hpl⟩ := hch.2.2.1
    rcases hr.logs.led_chain hr.votes hled₀ hled with h | h
    · exact .inl (hpl.trans h)
    · exact List.prefix_or_prefix_of_prefix hpl h
  · obtain ⟨a, p, hp, hleader, rfl, rfl⟩ := hled
    exact .inl (hk.leaders term pfx hch a p hp hleader hlt)

/-- The same of a start of such a log, which is what a follower takes from one batch. -/
theorem prefix_of_within (hr : Replicating c) (hk : Safe c) (hch : Choosable c term pfx)
    {later : Nat} {l : List (Entry N C)} (hwithin : Within c later l) (hle : term ≤ later) :
    pfx <+: l ∨ l <+: pfx := by
  obtain ⟨whole, hled, hstart⟩ := hwithin
  rcases prefix_of_led hr hk hch hled hle with h | h
  · exact List.prefix_or_prefix_of_prefix h hstart
  · exact .inr (hstart.trans h)

/-- A candidate whose log is not behind that of a node with something choosable has it too. -/
theorem up_to_date (hr : Replicating c) (hk : Safe c) (hch : Choosable c term pfx)
    {log : List (Entry N C)} (hlog : pfx <+: log) (hsourced : Sourced c log)
    (hsorted : log.Pairwise (·.term ≤ ·.term)) {candidate : N} {p : Node N C M}
    (hp : p ∈ c.seen candidate)
    (hfresh : lastTerm log < lastTerm p.log ∨
      (lastTerm p.log = lastTerm log ∧ log.length ≤ p.log.length)) : pfx <+: p.log := by
  have hpos : 0 < pfx.length := List.length_pos_iff.mpr hch.1
  have hle : term ≤ lastTerm log := by
    have := termAt_mono hsorted hpos hlog.length_le (Nat.le_refl _)
    rwa [← termAt_of_prefix hlog (Nat.le_refl _), hch.2.1] at this
  have hlen := hlog.length_le
  rcases hfresh with hlt | ⟨heq, hlonger⟩
  · have hm : 0 < p.log.length := by
      rcases Nat.eq_zero_or_pos p.log.length with h | h
      · simp [lastTerm, termAt, h] at hlt
      · exact h
    obtain ⟨_, ⟨b, pb, hpb, hleader, hpbterm, rfl⟩, htake⟩ :=
      hr.logs.sourced candidate p hp _ hm (Nat.le_refl _)
    rw [List.take_length] at htake
    have hpp : p.log <+: pb.log := htake ▸ List.take_prefix p.log.length pb.log
    have hpl := hk.leaders term pfx hch b pb hpb hleader
      (hpbterm ▸ Nat.lt_of_le_of_lt hle hlt)
    refine List.prefix_of_prefix_length_le hpl hpp (Nat.le_of_not_lt fun hshort => ?_)
    have := termAt_mono (hr.logs.sorted b pb hpb) hm (Nat.le_of_lt hshort) hpl.length_le
    rw [← termAt_of_prefix hpp (Nat.le_refl _), ← termAt_of_prefix hpl (Nat.le_refl _),
      hch.2.1] at this
    exact absurd (Nat.lt_of_le_of_lt hle hlt) (Nat.not_lt.mpr this)
  · obtain ⟨la, hla, htakeA⟩ := hsourced _ (by omega) (Nat.le_refl _)
    obtain ⟨lb, hlb, htakeB⟩ := hr.logs.sourced candidate p hp _ (by omega) (Nat.le_refl _)
    rw [List.take_length] at htakeA htakeB
    have hA : log <+: la := htakeA ▸ List.take_prefix log.length la
    have hB : p.log <+: lb := htakeB ▸ List.take_prefix p.log.length lb
    have hlb' : Led c (termAt log log.length) lb :=
      (show termAt p.log p.log.length = termAt log log.length from heq) ▸ hlb
    refine hlog.trans ?_
    rcases hr.logs.led_chain hr.votes hla hlb' with h | h
    · exact List.prefix_of_prefix_length_le (hA.trans h) hB hlonger
    · exact List.prefix_of_prefix_length_le hA (hB.trans h) hlonger

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- Nobody leads a term past the one in which an entry has just been added. -/
theorem no_later_leader (hr : Replicating c) (hv' : Votes (c.grow i ((s', c.seen i), effs)))
    (happ : Appended (c.state i).1 s' term pfx)
    (hch' : Choosable (c.grow i ((s', c.seen i), effs)) term pfx) {a : N} {p : Node N C M}
    (hp : p ∈ (c.grow i ((s', c.seen i), effs)).seen a) (hleader : isLeader p = true)
    (hterm : term < p.term) : False := by
  obtain ⟨quorum, hmajority, hheld⟩ := hch'.2.2.2
  obtain ⟨electors, helected, hvotes⟩ := hv'.elected a p hp hleader
  obtain ⟨v, hv, hve⟩ := Quorum.majority_inter hmajority helected
  obtain ⟨r, hrmem, hrterm, _⟩ := hvotes v hve
  have hpast := hv'.seen_term_le hrmem
  rcases hheld v hv with hheldv | hable
  · obtain rfl := happ.held hr hheldv
    have := happ.2.1
    have := happ.2.2.1
    simp only [SysState.grow_state_self] at hpast
    omega
  · omega

/-- A node that comes to lead a later term has what is choosable: it held it itself, or a node
that did voted for it. -/
theorem leader_moved (hk : Safe c)
    (hv' : Votes (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hch : Choosable c term pfx)
    (hch' : Choosable (c.grow i ((s', c.seen i), effs)) term pfx) (hleader : isLeader s' = true)
    (hterm : term < s'.term) : pfx <+: s'.log := by
  obtain ⟨quorum, hmajority, hheld⟩ := hch'.2.2.2
  have hold : ∀ v ∈ quorum, term < ((c.grow i ((s', c.seen i), effs)).state v).1.term →
      Held c v term pfx := by
    intro v hv hlater
    rcases hheld v hv with ⟨q, hq, hqterm, hqlog⟩ | hable
    · rcases mem_seen_grow.mp hq with hq | ⟨rfl, rfl⟩
      · exact ⟨q, hq, hqterm, hqlog⟩
      · omega
    · omega
  rcases hmoves.leader hleader with ⟨hnew, hone, _, hlog⟩ |
    ⟨hsame, hlog, votes₀, votes, hrole₀, _⟩ | ⟨hsame, hleader₀, hgrows⟩
  · obtain ⟨v, hv, hvi⟩ := Quorum.majority_inter hmajority hone
    obtain rfl := List.mem_singleton.mp hvi
    exact hlog ▸ hk.holders term pfx hch v (hold v hv (by simpa using hterm))
  · obtain ⟨electors, helected, hvotes⟩ :=
      hv'.elected i s' (mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩)) hleader
    obtain ⟨v, hv, hve⟩ := Quorum.majority_inter hmajority helected
    have hvoted := hvotes v hve
    have hheldv : Held c v term pfx := by
      obtain ⟨r, hrmem, hrterm, _⟩ := hvoted
      have := hv'.seen_term_le hrmem
      exact hold v hv (by omega)
    have hterm₀ : term < (c.state i).1.term := by omega
    rw [hsame] at hvoted
    rcases hvoted.of_grow with hvoted | ⟨rfl, _⟩
    · exact hlog ▸ hk.voters term pfx hch v hheldv _ i hterm₀ hvoted _ (c.mem_seen_self i) rfl
        ⟨votes₀, hrole₀⟩
    · exact hlog ▸ hk.holders term pfx hch v hheldv
  · exact (hk.leaders term pfx hch i _ (c.mem_seen_self i) hleader₀ (by omega)).trans hgrows

/-- A node that held something choosable still has it after it moves. -/
theorem holder_moved (hr : Replicating c) (hk : Safe c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcut : Logs.Cut c msg)
    (hch : Choosable c term pfx) (hheld : Held c i term pfx) : pfx <+: s'.log := by
  have hown := hk.holders term pfx hch i hheld
  have hle : term ≤ s'.term := by
    obtain ⟨q, hq, hqterm, _⟩ := hheld
    have := hr.votes.seen_term_le hq
    have := hmoves.term_le
    omega
  rcases hmoves.log with hlog | ⟨_, entry, _, hlog⟩ |
    ⟨_, leader, prev, entries, commit, hmsg, hprev, hlog⟩
  · exact hlog ▸ hown
  · exact hlog ▸ hown.trans (List.prefix_append _ _)
  · obtain ⟨l, hled, hlen, hterm, rfl⟩ := hcut _ leader prev _ _ commit hmsg
    rcases hr.logs.accepted hr.votes hled hprev hlen hterm hlog with h | h
    · exact h.2 ▸ hown
    · rw [h.2]
      exact (prefix_of_within hr hk hch hled hle).resolve_right fun hlp => h.1 (hlp.trans hown)

end Safe

section Votes

variable {c : SysState (recording N config machine)} {i : N} {msg : Option (Msg N C)}
  {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- A vote after a move is one from before, or the mover's own on starting a term, or one it has
just granted. -/
theorem VotedFor.of_moves (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    {voter candidate : N} {term : Nat}
    (h : VotedFor (c.grow i ((s', c.seen i), effs)) voter term candidate) :
    VotedFor c voter term candidate ∨ (voter = i ∧ s'.term = term ∧
      ((s'.term = (c.state i).1.term + 1 ∧ candidate = i ∧ s'.log = (c.state i).1.log) ∨
        ∃ lastIndex last, msg = some (.requestVote s'.term candidate lastIndex last) ∧
          s'.log = (c.state i).1.log ∧ (config.votesForUpToDateOnly = true →
            lastTerm (c.state i).1.log < last ∨
              (last = lastTerm (c.state i).1.log ∧ (c.state i).1.log.length ≤ lastIndex)))) := by
  rcases h.of_grow with hold | ⟨rfl, hterm, hnew⟩
  · exact .inl hold
  · rcases hmoves.vote candidate hnew with ⟨hsame, hkept⟩ | h | h
    · exact .inl ⟨_, c.mem_seen_self voter, hsame.symm.trans hterm, hkept⟩
    · exact .inr ⟨rfl, hterm, .inl h⟩
    · exact .inr ⟨rfl, hterm, .inr h⟩

end Votes

namespace Safe

variable {c : SysState (recording N config machine)} {term : Nat} {pfx : List (Entry N C)}
  {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

theorem voter_moved (hr : Replicating c) (hs : Standing c) (hk : Safe c)
    (hup : config.votesForUpToDateOnly = true)
    (hs' : Standing (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    (hch : Choosable c term pfx) {v : N} (hheld : Held c v term pfx) {later : Nat}
    {candidate : N} (hlater : term < later)
    (hvoted : VotedFor (c.grow i ((s', c.seen i), effs)) v later candidate) {p : Node N C M}
    (hp : p ∈ (c.grow i ((s', c.seen i), effs)).seen candidate) (hpterm : p.term = later)
    (hcandidate : IsCandidate p) : pfx <+: p.log := by
  have hown := hk.holders term pfx hch v hheld
  rcases hvoted.of_moves hmoves with
    hold | ⟨rfl, hterm', hself | ⟨lastIndex, last, hmsg, hlog, hfresh⟩⟩
  · rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
    · exact hk.voters term pfx hch v hheld later candidate hlater hold p hp hpterm hcandidate
    · obtain ⟨votes, hrole⟩ := hcandidate
      rcases hmoves.candidate votes hrole with ⟨hnew, _⟩ | ⟨hsame, hlog, votes₀, hrole₀, _⟩
      · have := hs.reached v later candidate hold
        omega
      · exact hlog ▸ hk.voters term pfx hch v hheld later candidate hlater hold _
          (c.mem_seen_self candidate) (hsame.symm.trans hpterm) ⟨votes₀, hrole₀⟩
  · obtain ⟨hnew, rfl, hlog⟩ := hself
    rcases mem_seen_grow.mp hp with hp | ⟨_, rfl⟩
    · have := hr.votes.seen_term_le hp
      omega
    · exact hlog ▸ hown
  · rcases hpending _ hmsg with ⟨src, hnet⟩ | h | h
    · obtain ⟨p₀, hp₀, hp₀term, hp₀candidate, rfl, rfl⟩ :=
        hs.requests src v _ candidate lastIndex last hnet
      rw [← hs'.oneLog candidate p₀ (mem_seen_grow.mpr (.inl hp₀)) p hp hp₀candidate hcandidate
        (by omega)]
      exact up_to_date hr hk hch hown (hr.logs.sourced v _ (c.mem_seen_self v))
        (hr.logs.sorted v _ (c.mem_seen_self v)) hp₀ (hfresh hup)
    · cases h
    · cases h

theorem grow (hr : Replicating c) (hs : Standing c) (hk : Safe c)
    (hup : config.votesForUpToDateOnly = true)
    (hv' : Votes (c.grow i ((s', c.seen i), effs)))
    (hs' : Standing (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg) :
    Safe (c.grow i ((s', c.seen i), effs)) := by
  refine ⟨fun term pfx hch' a p hp hleader hterm => ?_, fun term pfx hch' v hheld => ?_,
    fun term pfx hch' v hheld later candidate hlater hvoted p hp hpterm hcandidate => ?_⟩
  · rcases hch'.of_grow hr hs hmoves with hch | happ
    · rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
      · exact hk.leaders term pfx hch a p hp hleader hterm
      · exact leader_moved hk hv' hmoves hch hch' hleader hterm
    · exact (no_later_leader hr hv' happ hch' hp hleader hterm).elim
  · rcases hch'.of_grow hr hs hmoves with hch | happ
    · obtain ⟨q, hq, hqterm, hqlog⟩ := hheld
      by_cases hv : v = i
      · subst hv
        rw [SysState.grow_state_self]
        rcases mem_seen_grow.mp hq with hq | ⟨_, rfl⟩
        · exact holder_moved hr hk hmoves (hr.logs.cut_of_pending hpending) hch
            ⟨q, hq, hqterm, hqlog⟩
        · exact hqlog
      · rw [SysState.grow_state_of_ne _ _ hv]
        exact hk.holders term pfx hch v
          ⟨q, (mem_seen_grow.mp hq).resolve_right (hv ·.1), hqterm, hqlog⟩
    · obtain rfl := happ.held hr hheld
      rw [SysState.grow_state_self, happ.2.2.2.1]
      exact List.prefix_refl _
  · have hpast : term < ((c.grow i ((s', c.seen i), effs)).state v).1.term := by
      obtain ⟨r, hrmem, hrterm, _⟩ := hvoted
      have := hv'.seen_term_le hrmem
      omega
    rcases hch'.of_grow hr hs hmoves with hch | happ
    · have hheld₀ : Held c v term pfx := by
        obtain ⟨q, hq, hqterm, hqlog⟩ := hheld
        rcases mem_seen_grow.mp hq with hq | ⟨rfl, rfl⟩
        · exact ⟨q, hq, hqterm, hqlog⟩
        · simp only [SysState.grow_state_self] at hpast
          omega
      exact voter_moved hr hs hk hup hs' hmoves hpending hch hheld₀ hlater hvoted hp hpterm
        hcandidate
    · obtain rfl := happ.held hr hheld
      have := happ.2.1
      have := happ.2.2.1
      simp only [SysState.grow_state_self] at hpast
      omega

end Safe

theorem safe_monotone (hup : config.votesForUpToDateOnly = true) :
    (recording N config machine).Monotone fun c => (Replicating c ∧ Standing c) ∧ Safe c := by
  refine standing_monotone.and_state .blank
    (fun _ _ _ _ _ hk => ⟨hk.leaders, hk.holders, hk.voters⟩) ?_ ?_
  · exact fun c i msg hp hp' hk hpending => hk.grow hp.1 hp.2 hup hp'.1.votes hp'.2
      (step_moves config Enum.all machine i _ msg) (hp.1.timers.pending hpending)
  · exact fun c i hp hp' hk => hk.grow hp.1 hp.2 hup hp'.1.votes hp'.2
      (recover_moves config Enum.all machine i _) pending_none

/-- The invariant of the commit index, given the rest: a node has committed a start of its log
that is committed, and an `append` in flight claims no more of its leader's log, of which it
carries a batch. -/
structure Commits (c : SysState (recording N config machine)) : Prop where
  nodes : ∀ a, (c.state a).1.commit ≤ (c.state a).1.log.length ∧
    Committed c (c.state a).1.term ((c.state a).1.log.take (c.state a).1.commit)
  appends : ∀ src dst term leader prev prevTerm entries commit,
    (⟨src, dst, .append term leader prev prevTerm entries commit⟩ : Envelope (sig N C R)) ∈ c.net →
      ∃ l, Led c term l ∧ prev ≤ l.length ∧ prevTerm = termAt l prev ∧ entries <+: l.drop prev ∧
        commit ≤ l.length ∧ Committed c term (l.take commit)

namespace Commits

variable {c : SysState (recording N config machine)}

theorem blank : Commits (SysState.blank (recording N config machine)) := by
  constructor <;>
    simp [SysState.blank, recording, System.withPast, System.withGhost, node, Committed]

variable {term : Nat} {pfx : List (Entry N C)}

/-- A start of a leader's log, of a term no earlier, has what is committed or is itself the
start of it. -/
theorem in_within (hr : Replicating c) (hk : Safe c) (hcommitted : Committed c term pfx)
    {later : Nat} {l : List (Entry N C)} (hled : Within c later l) (hle : term ≤ later) :
    pfx <+: l ∨ l <+: pfx := by
  rcases hcommitted with rfl | ⟨chosenTerm, chosen, hct, hchosen, hpc⟩
  · exact .inl List.nil_prefix
  · rcases hk.prefix_of_within hr hchosen.choosable hled (Nat.le_trans hct hle) with h | h
    · exact .inl (hpc.trans h)
    · exact List.prefix_or_prefix_of_prefix hpc h

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- The start of a leader's log that replaces a follower's has what the follower had
committed. -/
theorem kept (hr : Replicating c) (hk : Safe c) (hc : Commits c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) {l : List (Entry N C)}
    (hled : Within c s'.term l) (hnot : ¬l <+: (c.state i).1.log) :
    (c.state i).1.commit ≤ l.length ∧
      l.take (c.state i).1.commit = (c.state i).1.log.take (c.state i).1.commit := by
  rcases in_within hr hk (hc.nodes i).2 hled hmoves.term_le with h | h
  · exact take_eq_of_take_prefix (hc.nodes i).1 h
  · exact absurd (h.trans (List.take_prefix _ _)) hnot

/-- A node whose commit index stays has still committed a start of its log. -/
theorem unmoved (hr : Replicating c) (hk : Safe c) (hc : Commits c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcut : Logs.Cut c msg)
    (hcommit : s'.commit = (c.state i).1.commit) :
    s'.commit ≤ s'.log.length ∧
      Committed (c.grow i ((s', c.seen i), effs)) s'.term (s'.log.take s'.commit) := by
  obtain ⟨hlen₀, hcommitted₀⟩ := hc.nodes i
  have hstays := (hcommitted₀.later hmoves.term_le).grow (i := i) (s' := s') (effs := effs)
  rw [hcommit]
  rcases hmoves.log with hlog | ⟨_, entry, _, hlog⟩ |
    ⟨_, leader, prev, entries, commit, hmsg, hprev, hlog⟩
  · rw [hlog]
    exact ⟨hlen₀, hstays⟩
  · rw [hlog, List.take_append_of_le_length hlen₀]
    exact ⟨by simp; omega, hstays⟩
  · obtain ⟨l, hled, hlen, hterm, rfl⟩ := hcut _ leader prev _ _ commit hmsg
    rcases hr.logs.accepted hr.votes hled hprev hlen hterm hlog with h | h
    · rw [h.2]
      exact ⟨hlen₀, hstays⟩
    · obtain ⟨hle, htake⟩ := hc.kept hr hk hmoves hled h.1
      rw [h.2, htake]
      exact ⟨hle, hstays⟩

/-- What a leader commits by counting, a majority has held in its term. -/
theorem advanced (hown : config.commitsOwnTermOnly = true)
    (hs' : Standing (c.grow i ((s', c.seen i), effs))) (hle : s'.commit ≤ s'.log.length)
    (hpos : 0 < s'.commit) {matched : List (N × Nat)} (hrole : s'.role = .leader matched)
    (hmajority : Quorum.isMajority Enum.all (holders i matched s'.commit) = true)
    (hterm : config.commitsOwnTermOnly = true → termAt s'.log s'.commit = s'.term) :
    Chosen (c.grow i ((s', c.seen i), effs)) s'.term (s'.log.take s'.commit) := by
  have hself : s' ∈ (c.grow i ((s', c.seen i), effs)).seen i := mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩)
  have hlength : (s'.log.take s'.commit).length = s'.commit := by
    rw [List.length_take, Nat.min_eq_left hle]
  refine ⟨fun h => ?_, ?_, ⟨s'.log, ⟨i, s', hself, isLeader_iff.mpr ⟨matched, hrole⟩, rfl, rfl⟩,
    List.take_prefix _ _⟩, holders i matched s'.commit, hmajority, fun v hv => ?_⟩
  · rw [h] at hlength
    simp at hlength
    omega
  · rw [hlength, termAt_of_prefix (List.take_prefix _ _) (Nat.le_of_eq hlength.symm)]
    exact hterm hown
  · simp only [holders, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at hv
    rcases hv with rfl | ⟨⟨f, index⟩, ⟨hmem, hindex⟩, rfl⟩
    · exact ⟨s', hself, rfl, List.take_prefix _ _⟩
    · have hheld := (hs'.matched i matched (by simpa using hrole) f index hmem).2
      rw [SysState.grow_state_self] at hheld
      exact hheld.mono (List.take_prefix_take_left hindex)

/-- A follower that takes an `append` has committed a start of its log, as far as the leader
said of what it sent, and it had before. -/
theorem taken (hr : Replicating c) (hk : Safe c) (hc : Commits c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) {l : List (Entry N C)}
    {prev commit : Nat} (hled : Within c s'.term l) (hprev : prev ≤ (c.state i).1.log.length)
    (hlen : prev ≤ l.length) (hterm : termAt (c.state i).1.log prev = termAt l prev)
    (hlog : s'.log =
      (c.state i).1.log.take prev ++ merge ((c.state i).1.log.drop prev) (l.drop prev))
    (hclaimed : commit ≤ l.length) (hcommitted : Committed c s'.term (l.take commit))
    (hcommit : s'.commit = max (c.state i).1.commit commit) :
    s'.commit ≤ s'.log.length ∧
      Committed (c.grow i ((s', c.seen i), effs)) s'.term (s'.log.take s'.commit) := by
  obtain ⟨hlen₀, hcommitted₀⟩ := hc.nodes i
  have hstays := (hcommitted₀.later hmoves.term_le).grow (i := i) (s' := s') (effs := effs)
  have hsaid := hcommitted.grow (i := i) (s' := s') (effs := effs)
  rw [hcommit]
  rcases hr.logs.accepted hr.votes hled hprev hlen hterm hlog with h | h
  · obtain ⟨hle, htake⟩ := take_eq_of_take_prefix hclaimed ((List.take_prefix _ _).trans h.1)
    rw [h.2]
    rcases Nat.le_total (c.state i).1.commit commit with hmax | hmax
    · rw [Nat.max_eq_right hmax, htake]
      exact ⟨hle, hsaid⟩
    · rw [Nat.max_eq_left hmax]
      exact ⟨hlen₀, hstays⟩
  · obtain ⟨hle, htake⟩ := hc.kept hr hk hmoves hled h.1
    rw [h.2]
    rcases Nat.le_total (c.state i).1.commit commit with hmax | hmax
    · rw [Nat.max_eq_right hmax]
      exact ⟨hclaimed, hsaid⟩
    · rw [Nat.max_eq_left hmax, htake]
      exact ⟨hle, hstays⟩

theorem node_moved (hr : Replicating c) (hk : Safe c) (hc : Commits c)
    (hown : config.commitsOwnTermOnly = true)
    (hs' : Standing (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg) :
    s'.commit ≤ s'.log.length ∧
      Committed (c.grow i ((s', c.seen i), effs)) s'.term (s'.log.take s'.commit) := by
  rcases hmoves.commit with hcommit | ⟨hmore, hle, ⟨matched, hrole, hmajority⟩, hterm⟩ |
    ⟨leader, prev, entries, commit, hmsg, hprev, hlog, hcommit⟩
  · exact hc.unmoved hr hk hmoves (hr.logs.cut_of_pending hpending) hcommit
  · exact ⟨hle, .inr ⟨s'.term, _, Nat.le_refl _,
      advanced hown hs' hle (by omega) hrole hmajority hterm, List.prefix_refl _⟩⟩
  · rcases hpending _ hmsg with ⟨src, hnet⟩ | h | h
    · obtain ⟨l, hled, hlen, hterm, hbatch, hclaimed, hcommitted⟩ :=
        hc.appends src i _ leader prev _ _ commit hnet
      obtain ⟨cut, hcut, hcutlen, hcutterm, rfl⟩ := exists_cut hlen hbatch
      have hindex : prev + (cut.drop prev).length = cut.length := by
        rw [List.length_drop]
        omega
      rw [hindex] at hcommit
      refine hc.taken hr hk hmoves ⟨l, hled, hcut⟩ hprev (by omega) (hterm.trans hcutterm.symm)
        hlog (Nat.min_le_right _ _) ?_ hcommit
      rw [← take_of_prefix hcut (Nat.min_le_right _ _)]
      exact hcommitted.mono (List.take_prefix_take_left (Nat.min_le_left _ _))
    · cases h
    · cases h

theorem grow (hr : Replicating c) (hk : Safe c) (hc : Commits c)
    (hown : config.commitsOwnTermOnly = true)
    (hs' : Standing (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hpending : Pending c i msg) :
    Commits (c.grow i ((s', c.seen i), effs)) := by
  have hnode := hc.node_moved hr hk hown hs' hmoves hpending
  refine ⟨fun a => ?_, fun src dst term leader prev prevTerm entries commit hmem => ?_⟩
  · by_cases ha : a = i
    · subst ha
      rw [SysState.grow_state_self]
      exact hnode
    · rw [SysState.grow_state_of_ne _ _ ha]
      exact (hc.nodes a).imp_right Committed.grow
  · rcases SysState.mem_grow_net.mp hmem with hmem | ⟨_, hnew⟩
    · obtain ⟨l, hled, h₁, h₂, h₃, h₄, hcommitted⟩ :=
        hc.appends src dst term leader prev prevTerm entries commit hmem
      exact ⟨l, hled.grow, h₁, h₂, h₃, h₄, hcommitted.grow⟩
    · obtain ⟨hleader, rfl, h₁, h₂, h₃, rfl⟩ := hmoves.sent _ hnew
      exact ⟨s'.log, ⟨i, s', mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩), hleader, rfl, rfl⟩, h₁, h₂, h₃,
        hnode.1, hnode.2⟩

end Commits

/-- Everything the proof of commitment keeps. -/
structure Committing (c : SysState (recording N config machine)) : Prop where
  replicating : Replicating c
  standing : Standing c
  safe : Safe c
  commits : Commits c

theorem committing_monotone (hup : config.votesForUpToDateOnly = true)
    (hown : config.commitsOwnTermOnly = true) :
    (recording N config machine).Monotone Committing := by
  refine ((safe_monotone hup).and_net .blank (fun _ _ _ _ _ hc hnet => ⟨hc.nodes,
    fun src dst term leader prev prevTerm entries commit h => hc.appends src dst term leader prev
      prevTerm entries commit (mem_of_not_propose hnet h nofun)⟩) ?_ ?_).of_iff fun c =>
    ⟨fun h => ⟨⟨⟨h.replicating, h.standing⟩, h.safe⟩, h.commits⟩, fun ⟨⟨⟨hr, hs⟩, hk⟩, hc⟩ =>
      ⟨hr, hs, hk, hc⟩⟩
  · exact fun c i msg hp hp' hc hpending => hc.grow hp.1.1 hp.2 hown hp'.1.2
      (step_moves config Enum.all machine i _ msg) (hp.1.1.timers.pending hpending)
  · exact fun c i hp hp' hc => hc.grow hp.1.1 hp.2 hown hp'.1.2
      (recover_moves config Enum.all machine i _) pending_none

section Theorems

variable {c : SysState (recording N config machine)}

/-- What two majorities held, in whatever terms, is one the start of the other. -/
theorem Chosen.comparable (hr : Replicating c) (hk : Safe c) {term₁ term₂ : Nat}
    {pfx₁ pfx₂ : List (Entry N C)} (h₁ : Chosen c term₁ pfx₁) (h₂ : Chosen c term₂ pfx₂) :
    pfx₁ <+: pfx₂ ∨ pfx₂ <+: pfx₁ := by
  have hlater : ∀ {term₁ term₂ : Nat} {pfx₁ pfx₂ : List (Entry N C)}, Chosen c term₁ pfx₁ →
      Chosen c term₂ pfx₂ → term₁ ≤ term₂ → pfx₁ <+: pfx₂ ∨ pfx₂ <+: pfx₁ := by
    intro term₁ term₂ pfx₁ pfx₂ h₁ h₂ hle
    obtain ⟨l, hled, hpl⟩ := h₂.2.2.1
    rcases hk.prefix_of_led hr h₁.choosable hled hle with h | h
    · exact List.prefix_or_prefix_of_prefix h hpl
    · exact .inr (hpl.trans h)
  rcases Nat.le_total term₁ term₂ with hle | hle
  · exact hlater h₁ h₂ hle
  · exact (hlater h₂ h₁ hle).symm

/-- What two nodes have committed is one the start of the other. -/
theorem Committed.comparable (hr : Replicating c) (hk : Safe c) {term₁ term₂ : Nat}
    {pfx₁ pfx₂ : List (Entry N C)} (h₁ : Committed c term₁ pfx₁) (h₂ : Committed c term₂ pfx₂) :
    pfx₁ <+: pfx₂ ∨ pfx₂ <+: pfx₁ := by
  rcases h₁ with rfl | ⟨_, chosen₁, _, hchosen₁, hp₁⟩
  · exact .inl List.nil_prefix
  rcases h₂ with rfl | ⟨_, chosen₂, _, hchosen₂, hp₂⟩
  · exact .inr List.nil_prefix
  rcases hchosen₁.comparable hr hk hchosen₂ with h | h
  · exact List.prefix_or_prefix_of_prefix (hp₁.trans h) hp₂
  · exact List.prefix_or_prefix_of_prefix hp₁ (hp₂.trans h)

/-- The node that leads a term has everything committed up to that term. -/
theorem Committed.in_leader (hr : Replicating c) (hk : Safe c) {term : Nat}
    {pfx : List (Entry N C)} (h : Committed c term pfx) {a : N}
    (hleader : isLeader (c.state a).1 = true) (hle : term ≤ (c.state a).1.term) :
    pfx <+: (c.state a).1.log := by
  rcases h with rfl | ⟨chosenTerm, chosen, hct, hchosen, hpc⟩
  · exact List.nil_prefix
  refine hpc.trans ?_
  rcases Nat.eq_or_lt_of_le (Nat.le_trans hct hle) with heq | hlt
  · obtain ⟨l, hled, hpl⟩ := hchosen.2.2.1
    exact hpl.trans (hr.logs.led_prefix hr.votes hleader (heq ▸ hled))
  · exact hk.leaders chosenTerm chosen hchosen.choosable a _ (c.mem_seen_self a) hleader hlt

end Theorems

section Headlines

variable (config) (machine : Machine C R M) (hup : config.votesForUpToDateOnly = true)
  (hown : config.commitsOwnTermOnly = true) (env : EnvModel (sig N C R))

include hup hown

/-- Leader completeness: what a majority held in a term, which is what it is to be committed in
that term, is in the log of every leader of a later term, at every time. -/
theorem leader_completeness :
    (recording N config machine).Invariant env fun c =>
      ∀ term pfx, Chosen c term pfx → ∀ a, ∀ p ∈ c.seen a, isLeader p = true → term < p.term →
        pfx <+: p.log :=
  fun c hc term pfx hchosen =>
    ((committing_monotone hup hown).invariant env c hc).safe.leaders term pfx hchosen.choosable

/-- What a node has committed, a majority held in some term up to the node's. -/
theorem committed_chosen :
    (recording N config machine).Invariant env fun c =>
      ∀ a, Committed c (c.state a).1.term ((c.state a).1.log.take (c.state a).1.commit) :=
  fun c hc a => (((committing_monotone hup hown).invariant env c hc).commits.nodes a).2

theorem commit_le_length :
    (cluster N config machine).Invariant env fun c =>
      ∀ a, (c.state a).commit ≤ (c.state a).log.length :=
  .of_ghost (.past _) fun c hc a =>
    (((committing_monotone hup hown).invariant env c hc).commits.nodes a).1

theorem committed_agree :
    (cluster N config machine).Invariant env fun c => ∀ a b,
      (c.state a).log.take (min (c.state a).commit (c.state b).commit) =
        (c.state b).log.take (min (c.state a).commit (c.state b).commit) := by
  refine .of_ghost (.past _) fun c hc a b => ?_
  obtain ⟨hr, _, hk, hcommits⟩ := (committing_monotone hup hown).invariant env c hc
  obtain ⟨hlenA, hA⟩ := hcommits.nodes a
  obtain ⟨hlenB, hB⟩ := hcommits.nodes b
  show (c.state a).1.log.take (min (c.state a).1.commit (c.state b).1.commit) =
    (c.state b).1.log.take (min (c.state a).1.commit (c.state b).1.commit)
  rcases hA.comparable hr hk hB with h | h
  · obtain ⟨_, htake⟩ := take_eq_of_take_prefix hlenA (h.trans (List.take_prefix _ _))
    have := congrArg (List.take (min (c.state a).1.commit (c.state b).1.commit)) htake
    simpa [List.take_take, Nat.min_assoc] using this.symm
  · obtain ⟨_, htake⟩ := take_eq_of_take_prefix hlenB (h.trans (List.take_prefix _ _))
    have := congrArg (List.take (min (c.state a).1.commit (c.state b).1.commit)) htake
    simpa [List.take_take, Nat.min_comm, Nat.min_assoc] using this

theorem leader_complete :
    (cluster N config machine).Invariant env fun c => ∀ l a, isLeader (c.state l) = true →
      (c.state a).term ≤ (c.state l).term →
        (c.state l).log.take (c.state a).commit = (c.state a).log.take (c.state a).commit := by
  refine .of_ghost (.past _) fun c hc l a hleader hle => ?_
  obtain ⟨hr, _, hk, hcommits⟩ := (committing_monotone hup hown).invariant env c hc
  obtain ⟨hlen, hcommitted⟩ := hcommits.nodes a
  exact (take_eq_of_take_prefix hlen (hcommitted.in_leader hr hk hleader hle)).2

theorem commitWithinLog_invariant :
    (cluster N config machine).Invariant env fun c => commitWithinLog c = true := by
  intro c hc
  simpa [commitWithinLog] using fun a _ => commit_le_length config machine hup hown env c hc a

theorem committedAgree_invariant :
    (cluster N config machine).Invariant env fun c => committedAgree c = true := by
  intro c hc
  simpa [committedAgree, pairs] using
    fun a _ b _ => committed_agree config machine hup hown env c hc a b

theorem leaderComplete_invariant :
    (cluster N config machine).Invariant env fun c => leaderComplete c = true := by
  intro c hc
  have hcomplete := leader_complete config machine hup hown env c hc
  simp only [leaderComplete, pairs, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, beq_iff_eq]
  intro l _ a _
  by_cases hleader : isLeader (c.state l) = true
  · by_cases hle : (c.state a).term ≤ (c.state l).term
    · exact .inr (hcomplete l a hleader hle)
    · exact .inl (.inr (by omega))
  · exact .inl (.inl (by simpa using hleader))

end Headlines

end RaftKV
