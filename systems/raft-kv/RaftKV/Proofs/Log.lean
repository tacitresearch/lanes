/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Election

/-!
# The first invariants of the log

For every finite set of nodes, every machine, every `Config` and every environment model:

- a node has applied no more than it has committed (`applied_le_commit`);
- no entry is of a later term than the node that holds it (`entry_term_le`);
- no `append` carries more than a batch (`append_bounded`);
- a leader's log only grows while it leads its term (`leader_append_only`);
- two logs that agree on the term of an entry agree on everything up to it (`log_matching`).

Log matching is about the past. An `append` in flight carries part of the log its leader had
when it was sent, and that leader may since have lost its role and had its log replaced. So the
proof reads the histories of `Proofs/Election.lean`. The invariant (`Logs`) says that the logs a
node had as leader of one term extend one another, that every entry of every log a node has had
came, with all before it, from the log of a leader of the entry's term, and that every `append`
in flight carries a batch cut from such a log. Two logs with an entry of one term at one place
then both got it from the one leader of that term. A follower that takes an `append` ends with
its own log or with the leader's as far as the batch goes (`Within`), so nothing new has to be
shown of the result.

Not here: `commit ≤ log.length`. A follower's log gets shorter when a leader's entries replace
its own, and that this never reaches a committed entry is leader completeness
(`Proofs/Commit.lean`). It is false with `votesForUpToDateOnly` off.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

theorem applied_le_commit (config : Config) (machine : Machine C R M)
    (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c =>
      ∀ a, (c.state a).applied ≤ (c.state a).commit := by
  intro c hc a
  refine System.invariant_of_actor (cluster N config machine) a
    (P := fun s => s.applied ≤ s.commit) (Actor.Inductive.invariant ?_) env c hc
  exact ⟨Nat.le_refl 0, fun s msg h => (step_moves config Enum.all machine a s msg).applied_le h,
    fun s h => (recover_moves config Enum.all machine a s).applied_le h⟩

section Terms

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem mem_merge {own sent : List (Entry N C)} {entry : Entry N C}
    (h : entry ∈ merge own sent) : entry ∈ own ∨ entry ∈ sent := by
  fun_induction merge own sent <;> grind

/-- No entry, in a log or in flight, is of a later term than the node or the message that holds
it. -/
structure Terms (c : SysState (recording N config machine)) : Prop where
  logs : ∀ a, ∀ entry ∈ (c.state a).1.log, entry.term ≤ (c.state a).1.term
  appends : ∀ src dst term leader prev prevTerm entries commit,
    (⟨src, dst, .append term leader prev prevTerm entries commit⟩ : Envelope (sig N C R)) ∈ c.net →
      ∀ entry ∈ entries, entry.term ≤ term

namespace Terms

variable {c : SysState (recording N config machine)}

theorem blank : Terms (SysState.blank (recording N config machine)) := by
  constructor <;> simp [SysState.blank, recording, System.withPast, System.withGhost, node]

theorem grow (hc : Terms c) {i : N} {msg : Option (Msg N C)} {s' : Node N C M}
    {effs : List (Effect (sig N C R) i)}
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (happend : ∀ term leader prev prevTerm entries commit,
      msg = some (.append term leader prev prevTerm entries commit) →
        ∀ entry ∈ entries, entry.term ≤ term) :
    Terms (c.grow i ((s', c.seen i), effs)) := by
  have hold : ∀ entry ∈ (c.state i).1.log, entry.term ≤ s'.term := fun entry h =>
    Nat.le_trans (hc.logs i entry h) hmoves.term_le
  have hlogs : ∀ entry ∈ s'.log, entry.term ≤ s'.term := by
    intro entry hentry
    rcases hmoves.log with h | ⟨_, added, hadded, h⟩ |
      ⟨_, leader, prev, entries, commit, hmsg, _, h⟩
    · exact hold entry (h ▸ hentry)
    · rcases List.mem_append.mp (h ▸ hentry) with hentry | hentry
      · exact hold entry hentry
      · exact Nat.le_of_eq (List.mem_singleton.mp hentry ▸ hadded)
    · rcases List.mem_append.mp (h ▸ hentry) with hentry | hentry
      · exact hold entry (List.mem_of_mem_take hentry)
      · rcases mem_merge hentry with hentry | hentry
        · exact hold entry (List.mem_of_mem_drop hentry)
        · exact happend _ leader prev _ entries commit hmsg entry hentry
  refine ⟨fun a => ?_, fun src dst term leader prev prevTerm entries commit hmem => ?_⟩
  · by_cases ha : a = i
    · subst ha
      simpa using hlogs
    · simpa [ha] using hc.logs a
  · rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact hc.appends src dst term leader prev prevTerm entries commit hold
    · obtain ⟨_, rfl, _, _, hbatch, _⟩ := hmoves.sent _ hnew
      exact fun entry hentry => hlogs entry (List.mem_of_mem_drop (hbatch.mem hentry))

end Terms

theorem terms_monotone :
    (recording N config machine).Monotone fun c => (Timers c ∧ Votes c) ∧ Terms c := by
  refine votes_monotone.and_net .blank (fun _ _ _ _ _ hc hnet => ⟨hc.logs,
    fun src dst term leader prev prevTerm entries commit h => hc.appends src dst term leader prev
      prevTerm entries commit (mem_of_not_propose hnet h nofun)⟩) ?_ ?_
  · intro c i msg hp _ hc hpending
    refine hc.grow (step_moves config Enum.all machine i _ msg) ?_
    intro term leader prev prevTerm entries commit hmsg
    obtain rfl := Option.some.inj hmsg
    rcases hpending with ⟨src, hnet⟩ | htimer
    · exact hc.appends src i term leader prev prevTerm entries commit hnet
    · exact nomatch hp.1 i _ htimer
  · exact fun c i _ _ hc => hc.grow (recover_moves config Enum.all machine i _) nofun

theorem entry_term_le (config : Config) (machine : Machine C R M) (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c =>
      ∀ a, ∀ entry ∈ (c.state a).log, entry.term ≤ (c.state a).term :=
  .of_ghost (.past _) fun c hc => (terms_monotone.invariant env c hc).2.logs

end Terms

section Batches

/-- An `append` in flight carries no more than a batch. -/
def Bounded (c : SysState (recording N config machine)) : Prop :=
  ∀ src dst term leader prev prevTerm entries commit,
    (⟨src, dst, .append term leader prev prevTerm entries commit⟩ : Envelope (sig N C R)) ∈ c.net →
      entries.length ≤ max 1 config.maxAppend

theorem bounded_monotone :
    (recording N config machine).Monotone fun c => Timers c ∧ Bounded c := by
  refine timers_monotone.and_net (fun _ _ _ _ _ _ _ _ h => nomatch h)
    (fun _ _ _ _ _ hc hnet src dst term leader prev prevTerm entries commit h =>
      hc src dst term leader prev prevTerm entries commit (mem_of_not_propose hnet h nofun)) ?_ ?_
  · intro c i msg _ _ hc _ src dst term leader prev prevTerm entries commit hmem
    rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact hc src dst term leader prev prevTerm entries commit hold
    · exact (step_moves config Enum.all machine i (c.state i).1 msg).batch _ _ _ _ _ _ _ hnew
  · intro c i _ _ hc src dst term leader prev prevTerm entries commit hmem
    rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact hc src dst term leader prev prevTerm entries commit hold
    · exact (recover_moves config Enum.all machine i (c.state i).1).batch _ _ _ _ _ _ _ hnew

/-- No `append` carries more than `maxAppend` entries, or more than one where that is zero. -/
theorem append_bounded (config : Config) (machine : Machine C R M) (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c =>
      ∀ src dst term leader prev prevTerm entries commit,
        (⟨src, dst, .append term leader prev prevTerm entries commit⟩ : Envelope (sig N C R))
          ∈ c.net → entries.length ≤ max 1 config.maxAppend :=
  .of_ghost (.past _) fun c hc => (bounded_monotone.invariant env c hc).2

theorem appendsBounded_invariant (config : Config) (machine : Machine C R M)
    (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c => appendsBounded c = true := by
  intro c hc
  simp only [appendsBounded, List.all_eq_true]
  rintro ⟨src, dst, msg⟩ hmem
  cases msg <;> first
    | rfl
    | simpa using append_bounded config machine env c hc _ _ _ _ _ _ _ _ hmem

end Batches

section Leader

variable {nodes : List N} {i : N} {s s' : Node N C M} {msg : Option (Msg N C)}
  {effs : List (Effect (sig N C R) i)}

omit [Enum N] in
theorem Moves.follower_stays (h : Moves config nodes i s msg s' effs) (hterm : s'.term = s.term)
    (hrole : s.role = .follower) : s'.role = .follower := by
  cases hrole' : s'.role with
  | follower => rfl
  | candidate votes =>
    rcases h.candidate votes hrole' with ⟨h, _⟩ | ⟨_, _, votes₀, h, _⟩
    · omega
    · simp [hrole] at h
  | leader matched =>
    rcases h.leader (isLeader_iff.mpr ⟨matched, hrole'⟩) with
      ⟨h, _⟩ | ⟨_, _, votes₀, _, h, _⟩ | ⟨_, h, _⟩
    · omega
    · simp [hrole] at h
    · simp [isLeader, hrole] at h

omit [Enum N] in
theorem Moves.leader_grows (h : Moves config nodes i s msg s' effs) (hterm : s'.term = s.term)
    (hrole : isLeader s = true) :
    s'.role = .follower ∨ (isLeader s' = true ∧ s.log <+: s'.log) := by
  cases hrole' : s'.role with
  | follower => exact .inl rfl
  | candidate votes =>
    rcases h.candidate votes hrole' with ⟨h, _⟩ | ⟨_, _, votes₀, h, _⟩
    · omega
    · simp [isLeader, h] at hrole
  | leader matched =>
    have hleader := isLeader_iff.mpr ⟨matched, hrole'⟩
    rcases h.leader hleader with ⟨h, _⟩ | ⟨_, _, votes₀, _, h, _⟩ | ⟨_, _, h⟩
    · omega
    · simp [isLeader, h] at hrole
    · exact .inr ⟨hleader, h⟩

omit [Enum N] in
/-- A leader's log only grows while it leads its term. -/
theorem leader_append_only (config : Config) (nodes : List N) (machine : Machine C R M)
    (self : N) (s : Node N C M) (msg : Msg N C) (hleader : isLeader s = true)
    (hleader' : isLeader ((node config nodes machine self).step s msg).1 = true)
    (hterm : ((node config nodes machine self).step s msg).1.term = s.term) :
    s.log <+: ((node config nodes machine self).step s msg).1.log := by
  rcases (step_moves config nodes machine self s msg).leader_grows hterm hleader with h | h
  · simp [isLeader, h] at hleader'
  · exact h.2

/-- The same of the cluster: whatever happens, under any environment model, a node that leads a
term before and after has kept every entry it had. -/
theorem leader_log_grows (config : Config) (machine : Machine C R M)
    {env : EnvModel (sig N C R)} {c c' : SysState (cluster N config machine)}
    {ev : Event (sig N C R)} (hstep : c.step env ev = some c') (a : N)
    (hleader : isLeader (c.state a) = true) (hleader' : isLeader (c'.state a) = true)
    (hterm : (c'.state a).term = (c.state a).term) : (c.state a).log <+: (c'.state a).log := by
  rcases SysState.step_state hstep with h | ⟨k, msg, h⟩ | ⟨k, h⟩ <;> rw [h] at hleader' hterm ⊢
  · exact List.prefix_refl _
  · by_cases ha : a = k
    · subst ha
      rw [update_self] at hleader' hterm ⊢
      exact leader_append_only config Enum.all machine a _ msg hleader hleader' hterm
    · rw [update_of_ne _ _ ha]
      exact List.prefix_refl _
  · by_cases ha : a = k
    · subst ha
      simp [isLeader, node] at hleader'
    · rw [update_of_ne _ _ ha]
      exact List.prefix_refl _

end Leader

section Matching

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]

theorem termAt_cons_succ (entry : Entry N C) (log : List (Entry N C)) {k : Nat} (hk : 0 < k) :
    termAt (entry :: log) (k + 1) = termAt log k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp [termAt]

theorem termAt_drop (log : List (Entry N C)) (prev : Nat) {k : Nat} (hk : 0 < k) :
    termAt (log.drop prev) k = termAt log (prev + k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp [termAt]

theorem termAt_append_left (a b : List (Entry N C)) {k : Nat} (hk : k ≤ a.length) :
    termAt (a ++ b) k = termAt a k := by
  unfold termAt
  split
  · rfl
  · rw [List.getElem?_append_left (by omega)]

theorem termAt_append_length (log : List (Entry N C)) (entry : Entry N C) :
    termAt (log ++ [entry]) (log.length + 1) = entry.term := by
  simp [termAt]

theorem termAt_of_prefix {a b : List (Entry N C)} (h : a <+: b) {k : Nat} (hk : k ≤ a.length) :
    termAt a k = termAt b k := by
  obtain ⟨rest, rfl⟩ := h
  exact (termAt_append_left a rest hk).symm

/-- A batch cut from `l` after `prev` is what follows `prev` in a start of `l`. -/
theorem exists_cut {l batch : List (Entry N C)} {prev : Nat} (hprev : prev ≤ l.length)
    (h : batch <+: l.drop prev) :
    ∃ cut, cut <+: l ∧ cut.length = prev + batch.length ∧ termAt cut prev = termAt l prev ∧
      cut.drop prev = batch := by
  have hlen := h.length_le
  rw [List.length_drop] at hlen
  have hcut : (l.take (prev + batch.length)).length = prev + batch.length := by
    rw [List.length_take]
    omega
  exact ⟨_, List.take_prefix _ _, hcut, termAt_of_prefix (List.take_prefix _ _) (by omega),
    drop_take_of_prefix h⟩

/-- Two logs that agree on the term of an entry agree on everything up to it. -/
def Matching (a b : List (Entry N C)) : Prop :=
  ∀ k, k ≤ a.length → k ≤ b.length → termAt a k = termAt b k → a.take k = b.take k

theorem Matching.tail {e e' : Entry N C} {a b : List (Entry N C)}
    (h : Matching (e :: a) (e' :: b)) : Matching a b := by
  intro k hka hkb hterm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have := h (k + 1) (by simpa using hka) (by simpa using hkb)
      (by rwa [termAt_cons_succ _ _ hk, termAt_cons_succ _ _ hk])
    simp only [List.take_succ_cons, List.cons.injEq] at this
    exact this.2

theorem Matching.drop {a b : List (Entry N C)} (h : Matching a b) (prev : Nat) :
    Matching (a.drop prev) (b.drop prev) := by
  intro k hka hkb hterm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp only [List.length_drop] at hka hkb
    rw [termAt_drop _ _ hk, termAt_drop _ _ hk] at hterm
    have := congrArg (List.drop prev) (h (prev + k) (by omega) (by omega) hterm)
    simpa [List.drop_take] using this

theorem merge_eq_of_matching {own sent : List (Entry N C)} (h : Matching own sent) :
    (merge own sent = own ∧ sent <+: own) ∨ merge own sent = sent := by
  fun_induction merge own sent with
  | case1 e own n sent hterm ih =>
    have := h 1 (by simp) (by simp) (by simpa [termAt] using hterm)
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at this
    subst this
    exact (ih h.tail).imp
      (fun h => ⟨congrArg _ h.1, List.cons_prefix_cons.mpr ⟨rfl, h.2⟩⟩) (congrArg _)
  | case2 e own n sent hterm => exact .inr rfl
  | case3 sent => exact .inr rfl
  | case4 own => exact .inl ⟨rfl, List.nil_prefix⟩

theorem merge_of_prefix {own sent : List (Entry N C)} (h : sent <+: own) :
    merge own sent = own := by
  fun_induction merge own sent with
  | case1 e own n sent hterm ih => rw [ih (List.cons_prefix_cons.mp h).2]
  | case2 e own n sent hterm => exact absurd (by rw [(List.cons_prefix_cons.mp h).1]) hterm
  | case3 sent => exact List.prefix_nil.mp h
  | case4 own => rfl

/-- What a follower has after taking an `append` cut from `theirs`: its own log if that holds
all of theirs, and theirs if not. -/
theorem take_append_merge {own theirs : List (Entry N C)} (h : Matching own theirs) {prev : Nat}
    (hown : prev ≤ own.length) (htheirs : prev ≤ theirs.length)
    (hterm : termAt own prev = termAt theirs prev) :
    (theirs <+: own ∧ own.take prev ++ merge (own.drop prev) (theirs.drop prev) = own) ∨
      (¬theirs <+: own ∧ own.take prev ++ merge (own.drop prev) (theirs.drop prev) = theirs) := by
  have htake := h prev hown htheirs hterm
  by_cases hprefix : theirs <+: own
  · refine .inl ⟨hprefix, ?_⟩
    obtain ⟨rest, rfl⟩ := hprefix
    rw [merge_of_prefix ⟨rest, (List.drop_append_of_le_length htheirs).symm⟩]
    exact List.take_append_drop prev _
  · refine .inr ⟨hprefix, ?_⟩
    rcases merge_eq_of_matching (h.drop prev) with ⟨_, rest, hrest⟩ | hmerge
    · refine absurd ⟨rest, ?_⟩ hprefix
      rw [← List.take_append_drop prev theirs, List.append_assoc, hrest, ← htake,
        List.take_append_drop]
    · rw [hmerge, htake]
      exact List.take_append_drop prev theirs

end Matching

/-- `log` was the log of a leader of `term`, at some time. -/
def Led (c : SysState (recording N config machine)) (term : Nat) (log : List (Entry N C)) : Prop :=
  ∃ a, ∃ p ∈ c.seen a, isLeader p = true ∧ p.term = term ∧ p.log = log

/-- `log` is a start of a log a leader of `term` had: what a follower has of that leader when
it has taken one batch. -/
def Within (c : SysState (recording N config machine)) (term : Nat) (log : List (Entry N C)) :
    Prop :=
  ∃ l, Led c term l ∧ log <+: l

/-- Every entry of `log` was, with all before it, in the log of a leader of the entry's term. -/
def Sourced (c : SysState (recording N config machine)) (log : List (Entry N C)) : Prop :=
  ∀ k, 0 < k → k ≤ log.length → ∃ l, Led c (termAt log k) l ∧ l.take k = log.take k

theorem Sourced.of_prefix {c : SysState (recording N config machine)} {log l : List (Entry N C)}
    (h : Sourced c l) (hp : log <+: l) : Sourced c log := by
  intro k hk hlen
  obtain ⟨l', hled, htake⟩ := h k hk (Nat.le_trans hlen hp.length_le)
  exact ⟨l', termAt_of_prefix hp hlen ▸ hled, htake.trans (take_of_prefix hp hlen)⟩

/--
The inductive invariant, given `Votes`. Like `Votes` it reads what nodes have been and what is
in flight, so no loss, duplication or crash can break it.
-/
structure Logs (c : SysState (recording N config machine)) : Prop where
  /-- A node that led its present term still leads it, with a log that has only grown, or has
  stepped down for good. -/
  grows : ∀ a, ∀ p ∈ c.seen a, isLeader p = true → p.term ≤ (c.state a).1.term ∧
    (p.term = (c.state a).1.term → (c.state a).1.role = .follower ∨
      (isLeader (c.state a).1 = true ∧ p.log <+: (c.state a).1.log))
  chain : ∀ a, ∀ p ∈ c.seen a, ∀ q ∈ c.seen a, isLeader p = true → isLeader q = true →
    p.term = q.term → p.log <+: q.log ∨ q.log <+: p.log
  sourced : ∀ a, ∀ p ∈ c.seen a, Sourced c p.log
  sorted : ∀ a, ∀ p ∈ c.seen a, p.log.Pairwise (·.term ≤ ·.term)
  appends : ∀ src dst term leader prev prevTerm entries commit,
    (⟨src, dst, .append term leader prev prevTerm entries commit⟩ : Envelope (sig N C R)) ∈ c.net →
      ∃ l, Led c term l ∧ prev ≤ l.length ∧ prevTerm = termAt l prev ∧ entries <+: l.drop prev

section Grow

variable {c : SysState (recording N config machine)} {i : N} {s' : Node N C M}
  {effs : List (Effect (sig N C R) i)}

theorem Led.grow {term : Nat} {log : List (Entry N C)} (h : Led c term log) :
    Led (c.grow i ((s', c.seen i), effs)) term log :=
  h.elim fun a ⟨p, hp, h⟩ => ⟨a, p, mem_seen_grow.mpr (.inl hp), h⟩

theorem Within.grow {term : Nat} {log : List (Entry N C)} (h : Within c term log) :
    Within (c.grow i ((s', c.seen i), effs)) term log :=
  h.imp fun _ hl => ⟨hl.1.grow, hl.2⟩

theorem Sourced.grow {log : List (Entry N C)} (h : Sourced c log) :
    Sourced (c.grow i ((s', c.seen i), effs)) log :=
  fun k hk hlen => (h k hk hlen).elim fun l hl => ⟨l, hl.1.grow, hl.2⟩

end Grow

namespace Logs

variable {c : SysState (recording N config machine)}

/-- The logs of the leader of a term extend one another. -/
theorem led_chain (hv : Votes c) (hc : Logs c) {term : Nat} {l₁ l₂ : List (Entry N C)}
    (h₁ : Led c term l₁) (h₂ : Led c term l₂) : l₁ <+: l₂ ∨ l₂ <+: l₁ := by
  obtain ⟨a, p, hp, hpleader, hpterm, rfl⟩ := h₁
  obtain ⟨b, q, hq, hqleader, hqterm, rfl⟩ := h₂
  obtain rfl := hv.leader_unique hp hq hpleader hqleader (hpterm.trans hqterm.symm)
  exact hc.chain a p hp q hq hpleader hqleader (hpterm.trans hqterm.symm)

theorem matching (hv : Votes c) (hc : Logs c) {a b : List (Entry N C)} (ha : Sourced c a)
    (hb : Sourced c b) : Matching a b := by
  intro k hka hkb hterm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨la, hla, htakeA⟩ := ha k hk hka
    obtain ⟨lb, hlb, htakeB⟩ := hb k hk hkb
    have hlenA : k ≤ la.length := by
      have := congrArg List.length htakeA
      simp only [List.length_take] at this
      omega
    have hlenB : k ≤ lb.length := by
      have := congrArg List.length htakeB
      simp only [List.length_take] at this
      omega
    rw [← htakeA, ← htakeB]
    rcases hc.led_chain hv (hterm ▸ hla) hlb with ⟨rest, rfl⟩ | ⟨rest, rfl⟩
    · exact (List.take_append_of_le_length hlenA).symm
    · exact List.take_append_of_le_length hlenB

theorem blank : Logs (SysState.blank (recording N config machine)) := by
  constructor <;>
    simp [SysState.blank, recording, System.withPast, System.withGhost, node, SysState.seen,
      isLeader, Sourced]
  exact fun _ k hk hzero => absurd hzero (Nat.ne_of_gt hk)

theorem led_sourced (hc : Logs c) {term : Nat} {l : List (Entry N C)} (h : Led c term l) :
    Sourced c l := by
  obtain ⟨a, p, hp, _, _, rfl⟩ := h
  exact hc.sourced a p hp

theorem within_sourced (hc : Logs c) {term : Nat} {l : List (Entry N C)} (h : Within c term l) :
    Sourced c l :=
  h.elim fun _ hl => (hc.led_sourced hl.1).of_prefix hl.2

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- An `append` that is being handled carries all that follows `prev` in a start of the log of
a leader of its term. -/
def Cut (c : SysState (recording N config machine)) (msg : Option (Msg N C)) : Prop :=
  ∀ term leader prev prevTerm entries commit,
    msg = some (.append term leader prev prevTerm entries commit) →
      ∃ cut, Within c term cut ∧ prev ≤ cut.length ∧ prevTerm = termAt cut prev ∧
        entries = cut.drop prev

theorem cut_none : Cut c (none : Option (Msg N C)) :=
  nofun

theorem cut_of_pending (hc : Logs c) (h : Pending c i msg) : Cut c msg := by
  intro term leader prev prevTerm entries commit hmsg
  rcases h _ hmsg with ⟨src, hnet⟩ | h | h
  · obtain ⟨l, hled, hprev, rfl, hbatch⟩ :=
      hc.appends src i term leader prev prevTerm entries commit hnet
    obtain ⟨cut, hcut, hlen, hterm, rfl⟩ := exists_cut hprev hbatch
    exact ⟨cut, ⟨l, hled, hcut⟩, by omega, hterm.symm, rfl⟩
  · cases h
  · cases h

/-- What a follower has after taking a batch that ends a start `l` of the leader's log: its own
log if that holds all of `l`, and `l` if not. -/
theorem accepted (hv : Votes c) (hc : Logs c) {term prev : Nat} {l log' : List (Entry N C)}
    (hled : Within c term l) (hprev : prev ≤ (c.state i).1.log.length) (hlen : prev ≤ l.length)
    (hterm : termAt (c.state i).1.log prev = termAt l prev)
    (hlog : log' =
      (c.state i).1.log.take prev ++ merge ((c.state i).1.log.drop prev) (l.drop prev)) :
    (l <+: (c.state i).1.log ∧ log' = (c.state i).1.log) ∨
      (¬l <+: (c.state i).1.log ∧ log' = l) :=
  (take_append_merge (hc.matching hv (hc.sourced i _ (c.mem_seen_self i)) (hc.within_sourced hled))
    hprev hlen hterm).imp (fun h => ⟨h.1, hlog.trans h.2⟩) fun h => ⟨h.1, hlog.trans h.2⟩

/-- The log of a node that has moved: as it was, or a leader's with one more entry of its term,
or a start of the log a leader of its term had. -/
theorem moved (hv : Votes c) (hc : Logs c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcut : Cut c msg) :
    s'.log = (c.state i).1.log ∨
      (isLeader s' = true ∧ ∃ entry, entry.term = s'.term ∧
        s'.log = (c.state i).1.log ++ [entry]) ∨
      (s'.role = .follower ∧ Within c s'.term s'.log) := by
  rcases hmoves.log with h | h | ⟨hrole, leader, prev, entries, commit, hmsg, hprev, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨l, hled, hlen, hterm, rfl⟩ := hcut _ leader prev _ _ commit hmsg
    rcases hc.accepted hv hled hprev hlen hterm h with h | h
    · exact .inl h.2
    · exact .inr (.inr ⟨hrole, h.2 ▸ hled⟩)

theorem sourced_moved (hv : Votes c) (hc : Logs c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcut : Cut c msg) :
    Sourced (c.grow i ((s', c.seen i), effs)) s'.log := by
  have hown : Sourced c (c.state i).1.log := hc.sourced i _ (c.mem_seen_self i)
  rcases hc.moved hv hmoves hcut with h | ⟨hleader, entry, hentry, h⟩ | ⟨_, hwithin⟩
  · exact h ▸ hown.grow
  · intro k hk hlen
    rw [h, List.length_append, List.length_singleton] at hlen
    by_cases hold : k ≤ (c.state i).1.log.length
    · rw [h, termAt_append_left _ _ hold, List.take_append_of_le_length hold]
      exact hown.grow k hk hold
    · obtain rfl : k = (c.state i).1.log.length + 1 := by omega
      refine ⟨s'.log, ⟨i, s', mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩), hleader, ?_, rfl⟩, rfl⟩
      rw [h, termAt_append_length, hentry]
  · exact (hc.within_sourced hwithin).grow

theorem sorted_moved (hv : Votes c) (ht : Terms c) (hc : Logs c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcut : Cut c msg) :
    s'.log.Pairwise (·.term ≤ ·.term) := by
  have hown := hc.sorted i _ (c.mem_seen_self i)
  rcases hc.moved hv hmoves hcut with h | ⟨_, entry, hentry, h⟩ |
    ⟨_, l, ⟨a, p, hp, _, _, rfl⟩, hstart⟩
  · rwa [h]
  · rw [h, List.pairwise_append]
    refine ⟨hown, List.pairwise_singleton _ _, fun e he e' he' => ?_⟩
    obtain rfl := List.mem_singleton.mp he'
    have := ht.logs i e he
    have := hmoves.term_le
    omega
  · exact (hc.sorted a p hp).sublist hstart.sublist

/-- Where a node that has moved stands to each state in which it led. -/
theorem grows_moved (hc : Logs c) (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    {p : Node N C M} (hp : p ∈ c.seen i) (hleader : isLeader p = true) :
    p.term ≤ s'.term ∧ (p.term = s'.term →
      s'.role = .follower ∨ (isLeader s' = true ∧ p.log <+: s'.log)) := by
  obtain ⟨hle, hnow⟩ := hc.grows i p hp hleader
  have hterm := hmoves.term_le
  refine ⟨by omega, fun heq => ?_⟩
  rcases hnow (by omega) with hfollower | ⟨hleader₀, hprefix⟩
  · exact .inl (hmoves.follower_stays (by omega) hfollower)
  · exact (hmoves.leader_grows (by omega) hleader₀).imp_right fun h => ⟨h.1, hprefix.trans h.2⟩

theorem chain_moved (hc : Logs c) (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    {p : Node N C M} (hp : p ∈ c.seen i) (hleader : isLeader p = true)
    (hleader' : isLeader s' = true) (hterm : p.term = s'.term) : p.log <+: s'.log := by
  rcases (hc.grows_moved hmoves hp hleader).2 hterm with h | h
  · simp [isLeader, h] at hleader'
  · exact h.2

theorem grow (hv : Votes c) (ht : Terms c) (hc : Logs c)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs) (hcut : Cut c msg) :
    Logs (c.grow i ((s', c.seen i), effs)) := by
  refine ⟨fun a p hp hleader => ?_, fun a p hp q hq hpleader hqleader hterm => ?_,
    fun a p hp => ?_, fun a p hp => ?_,
    fun src dst term leader prev prevTerm entries commit hmem => ?_⟩
  · by_cases ha : a = i
    · subst ha
      rw [SysState.grow_state_self]
      rcases mem_seen_grow.mp hp with hp | ⟨_, rfl⟩
      · exact hc.grows_moved hmoves hp hleader
      · exact ⟨Nat.le_refl _, fun _ => .inr ⟨hleader, List.prefix_refl _⟩⟩
    · rw [SysState.grow_state_of_ne _ _ ha]
      exact hc.grows a p ((mem_seen_grow.mp hp).resolve_right (ha ·.1)) hleader
  · rcases mem_seen_grow.mp hp with hp' | ⟨rfl, rfl⟩
    · rcases mem_seen_grow.mp hq with hq' | ⟨rfl, rfl⟩
      · exact hc.chain a p hp' q hq' hpleader hqleader hterm
      · exact .inl (hc.chain_moved hmoves hp' hpleader hqleader hterm)
    · rcases mem_seen_grow.mp hq with hq' | ⟨_, rfl⟩
      · exact .inr (hc.chain_moved hmoves hq' hqleader hpleader hterm.symm)
      · exact .inl (List.prefix_refl _)
  · rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
    · exact (hc.sourced a p hp).grow
    · exact hc.sourced_moved hv hmoves hcut
  · rcases mem_seen_grow.mp hp with hp | ⟨rfl, rfl⟩
    · exact hc.sorted a p hp
    · exact hc.sorted_moved hv ht hmoves hcut
  · rcases SysState.mem_grow_net.mp hmem with hmem | ⟨_, hnew⟩
    · obtain ⟨l, hled, h⟩ := hc.appends src dst term leader prev prevTerm entries commit hmem
      exact ⟨l, hled.grow, h⟩
    · obtain ⟨hleader, rfl, h₁, h₂, h₃, _⟩ := hmoves.sent _ hnew
      exact ⟨s'.log, ⟨i, s', mem_seen_grow.mpr (.inr ⟨rfl, rfl⟩), hleader, rfl, rfl⟩, h₁, h₂, h₃⟩

end Logs

/-- `Timers`, `Votes`, `Terms` and `Logs`: what the proofs of commitment start from. -/
structure Replicating (c : SysState (recording N config machine)) : Prop where
  timers : Timers c
  votes : Votes c
  terms : Terms c
  logs : Logs c

theorem replicating_monotone : (recording N config machine).Monotone Replicating := by
  refine (terms_monotone.and_net .blank (fun _ _ _ _ _ hc hnet => ⟨hc.grows, hc.chain,
    hc.sourced, hc.sorted, fun src dst term leader prev prevTerm entries commit h =>
      hc.appends src dst term leader prev prevTerm entries commit
        (mem_of_not_propose hnet h nofun)⟩) ?_ ?_).of_iff fun c =>
    ⟨fun h => ⟨⟨⟨h.timers, h.votes⟩, h.terms⟩, h.logs⟩, fun ⟨⟨⟨ht, hv⟩, hterms⟩, hl⟩ =>
      ⟨ht, hv, hterms, hl⟩⟩
  · exact fun c i msg hp _ hc hpending => hc.grow hp.1.2 hp.2
      (step_moves config Enum.all machine i _ msg) (hc.cut_of_pending (hp.1.1.pending hpending))
  · exact fun c i hp _ hc => hc.grow hp.1.2 hp.2 (recover_moves config Enum.all machine i _)
      Logs.cut_none

theorem log_matching (config : Config) (machine : Machine C R M) (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c =>
      ∀ a b, Matching (c.state a).log (c.state b).log := by
  refine .of_ghost (.past _) fun c hc a b => ?_
  have hr := replicating_monotone.invariant env c hc
  exact hr.logs.matching hr.votes (hr.logs.sourced a _ (c.mem_seen_self a))
    (hr.logs.sourced b _ (c.mem_seen_self b))

theorem logMatching_invariant (config : Config) (machine : Machine C R M)
    (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c => logMatching c = true := by
  intro c hc
  have hmatching := log_matching config machine env c hc
  simp only [logMatching, pairs, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    beq_iff_eq]
  intro a _ b _ k hk
  by_cases hterm : termAt (c.state a).log (k + 1) = termAt (c.state b).log (k + 1)
  · exact .inr (hmatching a b (k + 1) (by omega) (by omega) hterm)
  · exact .inl hterm

theorem appliedWithinCommit_invariant (config : Config) (machine : Machine C R M)
    (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c => appliedWithinCommit c = true := by
  intro c hc
  simpa [appliedWithinCommit] using fun a _ => applied_le_commit config machine env c hc a

theorem entryTermsWithinTerm_invariant (config : Config) (machine : Machine C R M)
    (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env fun c => entryTermsWithinTerm c = true := by
  intro c hc
  simpa [entryTermsWithinTerm] using fun a _ => entry_term_le config machine env c hc a

end RaftKV
