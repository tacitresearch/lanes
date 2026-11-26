/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Election

/-!
# At most one leader per term, for every cluster and every fault

`Tests/Election.lean` checks election safety on three nodes and two terms. Here it is proved for
any finite set of nodes, any number of terms and any environment model: links may lose,
duplicate and reorder messages, and nodes may crash and restart at any time.

A node forgets its vote when its term moves on, so the proof gives each node a history: every
`(term, votedFor)` pair it has held (`history`). The invariant (`Voted`) says a history names
one candidate per term, and that every vote in flight, every vote a candidate has counted and a
majority behind every leader are in the voters' histories. Two leaders of one term then share a
voter, whose history names them both.

The proof is in layers (`System.Monotone`): first that only the election timeout is ever armed
(`Timers`), then `Voted` on top of it.
-/

namespace Examples.Election

open Lanes

variable {N : Type} [DecidableEq N]

def record (s : Node N) (hist : List (Nat × N)) : List (Nat × N) :=
  match s.votedFor with
  | some candidate => (s.term, candidate) :: hist
  | none => hist

omit [DecidableEq N] in
theorem mem_record {s : Node N} {hist : List (Nat × N)} {t : Nat} {candidate : N} :
    (t, candidate) ∈ record s hist ↔
      (t, candidate) ∈ hist ∨ (t = s.term ∧ s.votedFor = some candidate) := by
  unfold record
  split <;> simp_all [or_comm, eq_comm]

abbrev history [Enum N] (config : Config) : Ghost (cluster N config) where
  Hist _ := List (Nat × N)
  init _ := []
  step self hist s msg := record ((node config Enum.all self).step s msg).1 hist

abbrev recording (N : Type) [DecidableEq N] [Enum N] (config : Config) : System (sig N) :=
  (cluster N config).withGhost (history config)

/--
What one transition of a node and its history can do, as far as the invariant can tell.
`granted v` says the transition handled `v`'s vote for this node in the term it was in.
-/
structure Moves (nodes : List N) (i : N) (s : Node N) (hist : List (Nat × N))
    (granted : N → Prop) (s' : Node N) (hist' : List (Nat × N))
    (effs : List (Effect (sig N) i)) : Prop where
  term_le : s.term ≤ s'.term
  keeps : s'.term = s.term → ∀ candidate, s.votedFor = some candidate →
    s'.votedFor = some candidate
  hist_sub : ∀ p ∈ hist, p ∈ hist'
  hist_new : ∀ t candidate, (t, candidate) ∈ hist' →
    (t, candidate) ∈ hist ∨ (t = s'.term ∧ s'.votedFor = some candidate)
  sends : ∀ dst t voter, Effect.send (σ := sig N) dst (.vote t voter) ∈ effs →
    voter = i ∧ (t, dst) ∈ hist'
  armed : ∀ delay msg, Effect.after delay msg ∈ effs → msg = .electionTimeout
  candidate : ∀ counted, s'.role = .candidate counted →
    (counted = [i] ∧ (s'.term, i) ∈ hist') ∨
    (s'.term = s.term ∧ ∃ counted₀, s.role = .candidate counted₀ ∧
      ∀ v ∈ counted, v ∈ counted₀ ∨ granted v)
  leader : s'.role = .leader → s'.term = s.term ∧
    (s.role = .leader ∨ ∃ counted₀ counted, s.role = .candidate counted₀ ∧
      Quorum.isMajority nodes counted = true ∧ ∀ v ∈ counted, v ∈ counted₀ ∨ granted v)

theorem step_moves (config : Config) (honly : config.votesOncePerTerm = true) (nodes : List N)
    (self : N) (s : Node N) (hist : List (Nat × N)) (msg : Msg N) :
    Moves nodes self s hist (fun v => msg = .vote s.term v)
      ((node config nodes self).step s msg).1
      (record ((node config nodes self).step s msg).1 hist)
      ((node config nodes self).step s msg).2 := by
  obtain ⟨term, voted, role⟩ := s
  cases msg <;> cases role <;> simp only [node] <;> (repeat' split) <;> constructor <;>
    simp [mem_record] <;> grind

theorem recover_moves (config : Config) (nodes : List N) (self : N) (s : Node N)
    (hist : List (Nat × N)) :
    Moves nodes self s hist (fun _ => False) ((node config nodes self).recover s).1 hist
      ((node config nodes self).recover s).2 := by
  constructor <;> simp +contextual [node]

theorem Moves.refl (nodes : List N) (i : N) (s : Node N) (hist : List (Nat × N))
    (granted : N → Prop) : Moves nodes i s hist granted s hist [] := by
  constructor <;> simp +contextual

/-- A history names one candidate per term, and in the node's own term the one it votes for. -/
structure OneVote (s : Node N) (hist : List (Nat × N)) : Prop where
  bound : ∀ t candidate, (t, candidate) ∈ hist →
    t ≤ s.term ∧ (t = s.term → s.votedFor = some candidate)
  once : ∀ t a b, (t, a) ∈ hist → (t, b) ∈ hist → a = b

omit [DecidableEq N] in
theorem OneVote.nil (s : Node N) : OneVote s [] :=
  ⟨by simp, by simp⟩

theorem Moves.oneVote {nodes : List N} {i : N} {s s' : Node N} {hist hist' : List (Nat × N)}
    {granted : N → Prop} {effs : List (Effect (sig N) i)}
    (h : Moves nodes i s hist granted s' hist' effs) (hs : OneVote s hist) :
    OneVote s' hist' := by
  have hterm := h.term_le
  have hbound : ∀ t candidate, (t, candidate) ∈ hist' →
      t ≤ s'.term ∧ (t = s'.term → s'.votedFor = some candidate) := by
    intro t candidate hmem
    rcases h.hist_new t candidate hmem with hold | ⟨rfl, hvoted⟩
    · obtain ⟨hle, heq⟩ := hs.bound t candidate hold
      exact ⟨by omega, fun ht => h.keeps (by omega) candidate (heq (by omega))⟩
    · exact ⟨Nat.le_refl _, fun _ => hvoted⟩
  refine ⟨hbound, fun t a b ha hb => ?_⟩
  by_cases ht : t = s'.term
  · exact Option.some.inj (((hbound t a ha).2 ht).symm.trans ((hbound t b hb).2 ht))
  · exact hs.once t a b ((h.hist_new t a ha).resolve_right (ht ·.1))
      ((h.hist_new t b hb).resolve_right (ht ·.1))

variable [Enum N] {config : Config}

/-- Only the election timeout is ever armed, so a `vote` never arrives as a timer, where
`Voted.sent` says nothing about it. -/
def Timers (c : SysState (recording N config)) : Prop :=
  ∀ i msg, msg ∈ c.timers i → msg = .electionTimeout

theorem timers_monotone (honly : config.votesOncePerTerm = true) :
    (recording N config).Monotone Timers :=
  .timers _ (fun i s msg => (step_moves config honly Enum.all i s.1 s.2 msg).armed)
    fun i s => (recover_moves config Enum.all i s.1 s.2).armed

/--
The inductive invariant. Every clause reads histories, which only grow, and quantifies over
all messages in flight, so no loss, duplication or crash can break it.
-/
structure Voted (c : SysState (recording N config)) : Prop where
  oneVote : ∀ v, OneVote (c.state v).1 (c.state v).2
  sent : ∀ src dst t voter, (⟨src, dst, .vote t voter⟩ : Envelope (sig N)) ∈ c.net →
    (t, dst) ∈ (c.state voter).2
  counted : ∀ a counted, (c.state a).1.role = .candidate counted →
    ∀ v ∈ counted, ((c.state a).1.term, a) ∈ (c.state v).2
  elected : ∀ a, (c.state a).1.role = .leader →
    ∃ counted, Quorum.isMajority Enum.all counted = true ∧
      ∀ v ∈ counted, ((c.state a).1.term, a) ∈ (c.state v).2

namespace Voted

variable {c : SysState (recording N config)}

theorem blank : Voted (SysState.blank (recording N config)) := by
  constructor <;> simp [SysState.blank, recording, System.withGhost, node, OneVote.nil]

variable {i : N} {granted : N → Prop} {s' : Node N} {hist' : List (Nat × N)}
  {effs : List (Effect (sig N) i)}

/-- When one node moves, every node has moved from where it was: the others by staying. -/
theorem grow_moves (hmoves : Moves Enum.all i (c.state i).1 (c.state i).2 granted s' hist' effs)
    (a : N) :
    ∃ effs', Moves Enum.all a (c.state a).1 (c.state a).2 (fun v => a = i ∧ granted v)
      ((c.grow i ((s', hist'), effs)).state a).1 ((c.grow i ((s', hist'), effs)).state a).2
      effs' := by
  by_cases ha : a = i
  · subst ha; exact ⟨effs, by simpa using hmoves⟩
  · exact ⟨[], by simpa [ha] using Moves.refl ..⟩

theorem grow_hist (hmoves : Moves Enum.all i (c.state i).1 (c.state i).2 granted s' hist' effs)
    {v : N} {p : Nat × N} (hp : p ∈ (c.state v).2) :
    p ∈ ((c.grow i ((s', hist'), effs)).state v).2 :=
  (grow_moves hmoves v).elim fun _ hv => hv.hist_sub p hp

theorem grow (hc : Voted c)
    (hmoves : Moves Enum.all i (c.state i).1 (c.state i).2 granted s' hist' effs)
    (hgranted : ∀ v, granted v → ((c.state i).1.term, i) ∈ (c.state v).2) :
    Voted (c.grow i ((s', hist'), effs)) := by
  have hall := grow_moves hmoves
  have hbacked (a : N) (counted₀ counted : List N)
      (hrole : (c.state a).1.role = .candidate counted₀)
      (hfrom : ∀ v ∈ counted, v ∈ counted₀ ∨ (a = i ∧ granted v)) (v : N) (hv : v ∈ counted) :
      ((c.state a).1.term, a) ∈ ((c.grow i ((s', hist'), effs)).state v).2 := by
    rcases hfrom v hv with hold | ⟨rfl, hnew⟩
    · exact grow_hist hmoves (hc.counted a counted₀ hrole v hold)
    · exact grow_hist hmoves (hgranted v hnew)
  refine ⟨fun v => ?_, fun src dst t voter hmem => ?_, fun a counted hrole v hv => ?_,
    fun a hrole => ?_⟩
  · obtain ⟨_, hv⟩ := hall v
    exact hv.oneVote (hc.oneVote v)
  · rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact grow_hist hmoves (hc.sent src dst t voter hold)
    · obtain ⟨rfl, hin⟩ := hmoves.sends dst t voter hnew
      simpa using hin
  · obtain ⟨_, ha⟩ := hall a
    rcases ha.candidate counted hrole with ⟨rfl, hself⟩ | ⟨hterm, counted₀, hrole₀, hfrom⟩
    · obtain rfl := List.mem_singleton.mp hv
      exact hself
    · exact hterm ▸ hbacked a counted₀ counted hrole₀ hfrom v hv
  · obtain ⟨_, ha⟩ := hall a
    obtain ⟨hterm, hwas | ⟨counted₀, counted, hrole₀, hmajority, hfrom⟩⟩ := ha.leader hrole
    · obtain ⟨counted, hmajority, hvotes⟩ := hc.elected a hwas
      exact ⟨counted, hmajority, fun v hv => grow_hist hmoves (hterm ▸ hvotes v hv)⟩
    · exact ⟨counted, hmajority, fun v hv => hterm ▸ hbacked a counted₀ counted hrole₀ hfrom v hv⟩

end Voted

/-- `Voted` reads the nodes' states and asks something of each message in flight, and the
system takes no input, so `Monotone.and_net` leaves the two kinds of step to prove. -/
theorem voted_monotone (honly : config.votesOncePerTerm = true) :
    (recording N config).Monotone fun c => Timers c ∧ Voted c := by
  refine (timers_monotone honly).and_net .blank (fun _ _ _ _ _ hc hnet => ⟨hc.oneVote,
    fun src dst t voter h =>
      hc.sent src dst t voter ((hnet _ h).resolve_right fun ⟨x, _⟩ => nomatch x),
    hc.counted, hc.elected⟩) ?_ ?_
  · intro c i msg ht _ hc hpending
    refine hc.grow (step_moves config honly Enum.all i _ _ msg) ?_
    rintro v rfl
    rcases hpending with ⟨src, hnet⟩ | htimer
    · exact hc.sent src i _ v hnet
    · nomatch ht i _ htimer
  · exact fun c i _ _ hc => hc.grow (recover_moves config Enum.all i _ _) nofun

theorem election_safety (config : Config) (honly : config.votesOncePerTerm = true)
    (env : EnvModel (sig N)) :
    (cluster N config).Invariant env fun c =>
      ∀ a b, (c.state a).role = .leader → (c.state b).role = .leader →
        (c.state a).term = (c.state b).term → a = b := by
  refine .of_ghost (history config) fun c hc a b ha hb hterm => ?_
  have hvoted := ((voted_monotone honly).invariant env c hc).2
  obtain ⟨countedA, hmajorityA, hvotesA⟩ := hvoted.elected a ha
  obtain ⟨countedB, hmajorityB, hvotesB⟩ := hvoted.elected b hb
  obtain ⟨v, hvA, hvB⟩ := Quorum.majority_inter hmajorityA hmajorityB
  exact (hvoted.oneVote v).once _ a b (hvotesA v hvA) (hterm ▸ hvotesB v hvB)

theorem atMostOneLeaderPerTerm_invariant (config : Config)
    (honly : config.votesOncePerTerm = true) (env : EnvModel (sig N)) :
    (cluster N config).Invariant env fun c => atMostOneLeaderPerTerm c = true := by
  intro c hc
  have hsafe := election_safety config honly env c hc
  simp only [atMostOneLeaderPerTerm, List.all_eq_true]
  intro a _ b _
  have := hsafe a b
  grind

end Examples.Election
