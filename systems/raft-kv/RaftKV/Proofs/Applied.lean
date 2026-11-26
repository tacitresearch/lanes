/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV.Proofs.Commit
import RaftKV.Proofs.Serves

/-!
# One log, applied in order

With both switches of `Config` on, for every finite set of nodes, every machine and every
environment model: a node has applied exactly what it has committed (`applied_eq_commit`), its
machine is the replicated machine run over the entries it has applied (`machine_eq_run`), and of
two nodes one has applied a start of what the other has (`applied_agree`). This is state machine
safety, of one state; `applied_agree_over_time` and `applied_same_entry` are it of two points
of a run: no two nodes ever apply different entries at one index.

The invariant (`Logged`) names the list the cluster has committed to: a committed list that
every node's committed entries are a start of. Each machine is that list run up to where the node
has applied. The list only grows (`Logged.grow`), by what the node that moved has newly
committed, and this is where the proof that the cluster is the machine
(`RaftKVProofs/Refines.lean`) makes the commands take effect.
-/

namespace RaftKV

open Lanes

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

omit [Enum N] in
theorem Moves.commit_le {nodes : List N} {i : N} {s s' : Node N C M} {msg : Option (Msg N C)}
    {effs : List (Effect (sig N C R) i)} (h : Moves config nodes i s msg s' effs) :
    s.commit ≤ s'.commit := by
  rcases h.commit with h | h | ⟨_, _, _, _, _, _, _, h⟩ <;> omega

/-- `log` is what the cluster has committed to: it is committed, every node has committed a
start of it and applied exactly that, and each machine is the replicated one run that far. -/
structure Logged (c : SysState (recording N config machine)) (log : List (Entry N C)) : Prop where
  committed : ∃ term, Committed c term log
  upper : ∀ a, (c.state a).1.log.take (c.state a).1.commit <+: log
  applied : ∀ a, (c.state a).1.applied = (c.state a).1.commit
  machine : ∀ a,
    (c.state a).1.machine = machine.run machine.init (log.take (c.state a).1.applied)

namespace Logged

variable {c : SysState (recording N config machine)} {log : List (Entry N C)}

theorem blank : Logged (SysState.blank (recording N config machine)) [] := by
  constructor <;>
    simp [SysState.blank, recording, System.withPast, System.withGhost, node, Committed]

theorem of_state {c' : SysState (recording N config machine)} (h : Logged c log)
    (hstate : c'.state = c.state) : Logged c' log := by
  obtain ⟨hcommitted, hupper, happlied, hmachine⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Committed, Chosen, Within, Held, Led, SysState.seen, hstate]
  · exact hcommitted
  · exact hupper
  · exact happlied
  · exact hmachine

theorem applied_le (h : Logged c log) (hc : Commits c) (a : N) :
    (c.state a).1.applied ≤ log.length := by
  have := (h.upper a).length_le
  rw [List.length_take] at this
  have := (hc.nodes a).1
  have := h.applied a
  omega

/-- What a node has applied is what the cluster's log starts with. -/
theorem take_applied (h : Logged c log) (hc : Commits c) (a : N) :
    log.take (c.state a).1.applied = (c.state a).1.log.take (c.state a).1.applied := by
  have hlen : (c.state a).1.applied ≤ ((c.state a).1.log.take (c.state a).1.commit).length := by
    rw [List.length_take, h.applied a]
    exact Nat.le_min.mpr ⟨Nat.le_refl _, (hc.nodes a).1⟩
  rw [take_of_prefix (h.upper a) hlen, List.take_take, h.applied a, Nat.min_self]

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- A node that keeps its log, what it has committed and applied, and its machine, keeps the
cluster's log. A recovery is one. -/
theorem grow_same (h : Logged c log) (hlog : s'.log = (c.state i).1.log)
    (hcommit : s'.commit = (c.state i).1.commit) (happlied : s'.applied = (c.state i).1.applied)
    (hmachine : s'.machine = (c.state i).1.machine) :
    Logged (c.grow i ((s', c.seen i), effs)) log := by
  refine ⟨h.committed.imp fun _ hc => hc.grow, fun a => ?_, fun a => ?_, fun a => ?_⟩ <;>
    by_cases ha : a = i
  · subst ha
    simpa [hlog, hcommit] using h.upper a
  · simpa [ha] using h.upper a
  · subst ha
    simpa [happlied, hcommit] using h.applied a
  · simpa [ha] using h.applied a
  · subst ha
    simpa [happlied, hmachine] using h.machine a
  · simpa [ha] using h.machine a

theorem recover (h : Logged c log) :
    Logged (c.grow i (((recording N config machine).actor i).recover (c.state i))) log :=
  h.grow_same (s' := { (c.state i).1 with role := .follower }) rfl rfl rfl rfl

/-- The cluster's log after a node moves: as it was, or what that node has now committed, which
starts with what it was. -/
theorem grow (h : Logged c log) (hc : Commits c)
    (hr' : Replicating (c.grow i ((s', c.seen i), effs)))
    (hk' : Safe (c.grow i ((s', c.seen i), effs)))
    (hc' : Commits (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (hserves : Serves machine i (c.state i).1 msg s' effs) :
    ∃ log', log <+: log' ∧ Logged (c.grow i ((s', c.seen i), effs)) log' ∧
      s'.log.take s'.commit <+: log' ∧ (log' = log ∨ log' = s'.log.take s'.commit) := by
  obtain ⟨term, hcommitted⟩ := h.committed
  have hnode := hc'.nodes i
  simp only [SysState.grow_state_self] at hnode
  obtain ⟨hlen', hmine⟩ := hnode
  obtain ⟨log', hgrows, hupper, hcommitted', hwhich⟩ :
      ∃ log', log <+: log' ∧ s'.log.take s'.commit <+: log' ∧
        (∃ term, Committed (c.grow i ((s', c.seen i), effs)) term log') ∧
        (log' = log ∨ log' = s'.log.take s'.commit) := by
    rcases hmine.comparable hr' hk' (hcommitted.grow (i := i) (s' := s') (effs := effs)) with
      hp | hp
    · exact ⟨log, List.prefix_refl _, hp, ⟨term, hcommitted.grow⟩, .inl rfl⟩
    · exact ⟨_, hp, List.prefix_refl _, ⟨_, hmine⟩, .inr rfl⟩
  obtain ⟨hmachine, happlied, _⟩ := hserves.applies (Nat.le_of_eq (h.applied i).symm)
  have hcommit := hmoves.commit_le
  have hwas := h.applied i
  have happlied' : s'.applied = s'.commit := by
    rw [happlied, List.length_drop, List.length_take]
    omega
  refine ⟨log', hgrows, ⟨hcommitted', fun a => ?_, fun a => ?_, fun a => ?_⟩, hupper, hwhich⟩ <;>
    by_cases ha : a = i
  · subst ha
    simpa using hupper
  · simpa [ha] using (h.upper a).trans hgrows
  · subst ha
    simpa using happlied'
  · simpa [ha] using h.applied a
  · subst ha
    have hmine' : (s'.log.take s'.commit).length = s'.commit := by
      rw [List.length_take]
      omega
    have hall : log'.take s'.commit = s'.log.take s'.commit := by
      rw [take_of_prefix hupper (Nat.le_of_eq hmine'.symm), List.take_take, Nat.min_self]
    have hsome : log.take (c.state a).1.applied =
        (s'.log.take s'.commit).take (c.state a).1.applied := by
      rw [← take_of_prefix hgrows (h.applied_le hc a), take_of_prefix hupper (by omega)]
    simp only [SysState.grow_state_self]
    rw [hmachine, h.machine a, happlied', hall, hsome, ← Machine.run_append,
      List.take_append_drop]
  · simp only [SysState.grow_state_of_ne _ _ ha]
    rw [h.machine a, take_of_prefix hgrows (h.applied_le hc a)]

end Logged

/-- `Committing`, and a list the cluster has committed to. -/
def Applying (c : SysState (recording N config machine)) : Prop :=
  Committing c ∧ ∃ log, Logged c log

theorem applying_monotone (hup : config.votesForUpToDateOnly = true)
    (hown : config.commitsOwnTermOnly = true) :
    (recording N config machine).Monotone Applying := by
  refine (committing_monotone hup hown).and_state ⟨[], .blank⟩
    (fun _ _ _ _ _ ⟨log, h⟩ => ⟨log, h.of_state rfl⟩) ?_ ?_
  · intro c i msg hp hp' ⟨log, h⟩ _
    obtain ⟨log', _, h', _⟩ := h.grow hp.commits hp'.replicating hp'.safe hp'.commits
      (step_moves config Enum.all machine i _ msg) (step_serves config Enum.all machine i _ msg)
    exact ⟨log', h'⟩
  · exact fun c i _ _ ⟨log, h⟩ => ⟨log, h.recover⟩

/-- Every request in flight came from a client: no node sends one. -/
def FromClients (c : SysState (recording N config machine)) : Prop :=
  ∀ src dst req cmd, (⟨src, dst, .propose req cmd⟩ : Envelope (sig N C R)) ∈ c.net → src = none

theorem fromClients_monotone :
    (recording N config machine).Monotone fun c => Timers c ∧ FromClients c := by
  refine timers_monotone.and_net (fun _ _ _ _ h => nomatch h) ?_ ?_ ?_
  · intro c up net timers outbox h hnet src dst req cmd hmem
    rcases hnet _ hmem with hold | ⟨x, hx⟩
    · exact h src dst req cmd hold
    · simp only [Envelope.mk.injEq] at hx
      exact hx.1
  · intro c i msg _ _ h _ src dst req cmd hmem
    rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact h src dst req cmd hold
    · exact absurd hnew ((step_serves config Enum.all machine i (c.state i).1 msg).proposes _ _ _)
  · intro c i _ _ h src dst req cmd hmem
    rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact h src dst req cmd hold
    · exact absurd hnew ((recover_serves config Enum.all machine i (c.state i).1).proposes _ _ _)

section Requests

variable (config) (machine : Machine C R M) (env : EnvModel (sig N C R))

theorem requests_from_clients :
    (cluster N config machine).Invariant env fun c => ∀ src dst req cmd,
      (⟨src, dst, .propose req cmd⟩ : Envelope (sig N C R)) ∈ c.net → src = none :=
  .of_ghost (.past _) fun c hc => (fromClients_monotone.invariant env c hc).2

theorem requestsFromClients_invariant :
    (cluster N config machine).Invariant env fun c => requestsFromClients c = true := by
  intro c hc
  simp only [requestsFromClients, List.all_eq_true]
  rintro ⟨src, dst, msg⟩ hmem
  cases msg <;> first
    | rfl
    | simp [requests_from_clients config machine env c hc _ _ _ _ hmem]

end Requests

section Headlines

variable (config) (machine : Machine C R M) (hup : config.votesForUpToDateOnly = true)
  (hown : config.commitsOwnTermOnly = true) (env : EnvModel (sig N C R))

include hup hown

/-- A node has applied all it has committed. -/
theorem applied_eq_commit :
    (cluster N config machine).Invariant env fun c =>
      ∀ a, (c.state a).applied = (c.state a).commit :=
  .of_ghost (.past _) fun c hc a => by
    obtain ⟨_, log, h⟩ := (applying_monotone hup hown).invariant env c hc
    exact h.applied a

/-- A node's machine is the replicated machine run over the entries the node has applied. -/
theorem machine_eq_run :
    (cluster N config machine).Invariant env fun c => ∀ a,
      (c.state a).machine =
        machine.run machine.init ((c.state a).log.take (c.state a).applied) :=
  .of_ghost (.past _) fun c hc a => by
    obtain ⟨hcommitting, log, h⟩ := (applying_monotone hup hown).invariant env c hc
    exact (h.machine a).trans (congrArg _ (h.take_applied hcommitting.commits a))

/-- State machine safety: of two nodes, the one that has applied less has applied a start of
what the other has. -/
theorem applied_agree :
    (cluster N config machine).Invariant env fun c => ∀ a b,
      (c.state a).applied ≤ (c.state b).applied →
        (c.state a).log.take (c.state a).applied <+: (c.state b).log.take (c.state b).applied :=
  .of_ghost (.past _) fun c hc a b hle => by
    obtain ⟨hcommitting, log, h⟩ := (applying_monotone hup hown).invariant env c hc
    show (c.state a).1.log.take (c.state a).1.applied <+:
      (c.state b).1.log.take (c.state b).1.applied
    rw [← h.take_applied hcommitting.commits a, ← h.take_applied hcommitting.commits b]
    exact (List.take_prefix_take_left hle)

/-- State machine safety over time: what a node has applied at one point of a run and what a
node, the same or another, has applied at a later point are one a start of the other. -/
theorem applied_agree_over_time {c c' : SysState (cluster N config machine)}
    {events : List (Event (sig N C R))} (hc : (cluster N config machine).Reachable env c)
    (hrun : c.run env events = some c') (a b : N) :
    (c.state a).log.take (c.state a).applied <+: (c'.state b).log.take (c'.state b).applied ∨
      (c'.state b).log.take (c'.state b).applied <+: (c.state a).log.take (c.state a).applied := by
  obtain ⟨d, d', hreach, rfl, hrun', rfl⟩ := hc.exists_ghost_run (.past _) hrun
  obtain ⟨hcommitting, log, h⟩ := (applying_monotone hup hown).invariant env d hreach
  obtain ⟨hcommitting', log', h'⟩ :=
    (applying_monotone hup hown).invariant env d' (hreach.run hrun')
  have hthen := (hcommitting.commits.nodes a).2.of_seen (c' := d')
    fun _ _ hp => SysState.mem_seen_run hrun' hp
  show (d.state a).1.log.take (d.state a).1.applied <+:
      (d'.state b).1.log.take (d'.state b).1.applied ∨
    (d'.state b).1.log.take (d'.state b).1.applied <+:
      (d.state a).1.log.take (d.state a).1.applied
  rw [h.applied a, h'.applied b]
  exact hthen.comparable hcommitting'.replicating hcommitting'.safe (hcommitting'.commits.nodes b).2

/-- No two nodes ever apply different entries at one index: an entry a node has applied at one
point of a run is the entry any node has applied there at any later point. -/
theorem applied_same_entry {c c' : SysState (cluster N config machine)}
    {events : List (Event (sig N C R))} (hc : (cluster N config machine).Reachable env c)
    (hrun : c.run env events = some c') {a b : N} {k : Nat} (ha : k < (c.state a).applied)
    (hb : k < (c'.state b).applied) : (c.state a).log[k]? = (c'.state b).log[k]? := by
  have hlenA := commit_le_length config machine hup hown env c hc a
  have hlenB := commit_le_length config machine hup hown env c' (hc.run hrun) b
  rw [← applied_eq_commit config machine hup hown env c hc a] at hlenA
  rw [← applied_eq_commit config machine hup hown env c' (hc.run hrun) b] at hlenB
  have hA : ((c.state a).log.take (c.state a).applied)[k]? = some (c.state a).log[k] := by
    rw [List.getElem?_take_of_lt ha, List.getElem?_eq_getElem]
  have hB : ((c'.state b).log.take (c'.state b).applied)[k]? = some (c'.state b).log[k] := by
    rw [List.getElem?_take_of_lt hb, List.getElem?_eq_getElem]
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  rcases applied_agree_over_time config machine hup hown env hc hrun a b with h | h
  · exact (Option.some.inj (hB.symm.trans (getElem?_of_prefix h hA))).symm ▸ rfl
  · exact Option.some.inj (hA.symm.trans (getElem?_of_prefix h hB)) ▸ rfl

theorem appliedAllCommitted_invariant :
    (cluster N config machine).Invariant env fun c => appliedAllCommitted c = true := by
  intro c hc
  simpa [appliedAllCommitted] using fun a _ => applied_eq_commit config machine hup hown env c hc a

theorem machinesRun_invariant [BEq M] [LawfulBEq M] :
    (cluster N config machine).Invariant env fun c => machinesRun c = true := by
  intro c hc
  simpa [machinesRun] using fun a _ => machine_eq_run config machine hup hown env c hc a

end Headlines

end RaftKV
