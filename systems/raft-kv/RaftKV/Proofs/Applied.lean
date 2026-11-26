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
safety.

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

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem take_of_prefix {α : Type} {a b : List α} (h : a <+: b) {n : Nat} (hn : n ≤ a.length) :
    b.take n = a.take n := by
  obtain ⟨rest, rfl⟩ := h
  exact List.take_append_of_le_length hn

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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Committed, Chosen, Held, Led, SysState.seen, hstate]
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
  refine (committing_monotone hup hown).and ⟨[], .blank⟩
    (fun _ _ _ ⟨log, h⟩ hbelow => ⟨log, h.of_state hbelow.state⟩)
    (fun _ _ _ ⟨log, h⟩ => ⟨log, h.of_state rfl⟩) ?_ ?_
  · intro c i msg hp hp' ⟨log, h⟩ _
    obtain ⟨log', _, h', _⟩ := h.grow hp.2 hp'.1.1.1 hp'.1.2 hp'.2
      (step_moves config Enum.all machine i _ msg) (step_serves config Enum.all machine i _ msg)
    exact ⟨log', h'⟩
  · exact fun c i _ _ ⟨log, h⟩ => ⟨log, h.recover⟩

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
    exact (h.machine a).trans (congrArg _ (h.take_applied hcommitting.2 a))

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
    rw [← h.take_applied hcommitting.2 a, ← h.take_applied hcommitting.2 b]
    exact (List.take_prefix_take_left hle)

end Headlines

end RaftKV
