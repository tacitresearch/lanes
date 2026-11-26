/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import RaftKV.Proofs.Applied

/-!
# The cluster is the machine

With both switches of `Config` on, for every finite set of nodes, every machine and every
environment that does not hand a client's request to a node twice, the cluster refines the
service of its machine (`cluster_implements`): each command takes effect at one instant between
its arrival and its answer.

The simulation (`Sim`) relates a state of the cluster with its history to a state of the service
through the list the cluster has committed to (`Logged`):

- the service's value is the machine run over that list;
- its outbox is the cluster's, and the answers nodes have yet to give for entries of the list
  they took from a client and have not applied (`owed`);
- its pending requests include those in flight to a node and those of every entry, in a log or
  in an `append` in flight, past the end of the list (`Accounts`).

A command takes effect when the list grows over its entry, which is when some node first commits
it. One step of a node can commit several entries, and the service then takes several internal
steps (`Sim.extend`). The pending requests are bounded from below, not given: a request that
was lost, or whose entry was replaced, stays pending in the service for ever, which the service
allows. So no ghost has to count requests.
-/

namespace RaftKV

open Lanes Cslib

variable {N C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N]
variable {config : Config} {machine : Machine C R M}

/-- The request an entry was made of. -/
def Entry.request (entry : Entry N C) : Request N C :=
  ⟨entry.req, entry.origin, entry.cmd⟩

/-- The answer to `entry` when it is applied after `before`. -/
def Machine.answer (machine : Machine C R M) (before : List (Entry N C)) (entry : Entry N C) :
    Response R :=
  ⟨entry.req, (machine.apply (machine.run machine.init before) entry.cmd).2⟩

section Owed

/-- The answers nodes have yet to give for `log`: each node's, to its entries past what it has
applied. -/
def owed (machine : Machine C R M) (log : List (Entry N C)) (applied : N → Nat) :
    Multiset (Response R) :=
  ∑ a ∈ (Enum.all (α := N)).toFinset,
    (↑(machine.replies a (machine.run machine.init (log.take (applied a)))
      (log.drop (applied a))) : Multiset (Response R))

omit [DecidableEq C] [DecidableEq R] in
theorem owed_nil (applied : N → Nat) : owed machine ([] : List (Entry N C)) applied = 0 := by
  simp [owed, Machine.replies]

omit [DecidableEq C] [DecidableEq R] in
/-- An entry added to the list is owed its answer by its origin. -/
theorem owed_concat (log : List (Entry N C)) (entry : Entry N C) {applied : N → Nat}
    (h : ∀ a, applied a ≤ log.length) :
    owed machine (log ++ [entry]) applied = owed machine log applied + {machine.answer log entry} := by
  have hterm : ∀ a, (↑(machine.replies a (machine.run machine.init ((log ++ [entry]).take (applied a)))
      ((log ++ [entry]).drop (applied a))) : Multiset (Response R)) =
      ↑(machine.replies a (machine.run machine.init (log.take (applied a))) (log.drop (applied a)))
        + if entry.origin = a then {machine.answer log entry} else 0 := by
    intro a
    rw [List.take_append_of_le_length (h a), List.drop_append_of_le_length (h a),
      Machine.replies_append, ← Machine.run_append, List.take_append_drop, ← Multiset.coe_add]
    congr 1
    by_cases horigin : entry.origin = a <;> simp [Machine.replies, Machine.answer, horigin]
  simp only [owed, hterm, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq]
  simp [Enum.complete]

omit [DecidableEq C] [DecidableEq R] in
/-- A node that applies entries gives the answers it owed for them. -/
theorem owed_advance (log : List (Entry N C)) {applied applied' : N → Nat} {i : N}
    (hother : ∀ a, a ≠ i → applied' a = applied a) (hle : applied i ≤ applied' i)
    (hlen : applied' i ≤ log.length) :
    owed machine log applied =
      ↑(machine.replies i (machine.run machine.init (log.take (applied i)))
        ((log.take (applied' i)).drop (applied i))) + owed machine log applied' := by
  have hi : i ∈ (Enum.all (α := N)).toFinset := by simp [Enum.complete]
  have hsplit : log.drop (applied i) =
      (log.take (applied' i)).drop (applied i) ++ log.drop (applied' i) := by
    rw [← List.drop_append_of_le_length (by rw [List.length_take]; omega),
      List.take_append_drop]
  have hrun : machine.run (machine.run machine.init (log.take (applied i)))
      ((log.take (applied' i)).drop (applied i)) =
      machine.run machine.init (log.take (applied' i)) := by
    rw [← Machine.run_append]
    congr 1
    conv_rhs => rw [← List.take_append_drop (applied i) (log.take (applied' i))]
    rw [List.take_take, Nat.min_eq_left hle]
  rw [owed, owed, ← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi, hsplit,
    Machine.replies_append, hrun, ← Multiset.coe_add, add_assoc]
  congr 2
  exact Finset.sum_congr rfl fun a ha => by rw [hother a (Finset.ne_of_mem_erase ha)]

end Owed

section Accounts

/-- The requests in flight to a node. -/
def inflight (net : List (Envelope (sig N C R))) : List (Request N C) :=
  net.filterMap fun e =>
    match (e.msg : Msg N C) with
    | .propose req cmd => some ⟨req, e.dst, cmd⟩
    | _ => none

/-- `entry` is entry `k + 1` of some node's log or of the log an `append` in flight was cut
from. -/
def Present (c : SysState (recording N config machine)) (k : Nat) (entry : Entry N C) : Prop :=
  (∃ a, (c.state a).1.log[k]? = some entry) ∨
    ∃ src dst term leader prev prevTerm entries commit,
      (⟨src, dst, .append term leader prev prevTerm entries commit⟩ : Envelope (sig N C R)) ∈ c.net
        ∧ prev ≤ k ∧ entries[k - prev]? = some entry

/-- `pending` has every request in flight to a node and, once for each place past the end of
`log` and each entry present there, the request the entry was made of. -/
def Accounts (c : SysState (recording N config machine)) (log : List (Entry N C))
    (pending : Multiset (Request N C)) : Prop :=
  ∃ live : Finset (Nat × Entry N C),
    (∀ k entry, Present c k entry → log.length ≤ k → (k, entry) ∈ live) ∧
      (↑(inflight c.net) : Multiset (Request N C)) + live.val.map (fun p => p.2.request) ≤ pending

omit [Enum N] in
theorem inflight_append (a b : List (Envelope (sig N C R))) :
    inflight (a ++ b) = inflight a ++ inflight b :=
  List.filterMap_append

omit [Enum N] in
theorem inflight_le {a b : List (Envelope (sig N C R))} (h : a.Sublist b) :
    (↑(inflight a) : Multiset (Request N C)) ≤ ↑(inflight b) :=
  Multiset.coe_le.mpr (h.filterMap _).subperm

omit [Enum N] in
/-- A request that is delivered is no longer in flight. -/
theorem inflight_erase {net : List (Envelope (sig N C R))} {src : Option N} {dst : N}
    {req : ReqId} {cmd : C} (h : (⟨src, dst, .propose req cmd⟩ : Envelope (sig N C R)) ∈ net) :
    ((⟨req, dst, cmd⟩ : Request N C) ::ₘ ↑(inflight (net.erase ⟨src, dst, .propose req cmd⟩)) :
      Multiset (Request N C)) = ↑(inflight net) := by
  have hperm : (inflight net).Perm
      (⟨req, dst, cmd⟩ :: inflight (net.erase ⟨src, dst, .propose req cmd⟩)) :=
    (List.perm_cons_erase h).filterMap _
  exact (Multiset.coe_eq_coe.mpr hperm).symm

variable {c : SysState (recording N config machine)} {log : List (Entry N C)}
  {pending : Multiset (Request N C)}

theorem Accounts.loses {c' : SysState (recording N config machine)} (h : Accounts c log pending)
    (hl : c'.Loses c) : Accounts c' log pending := by
  obtain ⟨live, hcovers, hcount⟩ := h
  refine ⟨live, fun k entry hpresent => hcovers k entry ?_,
    (add_le_add_left (inflight_le hl.net) _).trans hcount⟩
  rcases hpresent with ⟨a, ha⟩ | ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, h⟩
  · exact .inl ⟨a, by rwa [← hl.state]⟩
  · exact .inr ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hl.net.subset hmem, h⟩

theorem Accounts.input (h : Accounts c log pending) (x : Request N C) :
    Accounts { c with net := c.net ++ [⟨none, x.via, .propose x.req x.cmd⟩] } log
      (x ::ₘ pending) := by
  obtain ⟨live, hcovers, hcount⟩ := h
  refine ⟨live, fun k entry hpresent => hcovers k entry ?_, ?_⟩
  · rcases hpresent with ha | ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, h⟩
    · exact .inl ha
    · refine .inr ⟨src, dst, term, leader, prev, prevTerm, entries, commit, ?_, h⟩
      simpa using hmem
  · have hin : inflight (c.net ++ [(⟨none, x.via, .propose x.req x.cmd⟩ : Envelope (sig N C R))]) =
        inflight c.net ++ [x] := by simp [inflight]
    simp only [hin, ← Multiset.coe_add, ← Multiset.singleton_add, Multiset.coe_singleton]
    rw [add_comm (↑(inflight c.net) : Multiset (Request N C)), add_assoc]
    exact add_le_add_right hcount _

/-- An entry at the end of `log` is accounted for: its request is pending, and with the entry
added to `log` it is no longer needed. -/
theorem Accounts.extend (h : Accounts c log pending) {entry : Entry N C}
    (hpresent : Present c log.length entry) :
    entry.request ∈ pending ∧ Accounts c (log ++ [entry]) (pending.erase entry.request) := by
  obtain ⟨live, hcovers, hcount⟩ := h
  have hmem := hcovers _ entry hpresent (Nat.le_refl _)
  have hval : live.val = (log.length, entry) ::ₘ (live.erase (log.length, entry)).val := by
    rw [Finset.erase_val, Multiset.cons_erase hmem]
  rw [hval, Multiset.map_cons, Multiset.add_cons] at hcount
  refine ⟨Multiset.mem_of_le hcount (Multiset.mem_cons_self _ _),
    live.erase (log.length, entry), fun k e hp hk => ?_, ?_⟩
  · rw [List.length_append, List.length_singleton] at hk
    exact Finset.mem_erase.mpr ⟨fun heq => by simp at heq; omega, hcovers k e hp (by omega)⟩
  · have := Multiset.erase_le_erase entry.request hcount
    rwa [Multiset.erase_cons_head] at this

variable {i : N} {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

omit [Enum N] in
theorem inflight_sends {s : Node N C M} (hserves : Serves machine i s msg s' effs) :
    inflight (Effect.sends i effs) = [] := by
  rw [inflight, List.filterMap_eq_nil_iff]
  rintro ⟨src, dst, m⟩ he
  have hsent := (Effect.mem_sends.mp he).2
  cases m <;> first | rfl | exact absurd hsent (hserves.proposes _ _ _)

/-- An entry in the log of a node that has moved was in its log, or in the `append` it handled,
or is the request it handled. -/
theorem Present.of_moved (hserves : Serves machine i (c.state i).1 msg s' effs)
    (hpending : Pending c i msg) {k : Nat} {entry : Entry N C} (h : s'.log[k]? = some entry) :
    Present c k entry ∨ (k = (c.state i).1.log.length ∧ ∃ req cmd,
      msg = some (.propose req cmd) ∧ entry = ⟨(c.state i).1.term, i, req, cmd⟩) := by
  rcases hserves.log with hlog | ⟨req, cmd, hmsg, hlog⟩ |
    ⟨term, leader, prev, prevTerm, entries, commit, hmsg, hprev, hlog⟩
  · exact .inl (.inl ⟨i, hlog ▸ h⟩)
  · rw [hlog] at h
    by_cases hk : k < (c.state i).1.log.length
    · rw [List.getElem?_append_left hk] at h
      exact .inl (.inl ⟨i, h⟩)
    · rw [List.getElem?_append_right (by omega)] at h
      cases hd : k - (c.state i).1.log.length with
      | zero =>
        rw [hd] at h
        exact .inr ⟨by omega, req, cmd, hmsg, by simpa using h.symm⟩
      | succ d => simp [hd] at h
  · have hlen : ((c.state i).1.log.take prev).length = prev := by
      rw [List.length_take]
      omega
    rw [hlog] at h
    by_cases hk : k < prev
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hk] at h
      exact .inl (.inl ⟨i, h⟩)
    · rw [List.getElem?_append_right (by omega), hlen] at h
      rcases getElem?_merge h with h | h
      · rw [List.getElem?_drop, show prev + (k - prev) = k by omega] at h
        exact .inl (.inl ⟨i, h⟩)
      · rcases hpending _ hmsg with ⟨src, hnet⟩ | h' | h'
        · exact .inl (.inr ⟨src, i, term, leader, prev, prevTerm, entries, commit, hnet,
            by omega, h⟩)
        · cases h'
        · cases h'

theorem Present.of_grow {net : List (Envelope (sig N C R))} (hsub : ∀ e ∈ net, e ∈ c.net)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (hserves : Serves machine i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    {k : Nat} {entry : Entry N C}
    (h : Present (({ c with net := net }).grow i ((s', c.seen i), effs)) k entry) :
    Present c k entry ∨ (k = (c.state i).1.log.length ∧ ∃ req cmd,
      msg = some (.propose req cmd) ∧ entry = ⟨(c.state i).1.term, i, req, cmd⟩) := by
  rcases h with ⟨a, ha⟩ |
    ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, hk, hentry⟩
  · by_cases hai : a = i
    · subst hai
      rw [SysState.grow_state_self] at ha
      exact Present.of_moved hserves hpending ha
    · rw [SysState.grow_state_of_ne _ _ hai] at ha
      exact .inl (.inl ⟨a, ha⟩)
  · rcases SysState.mem_grow_net.mp hmem with hold | ⟨_, hnew⟩
    · exact .inl (.inr ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hsub _ hold,
        hk, hentry⟩)
    · obtain ⟨_, _, _, _, rfl, _⟩ := hmoves.sent _ hnew
      rw [List.getElem?_drop, show prev + (k - prev) = k by omega] at hentry
      exact Present.of_moved hserves hpending hentry

/-- A node that moves keeps the account: the entry it adds is the request it took out of the
network. -/
theorem Accounts.grow {net : List (Envelope (sig N C R))} (h : Accounts c log pending)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (hserves : Serves machine i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    (hsub : net.Sublist c.net)
    (htaken : ∀ req cmd, msg = some (.propose req cmd) →
      ((⟨req, i, cmd⟩ : Request N C) ::ₘ ↑(inflight net) : Multiset (Request N C))
        ≤ ↑(inflight c.net)) :
    Accounts (({ c with net := net }).grow i ((s', c.seen i), effs)) log pending := by
  obtain ⟨live, hcovers, hcount⟩ := h
  have hnet : inflight (({ c with net := net }).grow i ((s', c.seen i), effs)).net =
      inflight net := by
    show inflight (net ++ Effect.sends i effs) = inflight net
    rw [inflight_append, inflight_sends hserves, List.append_nil]
  rw [Accounts, hnet]
  by_cases hp : ∃ req cmd, msg = some (.propose req cmd)
  · obtain ⟨req, cmd, rfl⟩ := hp
    refine ⟨insert ((c.state i).1.log.length, ⟨(c.state i).1.term, i, req, cmd⟩) live,
      fun k entry hpresent hk => ?_, ?_⟩
    · rcases hpresent.of_grow hsub.subset hmoves hserves hpending with hold | ⟨rfl, _, _, hmsg, rfl⟩
      · exact Finset.mem_insert_of_mem (hcovers k entry hold hk)
      · obtain ⟨rfl, rfl⟩ := Msg.propose.inj (Option.some.inj hmsg)
        exact Finset.mem_insert_self _ _
    · have hinsert : (insert ((c.state i).1.log.length,
          (⟨(c.state i).1.term, i, req, cmd⟩ : Entry N C)) live).val.map (fun p => p.2.request) ≤
          (⟨req, i, cmd⟩ : Request N C) ::ₘ live.val.map (fun p => p.2.request) := by
        rw [Finset.insert_val]
        exact (Multiset.map_le_map (Multiset.ndinsert_le.mpr
          ⟨Multiset.le_cons_self _ _, Multiset.mem_cons_self _ _⟩)).trans
          (le_of_eq (Multiset.map_cons _ _ _))
      refine (add_le_add_right hinsert _).trans ?_
      rw [Multiset.add_cons, ← Multiset.cons_add]
      exact (add_le_add_left (htaken req cmd rfl) _).trans hcount
  · refine ⟨live, fun k entry hpresent hk => ?_, (add_le_add_left (inflight_le hsub) _).trans hcount⟩
    rcases hpresent.of_grow hsub.subset hmoves hserves hpending with hold | ⟨_, req, cmd, hmsg, _⟩
    · exact hcovers k entry hold hk
    · exact absurd ⟨req, cmd, hmsg⟩ hp

end Accounts

/-- The service of the machine, as the transition system the cluster refines. -/
abbrev service (N : Type) {C R M : Type} [DecidableEq N] [DecidableEq C] [DecidableEq R]
    (machine : Machine C R M) : Spec (Service.Abs (sig N C R) M) (Option (Visible (sig N C R))) :=
  (spec machine).spec

/-- The simulation: the state `t` of the service explains the state `c` of the cluster, with
`log` the list the cluster has committed to. -/
structure Sim (c : SysState (recording N config machine)) (t : Service.Abs (sig N C R) M)
    (log : List (Entry N C)) : Prop where
  logged : Logged c log
  value : t.value = machine.run machine.init log
  outbox : t.outbox = ↑c.outbox + owed machine log fun a => (c.state a).1.applied
  pending : Accounts c log t.pending

namespace Sim

variable {c : SysState (recording N config machine)} {t : Service.Abs (sig N C R) M}
  {log : List (Entry N C)}

theorem blank : Sim (SysState.blank (recording N config machine)) ⟨machine.init, 0, 0⟩ [] where
  logged := .blank
  value := rfl
  outbox := by simp [owed_nil, SysState.blank]
  pending := by
    refine ⟨∅, ?_, by simp [inflight, SysState.blank]⟩
    rintro k entry (⟨a, ha⟩ | ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, _⟩)
    · simp [SysState.blank, recording, System.withPast, System.withGhost, node] at ha
    · simp [SysState.blank] at hmem

theorem loses {c' : SysState (recording N config machine)} (h : Sim c t log) (hl : c'.Loses c) :
    Sim c' t log where
  logged := h.logged.of_state hl.state
  value := h.value
  outbox := by rw [hl.outbox, hl.state]; exact h.outbox
  pending := h.pending.loses hl

theorem input (h : Sim c t log) (x : Request N C) :
    Sim { c with net := c.net ++ [⟨none, x.via, .propose x.req x.cmd⟩] }
      { t with pending := x ::ₘ t.pending } log where
  logged := h.logged.of_state rfl
  value := h.value
  outbox := h.outbox
  pending := h.pending.input x

theorem output (h : Sim c t log) {out : Response R} (hmem : out ∈ c.outbox) :
    out ∈ t.outbox ∧ Sim { c with outbox := c.outbox.erase out }
      { t with outbox := t.outbox.erase out } log := by
  have hin : out ∈ (↑c.outbox : Multiset (Response R)) := Multiset.mem_coe.mpr hmem
  refine ⟨h.outbox ▸ Multiset.mem_add.mpr (.inl hin), h.logged.of_state rfl, h.value, ?_,
    h.pending⟩
  show t.outbox.erase out = ↑(c.outbox.erase out) + _
  rw [h.outbox, Multiset.erase_add_left_pos _ hin, Multiset.coe_erase]

variable {i : N}

theorem recover (h : Sim c t log) :
    Sim (c.grow i (((recording N config machine).actor i).recover (c.state i))) t log where
  logged := h.logged.recover
  value := h.value
  outbox := by
    have happlied : (fun a => ((c.grow i (((recording N config machine).actor i).recover
        (c.state i))).state a).1.applied) = fun a => (c.state a).1.applied := by
      funext a
      by_cases ha : a = i
      · subst ha
        rw [SysState.grow_state_self]
        rfl
      · rw [SysState.grow_state_of_ne _ _ ha]
    have hout : (c.grow i (((recording N config machine).actor i).recover (c.state i))).outbox =
        c.outbox := List.append_nil _
    rw [happlied, hout, h.outbox]
  pending := by
    have := h.pending.grow (net := c.net)
      (recover_moves config Enum.all machine i (c.state i).1)
      (recover_serves config Enum.all machine i (c.state i).1) pending_none
      (List.Sublist.refl _) nofun
    exact this

/-- The service takes one internal step for each entry the list grows by: the entry's request
takes effect and its answer is owed. The cluster's outbox `out` and what each node has applied
are held fixed here; `Sim.step` moves them after. -/
theorem extend {out : List (Response R)} {applied : N → Nat} (ext : List (Entry N C)) :
    ∀ {log : List (Entry N C)} {t : Service.Abs (sig N C R) M},
      (∀ a, applied a ≤ log.length) → t.value = machine.run machine.init log →
      t.outbox = ↑out + owed machine log applied → Accounts c log t.pending →
      (∀ k entry, ext[k]? = some entry → Present c (log.length + k) entry) →
      ∃ t', (service N machine).lts.τSTr t t' ∧ t'.value = machine.run machine.init (log ++ ext) ∧
        t'.outbox = ↑out + owed machine (log ++ ext) applied ∧
        Accounts c (log ++ ext) t'.pending := by
  induction ext with
  | nil =>
    intro log t _ hvalue houtbox hpending _
    exact ⟨t, .refl, by simpa using hvalue, by simpa using houtbox, by simpa using hpending⟩
  | cons entry ext ih =>
    intro log t hbound hvalue houtbox hpending hpresent
    obtain ⟨hmem, hpending'⟩ := hpending.extend (hpresent 0 entry rfl)
    obtain ⟨t', ht', hvalue', houtbox', hrest⟩ := ih
      (log := log ++ [entry])
      (t := ⟨machine.run machine.init (log ++ [entry]), t.pending.erase entry.request,
        t.outbox + {machine.answer log entry}⟩)
      (fun a => by simpa using Nat.le_succ_of_le (hbound a)) rfl
      (by rw [owed_concat log entry hbound, houtbox, add_assoc]) hpending'
      (fun k e hk => by
        have := hpresent (k + 1) e (by simpa using hk)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this)
    refine ⟨t', .head ?_ ht', by simpa using hvalue', by simpa using houtbox',
      by simpa using hrest⟩
    refine ⟨entry.request, hmem, ?_⟩
    simp [spec, Entry.request, Machine.answer, Machine.run, hvalue, List.foldl_append]

variable {msg : Option (Msg N C)} {s' : Node N C M} {effs : List (Effect (sig N C R) i)}

/-- A node handles a message, taken from `net`, which is what was in flight without it. The
service takes one internal step for each entry the node is the first to commit. -/
theorem step {net : List (Envelope (sig N C R))} (h : Sim c t log) (hc : Commits c)
    (hc' : Committing (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (hserves : Serves machine i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    (hsub : net.Sublist c.net)
    (htaken : ∀ req cmd, msg = some (.propose req cmd) →
      ((⟨req, i, cmd⟩ : Request N C) ::ₘ ↑(inflight net) : Multiset (Request N C))
        ≤ ↑(inflight c.net)) :
    ∃ t' log', (service N machine).lts.τSTr t t' ∧
      Sim (({ c with net := net }).grow i ((s', c.seen i), effs)) t' log' := by
  obtain ⟨log', ⟨ext, rfl⟩, hgrown, hupper, hwhich⟩ :=
    h.logged.grow hc hc'.replicating hc'.safe hc'.commits hmoves hserves
  have hlogged' : Logged (({ c with net := net }).grow i ((s', c.seen i), effs)) (log ++ ext) :=
    hgrown.of_state rfl
  have hbound := h.logged.applied_le hc
  have hpresent : ∀ k entry, ext[k]? = some entry →
      Present (({ c with net := net }).grow i ((s', c.seen i), effs)) (log.length + k) entry := by
    intro k entry hk
    rcases hwhich with hsame | hmine
    · simp [List.append_right_eq_self.mp hsame] at hk
    · refine .inl ⟨i, ?_⟩
      rw [SysState.grow_state_self]
      have hat : (log ++ ext)[log.length + k]? = some entry := by
        rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact hk
      rw [hmine, List.getElem?_take] at hat
      split at hat
      · exact hat
      · cases hat
  obtain ⟨t', ht', hvalue', houtbox', hpending'⟩ := extend ext hbound h.value h.outbox
    (h.pending.grow hmoves hserves hpending hsub htaken) hpresent
  refine ⟨t', log ++ ext, ht', hlogged', hvalue', ?_, hpending'⟩
  obtain ⟨_, _, hemits⟩ := hserves.applies (Nat.le_of_eq (h.logged.applied i).symm)
  have hnode := hc'.commits.nodes i
  simp only [SysState.grow_state_self] at hnode
  have happlied' := hlogged'.applied i
  simp only [SysState.grow_state_self] at happlied'
  have hmine : (log ++ ext).take s'.applied = s'.log.take s'.commit := by
    rw [happlied', take_of_prefix hupper (by rw [List.length_take]; omega), List.take_take,
      Nat.min_self]
  have hadvance := owed_advance (machine := machine) (log ++ ext) (i := i)
    (applied := fun a => (c.state a).1.applied)
    (applied' := fun a =>
      ((({ c with net := net }).grow i ((s', c.seen i), effs)).state a).1.applied)
    (fun a ha => by simp [ha])
    (by
      have := hmoves.commit_le
      have := h.logged.applied i
      simp only [SysState.grow_state_self]
      omega)
    (hgrown.applied_le hc'.commits i)
  simp only [SysState.grow_state_self] at hadvance
  rw [hmine, take_of_prefix (List.prefix_append log ext) (hbound i), ← h.logged.machine i,
    ← hemits] at hadvance
  rw [houtbox', hadvance, ← add_assoc, Multiset.coe_add]
  rfl

end Sim

section Theorem

variable (hup : config.votesForUpToDateOnly = true) (hown : config.commitsOwnTermOnly = true)

include hup hown

/-- `Sim.step` of the step function, with what it needs of the state after taken from the
invariant. -/
theorem Sim.handle {c : SysState (recording N config machine)} {t : Service.Abs (sig N C R) M}
    {log : List (Entry N C)} (h : Sim c t log) (hc : Committing c) {i : N} {m : Msg N C}
    {net : List (Envelope (sig N C R))} (hsub : net.Sublist c.net)
    (hpending : (∃ src, (⟨src, i, m⟩ : Envelope (sig N C R)) ∈ c.net) ∨ m ∈ c.timers i)
    (htaken : ∀ req cmd, m = .propose req cmd →
      ((⟨req, i, cmd⟩ : Request N C) ::ₘ ↑(inflight net) : Multiset (Request N C))
        ≤ ↑(inflight c.net)) :
    ∃ t', (service N machine).lts.τSTr t t' ∧ ∃ log', Sim (({ c with net := net }).grow i
      (((recording N config machine).actor i).step (c.state i) m)) t' log' := by
  obtain ⟨t', log', ht', h'⟩ := h.step hc.commits
    ((committing_monotone hup hown).step c i m hc hpending)
    (step_moves config Enum.all machine i (c.state i).1 m)
    (step_serves config Enum.all machine i (c.state i).1 m)
    (hc.replicating.timers.pending hpending) hsub
    fun req cmd hm => htaken req cmd (Option.some.inj hm)
  exact ⟨t', ht', log', h'⟩

variable (env : EnvModel (sig N C R)) (henv : ∀ node, (env.link none node).duplicating = false)

include henv

/-- The cluster with its history refines the service of its machine. -/
theorem recording_refines : (recording N config machine).Refines env (service N machine) := by
  have hinv : (recording N config machine).Invariant env fun c => Committing c ∧ FromClients c :=
    fun c hc => ⟨(committing_monotone hup hown).invariant env c hc,
      (fromClients_monotone.invariant env c hc).2⟩
  refine System.Refines.of_steps hinv (fun c t => ∃ log, Sim c t log) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨⟨machine.init, 0, 0⟩, rfl, [], SysState.init_induction (env := env)
      (P := fun c => Sim c ⟨machine.init, 0, 0⟩ []) .blank
      fun c i h => h.recover.loses (SysState.Loses.startActor c env i)⟩
  · exact fun c c' t ⟨log, h⟩ hl => ⟨log, h.loses hl⟩
  · exact fun c t x _ ⟨log, h⟩ => ⟨{ t with pending := x ::ₘ t.pending }, .single rfl, log, h.input x⟩
  · intro c t out _ ⟨log, h⟩ hmem
    obtain ⟨hout, h'⟩ := h.output hmem
    exact ⟨{ t with outbox := t.outbox.erase out }, .single ⟨hout, rfl⟩, log, h'⟩
  · rintro c t ⟨src, dst, m⟩ ⟨hc, _⟩ ⟨log, h⟩ hmem
    exact h.handle hup hown hc (net := c.net.erase ⟨src, dst, m⟩) List.erase_sublist
      (.inl ⟨src, hmem⟩) fun req cmd hm => by
        subst hm
        exact le_of_eq (inflight_erase hmem)
  · rintro c t ⟨src, dst, m⟩ ⟨hc, hclients⟩ ⟨log, h⟩ hmem hdup
    refine h.handle hup hown hc (net := c.net) (List.Sublist.refl _) (.inl ⟨src, hmem⟩)
      fun req cmd hm => ?_
    subst hm
    obtain rfl := hclients src dst req cmd hmem
    simp [henv dst] at hdup
  · rintro c t i m ⟨hc, _⟩ ⟨log, h⟩ hmem
    refine h.handle hup hown hc (net := c.net) (List.Sublist.refl _) (.inr hmem)
      fun req cmd hm => ?_
    subst hm
    rcases hc.replicating.timers i _ hmem with h | h <;> cases h
  · exact fun c t i _ ⟨log, h⟩ => ⟨t, .refl, log, h.recover⟩

/--
The cluster is the machine. To its clients, a Raft cluster of any size, with nodes crashing and
restarting and links between nodes losing, repeating and reordering messages, behaves as the
one machine it replicates, each command taking effect at one instant between its arrival and its
answer. The assumption is that no request is handed to a node twice.
-/
theorem cluster_implements : (cluster N config machine).Implements env (spec machine) :=
  System.Refines.of_ghost (.past _) (recording_refines hup hown env henv)

end Theorem

end RaftKV
