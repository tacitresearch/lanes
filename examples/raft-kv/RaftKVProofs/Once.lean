/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import RaftKVProofs.Refines
import RaftKV.Once

/-!
# The cluster is the machine, once per command

With the machine behind its memo (`Machine.once`), for every finite set of nodes, every machine,
every set of clients and every environment, the cluster with its empty answers hidden
implements `once` of the named machine (`onceCluster_implements`): each command takes effect at
most once, at one instant between its arrival and an answer, whatever the links lose, reorder
and repeat, those from clients included.

The simulation (`OnceSim`) is `Sim` of `RaftKVProofs/Refines.lean` with membership for counting.
The spec's state only grows (`Service.Once.Grows`), so a request is accounted for by having
arrived, wherever it is and however many copies of it there are; and an answer by having been
given, by whichever node gives it and however often. The list the cluster has committed to
(`Logged`) is as there; run over it, the machine behind the memo is the spec's value and a memo
that agrees with the keys taken (`Once.Memo.Agrees`), and each answer it gives along the list is
empty or given (`Answered`). A command takes effect when the list grows over the first entry of
its key, which is when the memo finds it fresh.
-/

namespace RaftKV

open Lanes Cslib

variable {N Cl C R M : Type} [DecidableEq N] [DecidableEq Cl] [DecidableEq C] [DecidableEq R]
  [Enum N] {config : Config} {machine : Machine C R M}

/-- The state of `once` of the named machine. -/
abbrev OnceAbs (N Cl C R M : Type) :=
  Service.Once (Request N (Named Cl C)) (Named Cl R) M (Cl × Nat)

/-- `once` of the named machine, for a cluster whose empty answers are hidden. -/
abbrev onceService (N Cl : Type) [DecidableEq N] [DecidableEq Cl] (machine : Machine C R M) :=
  ((named N Cl machine).once Request.key).showing (Response.res (R := Option (Named Cl R)))

section Machine

variable {m : M} {memo : Once.Memo Cl (Named Cl R)} {c : Cl} {n : Nat} {cmd : C}

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem once_apply_fresh (hs : memo.seen c n = .fresh) :
    (machine.once Cl).apply (m, memo) ⟨c, n, cmd⟩ =
      (((machine.apply m cmd).1, memo.record c n [⟨c, n, (machine.apply m cmd).2⟩]),
        some ⟨c, n, (machine.apply m cmd).2⟩) := by
  simp [Machine.once, hs]

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem once_apply_again {answers : List (Named Cl R)} (hs : memo.seen c n = .again answers) :
    (machine.once Cl).apply (m, memo) ⟨c, n, cmd⟩ = ((m, memo), answers.head?) := by
  simp [Machine.once, hs]

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem once_apply_stale (hs : memo.seen c n = .stale) :
    (machine.once Cl).apply (m, memo) ⟨c, n, cmd⟩ = ((m, memo), none) := by
  simp [Machine.once, hs]

end Machine

/-- Every answer the machine behind the memo gives along `log` is empty or is in `answered`. -/
def Answered (machine : Machine C R M) (log : List (Entry N (Named Cl C)))
    (answered : Set (Named Cl R)) : Prop :=
  ∀ pre entry a, pre ++ [entry] <+: log →
    ((machine.once Cl).apply ((machine.once Cl).run (machine.once Cl).init pre) entry.cmd).2 =
      some a → a ∈ answered

namespace Answered

variable {log : List (Entry N (Named Cl C))} {answered answered' : Set (Named Cl R)}

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem nil : Answered machine ([] : List (Entry N (Named Cl C))) answered := by
  intro pre entry a h
  have := h.length_le
  simp at this

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem mono (h : Answered machine log answered) (hg : answered ⊆ answered') :
    Answered machine log answered' :=
  fun pre entry a hp ha => hg (h pre entry a hp ha)

omit [DecidableEq N] [DecidableEq C] [DecidableEq R] [Enum N] in
theorem concat (h : Answered machine log answered) {entry : Entry N (Named Cl C)}
    (hentry : ∀ a, ((machine.once Cl).apply ((machine.once Cl).run (machine.once Cl).init log)
      entry.cmd).2 = some a → a ∈ answered) :
    Answered machine (log ++ [entry]) answered := by
  intro pre e a hp ha
  rcases List.prefix_concat_iff.mp hp with heq | hp
  · obtain ⟨rfl, he⟩ := List.append_inj' heq rfl
    obtain rfl := List.singleton_inj.mp he
    exact hentry a ha
  · exact h pre e a hp ha

omit [DecidableEq C] [DecidableEq R] [Enum N] in
/-- What a node answers while it applies entries of `log` is empty or answered. -/
theorem replies (h : Answered machine log answered) (i : N) :
    ∀ (seg pre : List (Entry N (Named Cl C))), pre ++ seg <+: log →
      ∀ r ∈ (machine.once Cl).replies i ((machine.once Cl).run (machine.once Cl).init pre) seg,
        ∀ a, r.res = some a → a ∈ answered
  | [], _, _, r, hr => by simp [Machine.replies] at hr
  | e :: seg, pre, hp, r, hr => by
    have hp' : (pre ++ [e]) ++ seg <+: log := by simpa using hp
    simp only [Machine.replies, List.mem_append] at hr
    rcases hr with hr | hr
    · split at hr
      · obtain rfl := List.mem_singleton.mp hr
        exact fun a ha => h pre e a ((List.prefix_append _ _).trans hp') ha
      · simp at hr
    · have := replies h i seg (pre ++ [e]) hp' r
      rw [Machine.run_append] at this
      exact this hr

end Answered

/-- The simulation: `t` explains `c`, with `log` the list the cluster has committed to. -/
structure OnceSim (c : SysState (recording N config (machine.once Cl))) (t : OnceAbs N Cl C R M)
    (log : List (Entry N (Named Cl C))) : Prop where
  /-- `log` is what the cluster has committed to. -/
  logged : Logged c log
  /-- The spec's value is the machine run over `log`. -/
  value : ((machine.once Cl).run (machine.once Cl).init log).1 = t.value
  /-- The memo after `log` agrees with the keys taken. -/
  memo : ((machine.once Cl).run (machine.once Cl).init log).2.Agrees t.taken (· ∈ t.answered)
  /-- Every answer along `log` is empty or answered. -/
  answers : Answered machine log t.answered
  /-- Every answer waiting is empty or answered. -/
  outbox : ∀ out ∈ c.outbox, ∀ a, out.res = some a → a ∈ t.answered
  /-- Every request in flight to a node has arrived. -/
  requests : ∀ x ∈ inflight c.net, x ∈ t.arrived
  /-- The request of every entry in a log or in an `append` in flight has arrived. -/
  entries : ∀ k entry, Present c k entry → entry.request ∈ t.arrived

namespace OnceSim

variable {c : SysState (recording N config (machine.once Cl))} {t : OnceAbs N Cl C R M}
  {log : List (Entry N (Named Cl C))}

theorem blank :
    OnceSim (SysState.blank (recording N config (machine.once Cl))) ⟨machine.init, ∅, ∅, ∅⟩ [] where
  logged := .blank
  value := rfl
  memo := Once.Memo.Agrees.empty
  answers := .nil
  outbox := by simp [SysState.blank]
  requests := by simp [inflight, SysState.blank]
  entries := by
    rintro k entry (⟨a, ha⟩ | ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, _⟩)
    · simp [SysState.blank, recording, System.withPast, System.withGhost, node] at ha
    · simp [SysState.blank] at hmem

theorem loses {c' : SysState (recording N config (machine.once Cl))} (h : OnceSim c t log)
    (hl : c'.Loses c) : OnceSim c' t log where
  logged := h.logged.of_state hl.state
  value := h.value
  memo := h.memo
  answers := h.answers
  outbox := by rw [hl.outbox]; exact h.outbox
  requests x hx := h.requests x ((hl.net.filterMap _).subset hx)
  entries k entry hp := by
    refine h.entries k entry ?_
    rcases hp with ⟨a, ha⟩ | ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, h⟩
    · exact .inl ⟨a, by rwa [← hl.state]⟩
    · exact .inr ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hl.net.subset hmem, h⟩

theorem input (h : OnceSim c t log) (x : Request N (Named Cl C)) :
    OnceSim { c with net := c.net ++ [⟨none, x.via, .propose x.req x.cmd⟩] }
      { t with arrived := insert x t.arrived } log where
  logged := h.logged.of_state rfl
  value := h.value
  memo := h.memo
  answers := h.answers
  outbox := h.outbox
  requests y hy := by
    have hin : inflight (c.net ++ [(⟨none, x.via, .propose x.req x.cmd⟩ :
        Envelope (sig N (Named Cl C) (Option (Named Cl R))))]) = inflight c.net ++ [x] := by
      simp [inflight]
    rcases List.mem_append.mp (hin ▸ hy) with hy | hy
    · exact Set.mem_insert_of_mem _ (h.requests y hy)
    · exact List.mem_singleton.mp hy ▸ Set.mem_insert _ _
  entries k entry hp := by
    refine Set.mem_insert_of_mem _ (h.entries k entry ?_)
    rcases hp with ha | ⟨src, dst, term, leader, prev, prevTerm, entries, commit, hmem, h⟩
    · exact .inl ha
    · refine .inr ⟨src, dst, term, leader, prev, prevTerm, entries, commit, ?_, h⟩
      simpa using hmem

theorem output (h : OnceSim c t log) (out : Response (Option (Named Cl R))) :
    OnceSim { c with outbox := c.outbox.erase out } t log where
  logged := h.logged.of_state rfl
  value := h.value
  memo := h.memo
  answers := h.answers
  outbox o ho := h.outbox o (List.mem_of_mem_erase ho)
  requests := h.requests
  entries := h.entries

variable {i : N} {msg : Option (Msg N (Named Cl C))} {s' : Node N (Named Cl C) (M × Once.Memo Cl (Named Cl R))}
  {effs : List (Effect (sig N (Named Cl C) (Option (Named Cl R))) i)}

/-- An entry in a log or an `append` after a node moves has a request that has arrived: it was
there before, or it is the request the node took out of the network. -/
theorem present_grow {net : List (Envelope (sig N (Named Cl C) (Option (Named Cl R))))}
    (h : OnceSim c t log) (hsub : net.Sublist c.net)
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (hserves : Serves (machine.once Cl) i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    (hmsg : ∀ req cmd, msg = some (.propose req cmd) →
      (⟨req, i, cmd⟩ : Request N (Named Cl C)) ∈ inflight c.net) :
    ∀ k entry, Present (({ c with net := net }).grow i ((s', c.seen i), effs)) k entry →
      entry.request ∈ t.arrived := by
  intro k entry hp
  rcases hp.of_grow hsub.subset hmoves hserves hpending with hold | ⟨_, req, cmd, hm, rfl⟩
  · exact h.entries k entry hold
  · exact h.requests _ (hmsg req cmd hm)

theorem recover (h : OnceSim c t log) :
    OnceSim (c.grow i (((recording N config (machine.once Cl)).actor i).recover (c.state i))) t
      log where
  logged := h.logged.recover
  value := h.value
  memo := h.memo
  answers := h.answers
  outbox := by
    have hout : (c.grow i (((recording N config (machine.once Cl)).actor i).recover
        (c.state i))).outbox = c.outbox := List.append_nil _
    rw [hout]
    exact h.outbox
  requests x hx := by
    have hnet : inflight (c.grow i (((recording N config (machine.once Cl)).actor i).recover
        (c.state i))).net = inflight c.net := by
      show inflight (c.net ++ Effect.sends i
        ((node config Enum.all (machine.once Cl) i).recover (c.state i).1).2) = _
      rw [inflight_append, inflight_sends (recover_serves config Enum.all (machine.once Cl) i
        (c.state i).1), List.append_nil]
    exact h.requests x (hnet ▸ hx)
  entries := h.present_grow (net := c.net) (List.Sublist.refl _)
    (recover_moves config Enum.all (machine.once Cl) i (c.state i).1)
    (recover_serves config Enum.all (machine.once Cl) i (c.state i).1) pending_none nofun

omit [DecidableEq C] [DecidableEq R] [Enum N] in
/-- The list grows by one entry: the spec takes its request if the memo finds it fresh, and
nothing otherwise. -/
theorem extend_one {log : List (Entry N (Named Cl C))} {t : OnceAbs N Cl C R M}
    (entry : Entry N (Named Cl C))
    (hvalue : ((machine.once Cl).run (machine.once Cl).init log).1 = t.value)
    (hmemo : ((machine.once Cl).run (machine.once Cl).init log).2.Agrees t.taken (· ∈ t.answered))
    (hanswers : Answered machine log t.answered) (harrived : entry.request ∈ t.arrived) :
    ∃ t', ((named N Cl machine).once Request.key).lts.τSTr t t' ∧ t.Grows t' ∧
      ((machine.once Cl).run (machine.once Cl).init (log ++ [entry])).1 = t'.value ∧
      ((machine.once Cl).run (machine.once Cl).init (log ++ [entry])).2.Agrees t'.taken
        (· ∈ t'.answered) ∧
      Answered machine (log ++ [entry]) t'.answered := by
  obtain ⟨term, origin, req, c, n, cmd⟩ := entry
  have hrun : (machine.once Cl).run (machine.once Cl).init
      (log ++ [⟨term, origin, req, ⟨c, n, cmd⟩⟩]) =
      ((machine.once Cl).apply ((machine.once Cl).run (machine.once Cl).init log)
        ⟨c, n, cmd⟩).1 := by
    rw [Machine.run_append]
    rfl
  rcases hrl : (machine.once Cl).run (machine.once Cl).init log with ⟨v, memo⟩
  rw [hrl] at hvalue hmemo hrun
  simp only at hvalue hmemo
  cases hs : memo.seen c n with
  | fresh =>
    have hτ := Service.once_take (svc := named N Cl machine) (key := Request.key) harrived
      (hmemo.fresh hs)
    have hg := Service.once_grows_τSTr hτ
    have hgiven : (⟨c, n, (machine.apply v cmd).2⟩ : Named Cl R) ∈
        (t.take (named N Cl machine) Request.key
          (Entry.request ⟨term, origin, req, ⟨c, n, cmd⟩⟩)).answered :=
      Or.inr (by simp [named, Entry.request, hvalue])
    refine ⟨_, hτ, hg, ?_, ?_, ?_⟩
    · rw [hrun, once_apply_fresh hs]
      simp [Service.Once.take, named, Entry.request, hvalue]
    · rw [hrun, once_apply_fresh hs]
      exact (hmemo.mono fun _ ha => hg.answered ha).record hs (by simpa using hgiven)
    · refine (hanswers.mono hg.answered).concat fun a ha => ?_
      rw [hrl, once_apply_fresh hs] at ha
      exact Option.some.inj ha ▸ hgiven
  | again answers =>
    refine ⟨t, .refl, .refl _, ?_, ?_, ?_⟩
    · rw [hrun, once_apply_again hs]
      exact hvalue
    · rw [hrun, once_apply_again hs]
      exact hmemo
    · refine hanswers.concat fun a ha => ?_
      rw [hrl, once_apply_again hs] at ha
      exact hmemo.again hs a (List.mem_of_mem_head? ha)
  | stale =>
    refine ⟨t, .refl, .refl _, ?_, ?_, ?_⟩
    · rw [hrun, once_apply_stale hs]
      exact hvalue
    · rw [hrun, once_apply_stale hs]
      exact hmemo
    · refine hanswers.concat fun a ha => ?_
      rw [hrl, once_apply_stale hs] at ha
      cases ha

omit [DecidableEq C] [DecidableEq R] [Enum N] in
/-- The list grows by `ext`: the spec takes the request of each entry the memo finds fresh. -/
theorem extend (ext : List (Entry N (Named Cl C))) :
    ∀ {log : List (Entry N (Named Cl C))} {t : OnceAbs N Cl C R M},
      ((machine.once Cl).run (machine.once Cl).init log).1 = t.value →
      ((machine.once Cl).run (machine.once Cl).init log).2.Agrees t.taken (· ∈ t.answered) →
      Answered machine log t.answered → (∀ entry ∈ ext, entry.request ∈ t.arrived) →
      ∃ t', ((named N Cl machine).once Request.key).lts.τSTr t t' ∧ t.Grows t' ∧
        ((machine.once Cl).run (machine.once Cl).init (log ++ ext)).1 = t'.value ∧
        ((machine.once Cl).run (machine.once Cl).init (log ++ ext)).2.Agrees t'.taken
          (· ∈ t'.answered) ∧
        Answered machine (log ++ ext) t'.answered := by
  induction ext with
  | nil =>
    intro log t hvalue hmemo hanswers _
    exact ⟨t, .refl, .refl _, by simpa using hvalue, by simpa using hmemo, by simpa using hanswers⟩
  | cons entry ext ih =>
    intro log t hvalue hmemo hanswers harrived
    obtain ⟨t₁, ht₁, hg₁, hvalue₁, hmemo₁, hanswers₁⟩ :=
      extend_one entry hvalue hmemo hanswers (harrived entry List.mem_cons_self)
    obtain ⟨t', ht', hg', hvalue', hmemo', hanswers'⟩ := ih hvalue₁ hmemo₁ hanswers₁
      fun e he => hg₁.arrived (harrived e (List.mem_cons_of_mem _ he))
    exact ⟨t', ht₁.trans ht', hg₁.trans hg', by simpa using hvalue', by simpa using hmemo',
      by simpa using hanswers'⟩

/-- A node handles a message, with `net` what is left in flight. The spec takes the request of
each entry the node is the first to commit whose key the memo finds fresh. -/
theorem step {net : List (Envelope (sig N (Named Cl C) (Option (Named Cl R))))}
    (h : OnceSim c t log) (hc : Commits c)
    (hc' : Committing (c.grow i ((s', c.seen i), effs)))
    (hmoves : Moves config Enum.all i (c.state i).1 msg s' effs)
    (hserves : Serves (machine.once Cl) i (c.state i).1 msg s' effs) (hpending : Pending c i msg)
    (hsub : net.Sublist c.net)
    (hmsg : ∀ req cmd, msg = some (.propose req cmd) →
      (⟨req, i, cmd⟩ : Request N (Named Cl C)) ∈ inflight c.net) :
    ∃ t' log', ((named N Cl machine).once Request.key).lts.τSTr t t' ∧
      OnceSim (({ c with net := net }).grow i ((s', c.seen i), effs)) t' log' := by
  obtain ⟨log', ⟨ext, rfl⟩, hgrown, hupper, hwhich⟩ :=
    h.logged.grow hc hc'.replicating hc'.safe hc'.commits hmoves hserves
  have hlogged' : Logged (({ c with net := net }).grow i ((s', c.seen i), effs)) (log ++ ext) :=
    hgrown.of_state rfl
  have hbound := h.logged.applied_le hc
  have hpresent := h.present_grow hsub hmoves hserves hpending hmsg
  have harrived : ∀ entry ∈ ext, entry.request ∈ t.arrived := by
    intro entry he
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
    refine hpresent (log.length + k) entry ?_
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
  obtain ⟨t', ht', hg, hvalue', hmemo', hanswers'⟩ :=
    extend ext h.value h.memo h.answers harrived
  refine ⟨t', log ++ ext, ht', hlogged', hvalue', hmemo', hanswers', ?_, ?_, ?_⟩
  · intro out hout a ha
    rcases List.mem_append.mp hout with hout | hout
    · exact hg.answered (h.outbox out hout a ha)
    obtain ⟨_, _, hemits⟩ := hserves.applies (Nat.le_of_eq (h.logged.applied i).symm)
    have hnode := hc'.commits.nodes i
    simp only [SysState.grow_state_self] at hnode
    have happlied' := hlogged'.applied i
    simp only [SysState.grow_state_self] at happlied'
    have htaken : (log ++ ext).take s'.applied = s'.log.take s'.commit := by
      rw [happlied', take_of_prefix hupper (by rw [List.length_take]; omega), List.take_take,
        Nat.min_self]
    have hle : (c.state i).1.applied ≤ s'.applied := by
      have := hmoves.commit_le
      have := h.logged.applied i
      omega
    have hseg : (log ++ ext).take (c.state i).1.applied ++
        ((log ++ ext).take s'.applied).drop (c.state i).1.applied <+: log ++ ext := by
      have htake : ((log ++ ext).take s'.applied).take (c.state i).1.applied =
          (log ++ ext).take (c.state i).1.applied := by
        rw [List.take_take, Nat.min_eq_left hle]
      rw [← htake, List.take_append_drop]
      exact List.take_prefix _ _
    rw [hemits, ← htaken, h.logged.machine i,
      ← take_of_prefix (List.prefix_append log ext) (hbound i)] at hout
    exact hanswers'.replies i _ _ hseg out hout a ha
  · intro x hx
    have hnet : inflight (net ++ Effect.sends i effs) = inflight net := by
      rw [inflight_append, inflight_sends hserves, List.append_nil]
    have hx' : x ∈ inflight (net ++ Effect.sends i effs) := hx
    rw [hnet] at hx'
    exact hg.arrived (h.requests x ((hsub.filterMap _).subset hx'))
  · exact fun k entry hp => hg.arrived (hpresent k entry hp)

end OnceSim

section Theorem

variable (hup : config.votesForUpToDateOnly = true) (hown : config.commitsOwnTermOnly = true)

include hup hown

/-- The cluster with its history and the machine behind its memo refines `once` of the named
machine, its empty answers allowed at any time, in every environment. -/
theorem recording_refines_once (env : EnvModel (sig N (Named Cl C) (Option (Named Cl R)))) :
    (recording N config (machine.once Cl)).Refines env (onceService N Cl machine) := by
  refine System.Refines.of_handles ((committing_monotone hup hown).invariant env)
    (fun c t => ∃ log, OnceSim c t log)
    ⟨⟨machine.init, ∅, ∅, ∅⟩, rfl, [], SysState.init_induction (env := env)
      (P := fun c => OnceSim c ⟨machine.init, ∅, ∅, ∅⟩ []) .blank
      fun c i h => h.recover.loses (SysState.Loses.startActor c env i)⟩
    (fun c c' t ⟨log, h⟩ hl => ⟨log, h.loses hl⟩)
    (fun c t x _ ⟨log, h⟩ => ⟨{ t with arrived := insert x t.arrived }, .single rfl, log, h.input x⟩)
    ?_ ?_ (fun c t i _ ⟨log, h⟩ => ⟨t, .refl, log, h.recover⟩)
  · intro c t out _ ⟨log, h⟩ hmem
    refine ⟨t, .single ?_, log, h.output out⟩
    cases hres : out.res with
    | none => simp [Spec.lts, Spec.showing, hres]
    | some a => simpa [Spec.lts, Spec.showing, Service.once, hres] using h.outbox out hmem a hres
  · rintro c t net i m hc ⟨log, h⟩ hsub hpending
    obtain ⟨t', log', ht', h'⟩ := h.step hc.commits
      ((committing_monotone hup hown).step c i m hc hpending)
      (step_moves config Enum.all (machine.once Cl) i (c.state i).1 m)
      (step_serves config Enum.all (machine.once Cl) i (c.state i).1 m)
      (hc.replicating.timers.pending hpending) hsub fun req cmd hm => by
        obtain rfl := Option.some.inj hm
        rcases hpending with ⟨src, hmem⟩ | hmem
        · exact List.mem_filterMap.mpr ⟨_, hmem, rfl⟩
        · rcases hc.replicating.timers i _ hmem with h | h <;> cases h
    exact ⟨t', Spec.τSTr_showing ht', log', h'⟩

/-- The cluster with the machine behind its memo refines `once` of the named machine, its empty
answers allowed at any time, in every environment. -/
theorem cluster_refines_once (env : EnvModel (sig N (Named Cl C) (Option (Named Cl R)))) :
    (cluster N config (machine.once Cl)).Refines env (onceService N Cl machine) :=
  System.Refines.of_ghost (.past _) (recording_refines_once hup hown env)

/--
The cluster is the machine, once per command. A Raft cluster of any size, with the machine
behind its memo and its empty answers hidden, behaves to its clients as the one machine, each
command taking effect at most once, at one instant between its arrival and an answer, and each
answer named as its command. Nodes crash and restart, and every link, those from clients
included, loses, repeats and reorders messages: a command a client sends again, or a link hands
over twice, is the same command.
-/
theorem onceCluster_implements
    (env : EnvModel ((sig N (Named Cl C) (Option (Named Cl R))).withIO (Request N (Named Cl C))
      (Named Cl R))) :
    (onceCluster N Cl config machine).ImplementsOnce env (named N Cl machine) Request.key :=
  System.Refines.filterMapIO (cluster_refines_once hup hown env.under)

end Theorem

end RaftKV
