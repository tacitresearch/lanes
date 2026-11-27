/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.FairScheduler
public import Lanes.Runtime.KernelSound
public import Lanes.Semantics.Liveness

/-!
# Fair runs exist

A leads-to theorem is about fair runs. If a system had none, or none through some state it can
reach, the theorem would say nothing there. This file proves that fairness never rules out a
finite run: every finite run extends to a fair run (machine closure). It holds for every system
and every environment model, with no assumption; a signature may have infinitely many
identities.

The fair run is the one `FairScheduler` makes. It takes the given events, and from then on the
event that has been owed longest. Its queue holds every owed event (`FairScheduler.Complete`),
and an owed event that is not taken moves at least one place forward at each step, unless it is
a timer that the step arms again: that one goes to the back. So an obligation that stays due
and is not restarted is taken after at most as many steps as there were events ahead of it.
The run is fair and not impatient: a timer that keeps being armed again while it waits its turn
does not fire.

What makes this work without listing all actors is that an event changes the timers of one
actor at most (`SysState.step_of_ne_actor`): the newly owed events are found among the messages
in flight, the outbox and that actor's timers. The schedule is a computable function. Classical
reasoning is used in proofs only.

## Main definitions

- `System.Run.fairAfter`: the run that takes a list of events and then serves what is owed,
  the event owed longest first.

## Main statements

- `System.exists_fair_run_of_run`: machine closure. A finite run extends to a fair run.
- `System.Reachable.exists_fair_run`: every reachable state is on a fair run.
- `System.exists_fair_run`: every system has a fair run.
- `System.LeadsTo.reachable`: if `P` leads to `Q` and a state satisfying `P` is reachable, a
  state satisfying `Q` is reachable. A leads-to theorem is never true for lack of fair runs.
- `Obligation.due_iff_owed`: `Obligation.Due` is `SysState.owed`, which the scheduler computes.
-/

@[expose] public section

namespace Lanes

open Cslib

variable {σ : Signature} {sys : System σ} {env : EnvModel σ}

namespace SysState

variable {c c' : SysState sys} {ev : Event σ}

/-- An event changes whether an actor is up, and which of its timers are armed, only for the
actor that takes the step. -/
theorem step_of_ne_actor {i : σ.Id} (hstep : c.step env ev = some c') (hi : ev.actor? ≠ some i) :
    c'.up i = c.up i ∧ c'.timers i = c.timers i := by
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact ⟨rfl, rfl⟩
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := step_deliver.mp hstep
    have hne : i ≠ e.dst := by rintro rfl; exact hi rfl
    exact ⟨settle_up_of_ne _ hne, settle_timers_of_ne _ hne⟩
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := step_duplicate.mp hstep
    have hne : i ≠ e.dst := by rintro rfl; exact hi rfl
    exact ⟨settle_up_of_ne _ hne, settle_timers_of_ne _ hne⟩
  | drop e =>
    obtain ⟨_, _, rfl⟩ := step_drop.mp hstep
    exact ⟨rfl, rfl⟩
  | timeout j msg =>
    obtain ⟨_, _, rfl⟩ := step_timeout.mp hstep
    have hne : i ≠ j := by rintro rfl; exact hi rfl
    refine ⟨settle_up_of_ne _ hne, ?_⟩
    rw [handle, settle_timers_of_ne _ hne]
    exact update_of_ne _ _ hne
  | output out =>
    obtain ⟨_, rfl⟩ := step_output.mp hstep
    exact ⟨rfl, rfl⟩
  | crash j =>
    obtain ⟨_, _, rfl⟩ := step_crash.mp hstep
    have hne : i ≠ j := by rintro rfl; exact hi rfl
    simp [down, hne]
  | start j =>
    obtain ⟨_, _, rfl⟩ := step_start.mp hstep
    have hne : i ≠ j := by rintro rfl; exact hi rfl
    rw [startActor, settle_up_of_ne _ hne, settle_timers_of_ne _ hne]
    exact ⟨update_of_ne _ _ hne, rfl⟩

/-- An actor that is not started with the system has no timer armed when the system starts. -/
theorem init_timers_of_not_mem_boot {i : σ.Id} (hi : i ∉ sys.boot) :
    (init sys env).timers i = [] := by
  have hfold (boot : List σ.Id) (c : SysState sys) (hi : i ∉ boot) :
      (boot.foldl (fun c j => c.startActor env j) c).timers i = c.timers i := by
    induction boot generalizing c with
    | nil => rfl
    | cons j boot ih =>
      rw [List.foldl_cons, ih _ fun h => hi (List.mem_cons_of_mem _ h), startActor]
      exact settle_timers_of_ne _ fun h => hi (h ▸ List.mem_cons_self)
  exact hfold sys.boot (blank sys) hi

/-- An owed event is enabled. -/
theorem step_of_owed (howed : c.owed env ev = true) : ∃ c', c.step env ev = some c' := by
  cases ev with
  | deliver e =>
    simp only [owed, Bool.and_eq_true] at howed
    exact ⟨_, step_deliver.mpr ⟨howed.1, howed.2, rfl⟩⟩
  | timeout i msg =>
    simp only [owed, Bool.and_eq_true, List.contains_iff_mem] at howed
    exact ⟨_, step_timeout.mpr ⟨howed.1, howed.2, rfl⟩⟩
  | start i =>
    simp only [owed, Bool.and_eq_true, Bool.not_eq_true'] at howed
    exact ⟨_, step_start.mpr ⟨howed.1, .inl howed.2, rfl⟩⟩
  | output out =>
    simp only [owed, List.contains_iff_mem] at howed
    exact ⟨_, step_output.mpr ⟨howed, rfl⟩⟩
  | input _ | duplicate _ | drop _ | crash _ => simp [owed] at howed

/-- An owed event is listed by `maybeOwed`, if it is not a timer of an actor outside
`actors`. -/
theorem mem_maybeOwed {actors : List σ.Id} (howed : c.owed env ev = true)
    (hactor : ∀ i msg, ev = .timeout i msg → i ∈ actors) : ev ∈ c.maybeOwed actors := by
  unfold maybeOwed
  cases ev with
  | deliver e =>
    simp only [owed, Bool.and_eq_true] at howed
    simp [mem_of_deliverable howed.2]
  | timeout i msg =>
    simp only [owed, Bool.and_eq_true, List.contains_iff_mem] at howed
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨i, hactor i msg rfl, List.mem_map.mpr ⟨msg, howed.2, rfl⟩⟩)
  | start i =>
    simp only [owed, hasMail, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at howed
    obtain ⟨_, e, he, rfl⟩ := howed
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨e, he, rfl⟩)))
  | output out =>
    simp only [owed, List.contains_iff_mem] at howed
    simp [howed]
  | input _ | duplicate _ | drop _ | crash _ => simp [owed] at howed

end SysState

namespace Obligation

variable {c : SysState sys} {ob : Obligation σ}

/-- An obligation is due exactly when the scheduler counts its event as owed. -/
theorem due_iff_owed : ob.Due env c ↔ c.owed env ob.event = true := by
  cases ob <;> simp [Due, event, SysState.owed]

/-- Whether an obligation is due can be computed. -/
instance : Decidable (ob.Due env c) := decidable_of_iff _ due_iff_owed.symm

end Obligation

namespace FairScheduler

variable {c : SysState sys} {s : FairScheduler sys} {ev e p : Event σ}
  {actors : List σ.Id} {queue pre post : List (Event σ)}

/-- An owed event is in the new queue if it was in the old one or is listed by `maybeOwed`. -/
theorem mem_requeue (howed : c.owed env ev = true) (hmem : ev ∈ queue ∨ ev ∈ c.maybeOwed actors) :
    ev ∈ requeue env c actors queue := by
  by_cases hkept : ev ∈ queue.filter (c.owed env)
  · exact List.mem_append_left _ hkept
  · obtain hqueue | hmaybe := hmem
    · exact absurd (List.mem_filter.mpr ⟨hqueue, howed⟩) hkept
    · exact List.mem_append_right _ (List.mem_eraseDups.mpr (List.mem_filter.mpr
        ⟨hmaybe, by simp [howed, hkept]⟩))

/-- An event that is still owed keeps its place in the queue or moves forward. -/
theorem requeue_append_cons (howed : c.owed env e = true) :
    ∃ pre' post', requeue env c actors (pre ++ e :: post) = pre' ++ e :: post' ∧
      pre'.length ≤ pre.length := by
  have h : requeue env c actors (pre ++ e :: post) = pre.filter (c.owed env) ++
      e :: (post.filter (c.owed env) ++ ((c.maybeOwed actors).filter fun ev =>
        c.owed env ev && !((pre ++ e :: post).filter (c.owed env)).contains ev).eraseDups) := by
    simp only [requeue, List.filter_append, List.filter_cons_of_pos howed, List.append_assoc,
      List.cons_append]
  exact ⟨_, _, h, List.length_filter_le _ _⟩

/-- When an event ahead of `e` in the queue is taken, and `e` is still owed and not armed
again, `e` moves forward. -/
theorem take_queue {c' : SysState sys} (hqueue : s.queue = pre ++ e :: post) (hp : p ∈ pre)
    (hstep : s.state.step env p = some c') (howed : c'.owed env e = true)
    (hquiet : e ∉ s.state.arms p) :
    ∃ pre' post', (s.take env p).queue = pre' ++ e :: post' ∧ pre'.length < pre.length := by
  let waits (e : Event σ) : Bool := !(s.state.arms p).contains e
  obtain ⟨pre', post', hrequeue, hlen⟩ := requeue_append_cons (env := env)
    (actors := p.actor?.toList) (pre := (pre.erase p).filter waits)
    (post := post.filter waits ++ [p]) howed
  refine ⟨pre', post', ?_, ?_⟩
  · have hwaits : waits e = true := by simpa [waits] using hquiet
    simp only [take, hstep, hqueue, List.erase_append_left _ hp, List.filter_append,
      List.filter_cons_of_pos hwaits, List.append_assoc, List.cons_append, waits, hrequeue]
  · have := List.length_pos_of_mem hp
    have := List.length_filter_le waits (pre.erase p)
    rw [List.length_erase_of_mem hp] at this
    omega

/-- The queue misses no owed event. -/
def Complete (env : EnvModel σ) (s : FairScheduler sys) : Prop :=
  ∀ ev, s.state.owed env ev = true → ev ∈ s.queue

/-- The scheduler starts with every owed event in its queue. -/
theorem init_complete (sys : System σ) (env : EnvModel σ) : (init sys env).Complete env := by
  intro ev howed
  refine mem_requeue howed (.inr (SysState.mem_maybeOwed howed ?_))
  rintro i msg rfl
  by_contra hi
  have htimers : (init sys env).state.timers i = [] := SysState.init_timers_of_not_mem_boot hi
  simp [SysState.owed, htimers] at howed

/-- Taking an event, owed or not, leaves every owed event in the queue. -/
theorem Complete.take (hs : s.Complete env) (ev : Event σ) : (s.take env ev).Complete env := by
  unfold FairScheduler.take
  split
  · exact hs
  · next c hstep =>
    intro ev' howed
    refine mem_requeue howed ?_
    by_cases hactor : ∀ i msg, ev' = .timeout i msg → i ∈ ev.actor?.toList
    · exact .inr (SysState.mem_maybeOwed howed hactor)
    · simp only [not_forall] at hactor
      obtain ⟨i, msg, rfl, hi⟩ := hactor
      obtain ⟨hup, htimers⟩ := SysState.step_of_ne_actor hstep (i := i) (by simpa using hi)
      have hbefore : Event.timeout i msg ∈ s.queue :=
        hs _ (by simpa [SysState.owed, hup, htimers] using howed)
      have hwaits : Event.timeout i msg ∉ s.state.arms ev := by
        intro harms
        obtain ⟨_, _, htimeout, hactor⟩ := SysState.actor?_of_mem_arms harms
        cases htimeout
        simp [hactor] at hi
      by_cases heq : Event.timeout i msg = ev
      · exact .inl (by simp [heq])
      · exact .inl (List.mem_append_left _ (List.mem_filter.mpr
          ⟨(List.mem_erase_of_ne heq).mpr hbefore, by simpa using hwaits⟩))

end FairScheduler

namespace System

variable {evs : List (Event σ)} {c : SysState sys} {k : ℕ}

/-- The event tried at position `k` by the run that takes `evs` and then serves what is owed:
the next of `evs`, and once they are taken the event owed longest. -/
def fairChoice (env : EnvModel σ) (evs : List (Event σ)) (k : ℕ) (s : FairScheduler sys) :
    Option (Event σ) :=
  evs[k]?.or (s.next env)

/-- The scheduler at position `k` of the run that takes `evs` and then serves what is owed. -/
def fairSchedule (sys : System σ) (env : EnvModel σ) (evs : List (Event σ)) :
    ℕ → FairScheduler sys
  | 0 => .init sys env
  | k + 1 =>
    match fairChoice env evs k (fairSchedule sys env evs k) with
    | none => fairSchedule sys env evs k
    | some ev => (fairSchedule sys env evs k).take env ev

/-- The run that takes `evs`, as far as they are enabled, and then serves what is owed, the
event owed longest first. It stutters where nothing is owed. -/
def Run.fairAfter (sys : System σ) (env : EnvModel σ) (evs : List (Event σ)) : sys.Run env where
  state := ⟨fun k => (fairSchedule sys env evs k).state⟩
  event := ⟨fun k => (fairChoice env evs k (fairSchedule sys env evs k)).filter fun ev =>
    ((fairSchedule sys env evs k).state.step env ev).isSome⟩
  init := rfl
  exec k := by
    simp only [ωSequence.get_fun, fairSchedule]
    cases fairChoice env evs k (fairSchedule sys env evs k) with
    | none => rfl
    | some ev =>
      cases hstep : (fairSchedule sys env evs k).state.step env ev with
      | none => simp [FairScheduler.take, hstep, Spec.stutter, Option.filter]
      | some c' => simp [FairScheduler.take, hstep, Spec.stutter, System.sem, Option.filter]

/-- The scheduler has every owed event in its queue at every position. -/
theorem fairSchedule_complete (sys : System σ) (env : EnvModel σ) (evs : List (Event σ))
    (k : ℕ) : (fairSchedule sys env evs k).Complete env := by
  induction k with
  | zero => exact FairScheduler.init_complete sys env
  | succ k ih =>
    rw [fairSchedule]
    split
    · exact ih
    · exact ih.take _

/-- While it takes the events of a finite run, the scheduler is in the states of that run. -/
theorem fairSchedule_run (hrun : (SysState.init sys env).run env evs = some c)
    (hk : k ≤ evs.length) :
    (SysState.init sys env).run env (evs.take k) = some (fairSchedule sys env evs k).state := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < evs.length := by omega
    have htake : evs.take (k + 1) = evs.take k ++ [evs[k]] := by simp
    obtain ⟨c₁, h₁⟩ : ∃ c₁, (SysState.init sys env).run env (evs.take (k + 1)) = some c₁ := by
      rw [← List.take_append_drop (k + 1) evs, SysState.run_append] at hrun
      cases h : (SysState.init sys env).run env (evs.take (k + 1)) with
      | none => simp [h] at hrun
      | some c₁ => exact ⟨c₁, rfl⟩
    rw [h₁]
    rw [htake, SysState.run_append, ih (by omega)] at h₁
    have hstep : (fairSchedule sys env evs k).state.step env evs[k] = some c₁ := by
      simpa [SysState.run] using h₁
    simp [fairSchedule, fairChoice, hlt, FairScheduler.take, hstep]

/-- The run that extends a finite run reaches the state the finite run ends in. -/
theorem Run.fairAfter_state (hrun : (SysState.init sys env).run env evs = some c) :
    (Run.fairAfter sys env evs).state evs.length = c := by
  have h := fairSchedule_run hrun (Nat.le_refl _)
  rw [List.take_length, hrun] at h
  exact (Option.some.inj h).symm

/-- The run that extends a finite run starts with the events of the finite run. -/
theorem Run.fairAfter_event (hrun : (SysState.init sys env).run env evs = some c)
    (hk : k < evs.length) : (Run.fairAfter sys env evs).event k = some evs[k] := by
  have h := fairSchedule_run hrun (Nat.succ_le_of_lt hk)
  have htake : evs.take (k + 1) = evs.take k ++ [evs[k]] := by simp
  rw [htake, SysState.run_append, fairSchedule_run hrun (Nat.le_of_lt hk)] at h
  have hstep : ((fairSchedule sys env evs k).state.step env evs[k]).isSome = true := by
    cases hstep : (fairSchedule sys env evs k).state.step env evs[k] with
    | none => simp [SysState.run, hstep] at h
    | some c₁ => rfl
  simp [Run.fairAfter, fairChoice, hk, hstep]

/-- Once the given events are taken, an event that is in the queue, stays owed and is not
armed again is taken within as many steps as there are events ahead of it: at each step it is
taken or moves forward. -/
theorem Run.fairAfter_taken {e : Event σ} {m : ℕ} {pre post : List (Event σ)}
    (hm : evs.length ≤ m) (hqueue : (fairSchedule sys env evs m).queue = pre ++ e :: post)
    (howed : ∀ k, m ≤ k → (fairSchedule sys env evs k).state.owed env e = true)
    (hquiet : ∀ k p, m ≤ k → (Run.fairAfter sys env evs).event k = some p →
      e ∉ (fairSchedule sys env evs k).state.arms p) :
    ∃ k, m ≤ k ∧ k ≤ m + pre.length ∧ (Run.fairAfter sys env evs).event k = some e := by
  induction hlen : pre.length using Nat.strong_induction_on generalizing m pre post with
  | _ len ih =>
    have hchoice : fairChoice env evs m (fairSchedule sys env evs m)
        = (pre.find? ((fairSchedule sys env evs m).state.owed env)).or (some e) := by
      simp [fairChoice, hm, FairScheduler.next, hqueue, List.find?_append, howed m (Nat.le_refl m)]
    cases hfind : pre.find? ((fairSchedule sys env evs m).state.owed env) with
    | none =>
      obtain ⟨c', hstep⟩ := SysState.step_of_owed (howed m (Nat.le_refl m))
      exact ⟨m, Nat.le_refl m, by omega, by simp [Run.fairAfter, hchoice, hfind, hstep]⟩
    | some p =>
      obtain ⟨c', hstep⟩ := SysState.step_of_owed (List.find?_some hfind)
      have hnext : fairSchedule sys env evs (m + 1) = (fairSchedule sys env evs m).take env p := by
        simp [fairSchedule, hchoice, hfind]
      have hstate : (fairSchedule sys env evs (m + 1)).state = c' := by
        simp [hnext, FairScheduler.take, hstep]
      have htaken : (Run.fairAfter sys env evs).event m = some p := by
        simp [Run.fairAfter, hchoice, hfind, hstep]
      obtain ⟨pre', post', hqueue', hlt⟩ := FairScheduler.take_queue hqueue
        (List.mem_of_find?_eq_some hfind) hstep (hstate ▸ howed (m + 1) (by omega))
        (hquiet m p (Nat.le_refl m) htaken)
      obtain ⟨k, hk, hbound, hev⟩ := ih pre'.length (by omega) (by omega : evs.length ≤ m + 1)
        (hnext ▸ hqueue') (fun k hk => howed k (by omega))
        (fun k p hk => hquiet k p (by omega)) rfl
      exact ⟨k, by omega, by omega, hev⟩

/-- The run that takes `evs` and then serves what is owed, the event owed longest first, is
fair. -/
theorem Run.fairAfter_fair (sys : System σ) (env : EnvModel σ) (evs : List (Event σ)) :
    (Run.fairAfter sys env evs).Fair := by
  refine Run.fair_iff.mpr fun ob n hdue => ?_
  have howed (k : ℕ) (hk : max n evs.length ≤ k) :
      (fairSchedule sys env evs k).state.owed env ob.event = true :=
    Obligation.due_iff_owed.mp (hdue k (by omega)).1
  have hquiet (k : ℕ) (p : Event σ) (hk : max n evs.length ≤ k)
      (hev : (Run.fairAfter sys env evs).event k = some p) :
      ob.event ∉ (fairSchedule sys env evs k).state.arms p :=
    fun harms => (hdue k (by omega)).2 ⟨p, hev, Obligation.restarted_iff_mem_arms.mpr harms⟩
  obtain ⟨pre, post, hqueue⟩ := List.append_of_mem
    (fairSchedule_complete sys env evs _ _ (howed _ (Nat.le_refl _)))
  obtain ⟨k, hk, _, hev⟩ := Run.fairAfter_taken (by omega) hqueue howed hquiet
  exact ⟨k, by omega, hev⟩

/-- Machine closure: every finite run extends to a fair run. So fairness rules out no finite
behaviour, and a property of all fair runs is never true for lack of them. -/
theorem exists_fair_run_of_run (hrun : (SysState.init sys env).run env evs = some c) :
    ∃ r : sys.Run env, r.Fair ∧ r.event.take evs.length = evs.map some ∧
      r.state evs.length = c := by
  refine ⟨.fairAfter sys env evs, Run.fairAfter_fair sys env evs, ?_, Run.fairAfter_state hrun⟩
  refine List.ext_getElem (by simp [ωSequence.length_take]) fun k hk _ => ?_
  rw [ωSequence.take_get, List.getElem_map]
  exact Run.fairAfter_event hrun (by simpa [ωSequence.length_take] using hk)

/-- A reachable state is the end of a finite run. -/
theorem Reachable.exists_run (hc : sys.Reachable env c) :
    ∃ evs, (SysState.init sys env).run env evs = some c := by
  induction hc with
  | init => exact ⟨[], rfl⟩
  | step ev _ hstep ih =>
    obtain ⟨evs, hrun⟩ := ih
    exact ⟨evs ++ [ev], by simp [SysState.run_append, hrun, SysState.run, hstep]⟩

/-- Every reachable state is on a fair run. -/
theorem Reachable.exists_fair_run (hc : sys.Reachable env c) :
    ∃ r : sys.Run env, r.Fair ∧ ∃ n, r.state n = c := by
  obtain ⟨evs, hrun⟩ := hc.exists_run
  obtain ⟨r, hfair, _, hstate⟩ := exists_fair_run_of_run hrun
  exact ⟨r, hfair, evs.length, hstate⟩

/-- Every system has a fair run, under every environment model. -/
theorem exists_fair_run (sys : System σ) (env : EnvModel σ) : ∃ r : sys.Run env, r.Fair :=
  ⟨.fairAfter sys env [], Run.fairAfter_fair sys env []⟩

/-- If `P` leads to `Q` and a state satisfying `P` is reachable, then a state satisfying `Q` is
reachable: a leads-to theorem is not true for lack of fair runs. -/
theorem LeadsTo.reachable {P Q : SysState sys → Prop} (h : sys.LeadsTo env P Q)
    (hc : sys.Reachable env c) (hP : P c) : ∃ c', sys.Reachable env c' ∧ Q c' := by
  obtain ⟨r, hfair, n, rfl⟩ := hc.exists_fair_run
  obtain ⟨m, _, hQ⟩ := h r hfair n hP
  exact ⟨r.state m, r.reachable m, hQ⟩

end System

end Lanes
