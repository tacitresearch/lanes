/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Jobs
public import Lanes.Actors.Deed
public import Lanes.Actors.JoinSound
public import Lanes.Actors.Lift
public import Lanes.Actors.Run

/-!
What the jobs actor does, in every environment: it keeps no more jobs active than its slots
(`Jobs.within`), keeps the timer of every active job armed while it is up (`Jobs.armed`), and
answers no key more often than it handles a submission of it (`Jobs.answered_le_handled`). A
retry carries the key and the work of the attempt before it (`Jobs.retry_same`, in
`Lanes.Behaviours.Jobs`).

The steps are taken apart first: what a step does to the timers, to the entry of one key, and
to what the actor owes a key. `Lanes.Semantics.JobsLive` builds the liveness proof on them.
-/

@[expose] public section

namespace Lanes.Jobs

/-! ### Timers -/

section Timer

variable {K J R : Type} {a : Active K J} {key : K}

theorem timer_eq_expire : timer (R := R) a = .expire key ↔ a.key = key ∧ a.phase = .running := by
  unfold timer
  split <;> simp_all

theorem timer_eq_retry : timer (R := R) a = .retry key ↔ a.key = key ∧ a.phase = .backoff := by
  unfold timer
  split <;> simp_all

@[simp] theorem timer_ne_submit (job : J) : timer (R := R) a ≠ .submit key job := by
  unfold timer
  split <;> simp

@[simp] theorem timer_ne_result (attempt : Nat) (r : R) : timer a ≠ .result key attempt r := by
  unfold timer
  split <;> simp

theorem timer_ne_of_key (h : a.key ≠ key) :
    timer (R := R) a ≠ .expire key ∧ timer (R := R) a ≠ .retry key :=
  ⟨fun he => h (timer_eq_expire.mp he).1, fun he => h (timer_eq_retry.mp he).1⟩

theorem timer_eq_of_phase {a' : Active K J} (hkey : a'.key = a.key) (hphase : a'.phase = a.phase) :
    timer (R := R) a' = timer a := by
  unfold timer
  rw [hphase, hkey]

end Timer

variable {K J R : Type} [DecidableEq K] [DecidableEq J] [DecidableEq R] {config : Config R}

theorem step_runs (config : Config R) (active : List (Active K J)) (msg : Jobs.Msg K J R) :
    (step config active msg).2.any Effect.isStop = false := by
  cases msg <;> simp only [step, fail] <;> repeat' split
  all_goals simp [Effect.isStop]

theorem recover_runs (config : Config R) (active : List (Active K J)) :
    ((actor config).recover active).2.any Effect.isStop = false := by
  simp only [actor, List.any_map, List.any_eq_false, Function.comp_def, rearm]
  intro a _
  split <;> simp [Effect.isStop]

/-- What a failed attempt leaves armed: the backoff of the job that failed, and the timer of
every other job, when the effects before it cancel only the job's deadline. -/
theorem armed_fail (config : Config R) {active : List (Active K J)} {timers : List (Jobs.Msg K J R)}
    {a : Active K J} (outcome : Outcome R) {first : List (Eff K J R)}
    (hfirst : ∀ m, (.cancel m : Eff K J R) ∈ first → m = .expire a.key)
    (h : ∀ b ∈ active, b.key ≠ a.key → timer b ∈ timers) :
    ∀ b ∈ (fail config active a outcome first).1,
      timer b ∈ Effect.retime (fail config active a outcome first).2 timers := by
  have hother {effs : List (Eff K J R)} (heffs : ∀ m, (.cancel m : Eff K J R) ∈ effs →
      m = .expire a.key) {b : Active K J} (hb : b ∈ active) (hne : b.key ≠ a.key) :
      timer b ∈ Effect.retime effs timers :=
    Effect.mem_retime_of_mem (h b hb hne) fun hc =>
      (timer_ne_of_key hne).1 (heffs _ hc)
  unfold fail
  split
  · intro b hb
    rcases mem_put hb with rfl | ⟨hb, hne⟩
    · refine Effect.mem_retime_of_after (delay_ms := config.backoff a.attempt)
        (by simp [timer]) ?_
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      intro hc
      have := hfirst _ hc
      simp [timer] at this
    · exact hother (by simpa using hfirst) hb hne
  · intro b hb
    obtain ⟨hb, hne⟩ := mem_remove.mp hb
    exact hother (by simpa using hfirst) hb hne

/-- After a step, the timer of every active job is armed, if before it the timer of every
active job was, but perhaps the one the step handles. -/
theorem armed_step (config : Config R) {active : List (Active K J)}
    {timers : List (Jobs.Msg K J R)} (msg : Jobs.Msg K J R) (hnodup : (keys active).Nodup)
    (h : ∀ a ∈ active, timer a ≠ msg → timer a ∈ timers) :
    ∀ a ∈ (step config active msg).1, timer a ∈ Effect.retime (step config active msg).2 timers := by
  have hother {key : K} (hk : ∀ b ∈ active, b.key ≠ key → timer b ≠ msg) {b : Active K J}
      (hb : b ∈ active) (hne : b.key ≠ key) : timer b ∈ timers := h b hb (hk b hb hne)
  have hsame {key : K} {a : Active K J} (ha : entry active key = some a) {b : Active K J}
      (hb : b ∈ active) (hkey : b.key = key) : b = a := by
    have := entry_of_mem hnodup hb
    rw [hkey, ha] at this
    exact (Option.some.inj this).symm
  cases msg with
  | submit key job =>
    simp only [step]
    split
    · exact fun b hb => h b hb (by simp)
    · split
      · exact fun b hb => h b hb (by simp)
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Effect.mem_retime_of_after (delay_ms := config.attempt_ms) (by simp [timer])
            (by simp)
        · exact Effect.mem_retime_of_mem (h b hb (by simp)) (by simp)
  | result key attempt r =>
    simp only [step]
    split
    · next a ha =>
      obtain ⟨-, rfl⟩ := entry_some ha
      split
      · split
        · exact armed_fail config _ (by simp) fun b hb _ => h b hb (by simp)
        · intro b hb
          obtain ⟨hb, hne⟩ := mem_remove.mp hb
          refine Effect.mem_retime_of_mem (h b hb (by simp)) ?_
          simp [(timer_ne_of_key hne).1]
      · exact fun b hb => h b hb (by simp)
    · exact fun b hb => h b hb (by simp)
  | expire key =>
    simp only [step]
    split
    · next a ha =>
      obtain ⟨-, rfl⟩ := entry_some ha
      split
      · exact armed_fail config _ (by simp) fun b hb hne =>
          hother (fun b _ hne => (timer_ne_of_key hne).1) hb hne
      · next hphase =>
        intro b hb
        by_cases hkey : b.key = a.key
        · obtain rfl := hsame ha hb hkey
          exact h b hb fun he => hphase (timer_eq_expire.mp he).2
        · exact hother (fun b _ hne => (timer_ne_of_key hne).1) hb hkey
    · next ha =>
      intro b hb
      have hne : b.key ≠ key := fun he =>
        entry_eq_none.mp ha (mem_keys.mpr ⟨b, hb, he⟩)
      exact hother (fun b _ hne => (timer_ne_of_key hne).1) hb hne
  | retry key =>
    simp only [step]
    split
    · next a ha =>
      obtain ⟨hmem, rfl⟩ := entry_some ha
      split
      · intro b hb
        rcases mem_put hb with rfl | ⟨hb, hne⟩
        · exact Effect.mem_retime_of_after (delay_ms := config.attempt_ms) (by simp [timer])
            (by simp)
        · exact Effect.mem_retime_of_mem
            (hother (fun b _ hne => (timer_ne_of_key hne).2) hb hne) (by simp)
      · next hphase =>
        intro b hb
        by_cases hkey : b.key = a.key
        · obtain rfl := hsame ha hb hkey
          exact h b hb fun he => hphase (timer_eq_retry.mp he).2
        · exact hother (fun b _ hne => (timer_ne_of_key hne).2) hb hkey
    · next ha =>
      intro b hb
      have hne : b.key ≠ key := fun he =>
        entry_eq_none.mp ha (mem_keys.mpr ⟨b, hb, he⟩)
      exact hother (fun b _ hne => (timer_ne_of_key hne).2) hb hne

end Lanes.Jobs

namespace Lanes.Jobs

variable {K J R : Type} [DecidableEq K] [DecidableEq J] [DecidableEq R] {config : Config R}

/-! ### The entry of one key -/

/-- How far an active job is from its answer: two for each attempt left, and one more while an
attempt is made. Every step that changes the job brings it nearer, or answers it. -/
def left (config : Config R) (a : Active K J) : Nat :=
  2 * (config.cap - a.attempt) + match a.phase with
    | .running => 1
    | .backoff => 0

/-- The entry of a key after a step is gone or nearer its answer than `a`. -/
def Moved (config : Config R) (a : Active K J) (e : Option (Active K J)) : Prop :=
  e = none ∨ ∃ a', e = some a' ∧ left config a' < left config a

theorem moved_fail (config : Config R) {active : List (Active K J)} {a : Active K J}
    (outcome : Outcome R) (first : List (Eff K J R)) (ha : a ∈ active)
    (hrunning : a.phase = .running) :
    Moved config a (entry (fail config active a outcome first).1 a.key) := by
  unfold fail
  split
  · refine .inr ⟨_, entry_put_self (mem_keys.mpr ⟨a, ha, rfl⟩), ?_⟩
    simp [left, hrunning]
  · exact .inl (entry_remove_self ..)

theorem entry_fail_of_ne (config : Config R) {active : List (Active K J)} {a : Active K J}
    (outcome : Outcome R) (first : List (Eff K J R)) {key : K} (h : key ≠ a.key) :
    entry (fail config active a outcome first).1 key = entry active key := by
  unfold fail
  split
  · exact entry_put_of_ne h
  · exact entry_remove_of_ne _ h

/-- A step leaves the entry of `key` as it was, or moves it nearer its answer. -/
theorem entry_step (config : Config R) {active : List (Active K J)} (hatt : Attempts config active)
    {key : K} {a : Active K J} (ha : entry active key = some a) (msg : Jobs.Msg K J R) :
    entry (step config active msg).1 key = some a ∨
      Moved config a (entry (step config active msg).1 key) := by
  obtain ⟨hmem, rfl⟩ := entry_some ha
  cases msg with
  | submit key' job =>
    simp only [step]
    split
    · exact .inl ha
    · next hnew =>
      split
      · exact .inl ha
      · have hne : a.key ≠ key' := fun he => hnew (he ▸ mem_keys.mpr ⟨a, hmem, rfl⟩)
        exact .inl ((entry_cons_of_ne _ _ (Ne.symm hne)).trans ha)
  | result key' attempt r =>
    simp only [step]
    split
    · next a' ha' =>
      obtain ⟨hmem', rfl⟩ := entry_some ha'
      split
      · next hmatch =>
        by_cases hkey : a.key = a'.key
        · obtain rfl : a = a' := Option.some.inj (ha.symm.trans (hkey ▸ ha'))
          split
          · exact .inr (moved_fail config _ _ hmem hmatch.1)
          · exact .inr (.inl (entry_remove_self ..))
        · split
          · exact .inl ((entry_fail_of_ne config _ _ hkey).trans ha)
          · exact .inl ((entry_remove_of_ne _ hkey).trans ha)
      · exact .inl ha
    · exact .inl ha
  | expire key' =>
    simp only [step]
    split
    · next a' ha' =>
      obtain ⟨hmem', rfl⟩ := entry_some ha'
      split
      · next hrunning =>
        by_cases hkey : a.key = a'.key
        · obtain rfl : a = a' := Option.some.inj (ha.symm.trans (hkey ▸ ha'))
          exact .inr (moved_fail config _ _ hmem hrunning)
        · exact .inl ((entry_fail_of_ne config _ _ hkey).trans ha)
      · exact .inl ha
    · exact .inl ha
  | retry key' =>
    simp only [step]
    split
    · next a' ha' =>
      obtain ⟨hmem', rfl⟩ := entry_some ha'
      split
      · next hback =>
        by_cases hkey : a.key = a'.key
        · obtain rfl : a = a' := Option.some.inj (ha.symm.trans (hkey ▸ ha'))
          refine .inr (.inr ⟨_, entry_put_self (mem_keys.mpr ⟨a, hmem, rfl⟩), ?_⟩)
          have hlt := (hatt a hmem).2.2 hback
          simp only [left, hback]
          omega
        · exact .inl ((entry_put_of_ne
            (a := { a' with attempt := a'.attempt + 1, phase := .running }) hkey).trans ha)
      · exact .inl ha
    · exact .inl ha

/-- Handling the timer an active job waits on moves it nearer its answer. -/
theorem entry_step_timer (config : Config R) {active : List (Active K J)}
    (hatt : Attempts config active) {key : K} {a : Active K J} (ha : entry active key = some a) :
    Moved config a (entry (step config active (timer a)).1 key) := by
  obtain ⟨hmem, rfl⟩ := entry_some ha
  unfold timer
  split
  · next hrunning =>
    simp only [step, ha, hrunning, ↓reduceIte]
    exact moved_fail config _ _ hmem hrunning
  · next hback =>
    simp only [step, ha, hback, ↓reduceIte]
    refine .inr ⟨_, entry_put_self (mem_keys.mpr ⟨a, hmem, rfl⟩), ?_⟩
    have hlt := (hatt a hmem).2.2 hback
    simp only [left, hback]
    omega

/-- No step arms again the timer an active job waits on: a job's deadline is armed only by the
step that admits it or ends its backoff, its backoff only by the step that ends an attempt. -/
theorem not_arms (config : Config R) {active : List (Active K J)} {a : Active K J}
    (ha : entry active a.key = some a) (msg : Jobs.Msg K J R) (delay_ms : Nat) :
    (.after delay_ms (timer a) : Eff K J R) ∉ (step config active msg).2 := by
  have hfail {a' : Active K J} (ha' : entry active a'.key = some a')
      (hrunning : a'.phase = .running) (outcome : Outcome R) {first : List (Eff K J R)}
      (hfirst : ∀ d m, (.after d m : Eff K J R) ∉ first) :
      (.after delay_ms (timer a) : Eff K J R) ∉ (fail config active a' outcome first).2 := by
    unfold fail
    split
    · simp only [List.mem_append, List.mem_singleton, Effect.after.injEq, not_or]
      refine ⟨hfirst _ _, fun ⟨_, he⟩ => ?_⟩
      obtain ⟨hkey, hback⟩ := timer_eq_retry.mp he
      rw [hkey, ha'] at ha
      obtain rfl := Option.some.inj ha
      simp [hrunning] at hback
    · simp [hfirst]
  cases msg with
  | submit key job =>
    simp only [step]
    split
    · simp
    · next hnew =>
      split
      · simp
      · simp only [List.mem_cons, Effect.after.injEq, reduceCtorEq, List.not_mem_nil, or_false,
          false_or, not_and]
        intro _ he
        exact hnew ((timer_eq_expire.mp he).1 ▸ mem_keys.mpr ⟨a, (entry_some ha).1, rfl⟩)
  | result key attempt r =>
    simp only [step]
    split
    · next a' ha' =>
      obtain ⟨-, rfl⟩ := entry_some ha'
      split
      · next hmatch =>
        split
        · exact hfail ha' hmatch.1 _ (by simp)
        · simp
      · simp
    · simp
  | expire key =>
    simp only [step]
    split
    · next a' ha' =>
      obtain ⟨-, rfl⟩ := entry_some ha'
      split
      · next hrunning => exact hfail ha' hrunning _ (by simp)
      · simp
    · simp
  | retry key =>
    simp only [step]
    split
    · next a' ha' =>
      obtain ⟨-, rfl⟩ := entry_some ha'
      split
      · next hback =>
        simp only [List.mem_cons, Effect.after.injEq, reduceCtorEq, List.not_mem_nil, or_false,
          false_or, not_and]
        intro _ he
        obtain ⟨hkey, hrunning⟩ := timer_eq_expire.mp he
        rw [hkey, ha'] at ha
        obtain rfl := Option.some.inj ha
        simp [hrunning] at hback
      · simp
    · simp

/-- A job leaves only in a step that answers it. -/
theorem answer_of_leaves (config : Config R) {active : List (Active K J)} {key : K}
    {a : Active K J} (ha : entry active key = some a) {msg : Jobs.Msg K J R}
    (hgone : entry (step config active msg).1 key = none) :
    ∃ outcome, (.emit (.answer key outcome) : Eff K J R) ∈ (step config active msg).2 := by
  obtain ⟨hmem, rfl⟩ := entry_some ha
  have hkeep {e : Option (Active K J)} (he : e = some a) : e ≠ none := by
    rw [he]
    exact Option.some_ne_none a
  have hfail {a' : Active K J} (outcome : Outcome R) {first : List (Eff K J R)}
      (hgone : entry (fail config active a' outcome first).1 a.key = none) :
      (.emit (.answer a.key outcome) : Eff K J R) ∈ (fail config active a' outcome first).2 := by
    unfold fail at hgone ⊢
    by_cases hlt : a'.attempt < config.cap
    · simp only [hlt, ↓reduceIte] at hgone
      by_cases hkey : a.key = a'.key
      · rw [hkey] at hgone ⊢
        refine absurd hgone (Option.ne_none_iff_exists'.mpr ⟨_, entry_put_self ?_⟩)
        exact hkey ▸ mem_keys.mpr ⟨a, hmem, rfl⟩
      · exact absurd ((entry_put_of_ne (a := { a' with phase := .backoff }) hkey).symm.trans hgone)
          (hkeep ha)
    · simp only [hlt, ↓reduceIte] at hgone ⊢
      by_cases hkey : a.key = a'.key
      · simp [hkey]
      · exact absurd ((entry_remove_of_ne _ hkey).symm.trans hgone) (hkeep ha)
  cases msg with
  | submit key' job =>
    simp only [step] at hgone ⊢
    split
    · next hin =>
      simp only [hin, ↓reduceIte] at hgone
      exact absurd hgone (hkeep ha)
    · next hnew =>
      simp only [hnew, ↓reduceIte] at hgone
      split
      · next hfull =>
        simp only [hfull, ↓reduceIte] at hgone
        exact absurd hgone (hkeep ha)
      · next hroom =>
        simp only [hroom, ↓reduceIte] at hgone
        have hne : a.key ≠ key' := fun he => hnew (he ▸ mem_keys.mpr ⟨a, hmem, rfl⟩)
        exact absurd hgone (hkeep ((entry_cons_of_ne _ _ (Ne.symm hne)).trans ha))
  | result key' attempt r =>
    simp only [step] at hgone ⊢
    split
    · next a' ha' =>
      simp only [ha'] at hgone
      obtain ⟨-, rfl⟩ := entry_some ha'
      split
      · next hmatch =>
        simp only [hmatch, and_self, ↓reduceIte] at hgone
        split
        · next hretry =>
          simp only [hretry, ↓reduceIte] at hgone
          exact ⟨_, hfail _ hgone⟩
        · next hretry =>
          simp only [hretry, Bool.false_eq_true, ↓reduceIte] at hgone
          by_cases hkey : a.key = a'.key
          · exact ⟨.done r, by simp [hkey]⟩
          · exact absurd ((entry_remove_of_ne _ hkey).symm.trans hgone) (hkeep ha)
      · next hmatch =>
        simp only [hmatch, ↓reduceIte] at hgone
        exact absurd hgone (hkeep ha)
    · next hnone =>
      simp only [hnone] at hgone
      exact absurd hgone (hkeep ha)
  | expire key' =>
    simp only [step] at hgone ⊢
    split
    · next a' ha' =>
      simp only [ha'] at hgone
      split
      · next hrunning =>
        simp only [hrunning, ↓reduceIte] at hgone
        exact ⟨_, hfail _ hgone⟩
      · next hrunning =>
        simp only [hrunning, ↓reduceIte] at hgone
        exact absurd hgone (hkeep ha)
    · next hnone =>
      simp only [hnone] at hgone
      exact absurd hgone (hkeep ha)
  | retry key' =>
    simp only [step] at hgone ⊢
    split
    · next a' ha' =>
      simp only [ha'] at hgone
      obtain ⟨hmem', rfl⟩ := entry_some ha'
      split
      · next hback =>
        simp only [hback, ↓reduceIte] at hgone
        by_cases hkey : a.key = a'.key
        · rw [hkey] at hgone
          exact absurd hgone (Option.ne_none_iff_exists'.mpr
            ⟨_, entry_put_self (mem_keys.mpr ⟨a', hmem', rfl⟩)⟩)
        · exact absurd ((entry_put_of_ne
            (a := { a' with attempt := a'.attempt + 1, phase := .running }) hkey).symm.trans
            hgone) (hkeep ha)
      · next hback =>
        simp only [hback, ↓reduceIte] at hgone
        exact absurd hgone (hkeep ha)
    · next hnone =>
      simp only [hnone] at hgone
      exact absurd hgone (hkeep ha)

/-- A submission leaves its key active, or answers it at once. -/
theorem submit_step (config : Config R) (active : List (Active K J)) (key : K) (job : J) :
    key ∈ keys (step config active (.submit key job)).1 ∨
      ∃ outcome, (.emit (.answer key outcome) : Eff K J R) ∈
        (step config active (.submit key job)).2 := by
  simp only [step]
  split
  · exact .inl ‹_›
  · split
    · exact .inr ⟨_, List.mem_singleton_self _⟩
    · exact .inl (List.mem_cons_self ..)

end Lanes.Jobs

/-! ### The jobs actor as a system -/

namespace Lanes.Jobs

variable {K J R : Type} [DecidableEq K] [DecidableEq J] [DecidableEq R] {config : Config R}
  {env : EnvModel (sig K J R)}

/-- While the jobs actor is up, the timer each active job waits on is armed. -/
def Armed (c : SysState (system (K := K) (J := J) config)) : Prop :=
  c.up () = true → ∀ a ∈ (c.state () : List (Active K J)), timer a ∈ c.timers ()

/-- No more jobs are active than there are slots, in every environment. -/
theorem within (config : Config R) (env : EnvModel (sig K J R)) :
    (system (K := K) (J := J) config).Invariant env fun c => Within config (c.state ()) :=
  System.invariant_of_actor _ () (actor_within config) env

theorem attempts (config : Config R) (env : EnvModel (sig K J R)) :
    (system (K := K) (J := J) config).Invariant env fun c => Attempts config (c.state ()) :=
  System.invariant_of_actor _ () (actor_attempts config) env

theorem handle_eq (c : SysState (system (K := K) (J := J) config)) (msg : Jobs.Msg K J R) :
    c.handle env () msg = { c with
      state := update c.state () (step config (c.state ()) msg).1
      net := c.net ++ Effect.sends () (step config (c.state ()) msg).2
      timers := update c.timers () (Effect.retime (step config (c.state ()) msg).2 (c.timers ()))
      outbox := c.outbox ++ Effect.emits (step config (c.state ()) msg).2 } := by
  have hr : ((actor config).step (c.state ()) msg).2.any Effect.isStop = false :=
    step_runs config (c.state ()) msg
  simp only [SysState.handle, SysState.settle_eq, hr, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem startActor_eq (c : SysState (system (K := K) (J := J) config)) :
    c.startActor env () = { c with
      up := update c.up () true
      net := c.net ++ Effect.sends () ((c.state ()).map (rearm config))
      timers := update c.timers () (Effect.retime ((c.state ()).map (rearm config)) (c.timers ()))
      outbox := c.outbox ++ Effect.emits ((c.state ()).map (rearm config)) } := by
  have hr := recover_runs (K := K) (J := J) config (c.state ())
  simp only [SysState.startActor, SysState.settle_eq, hr, Bool.false_eq_true, ↓reduceIte]
  simp only [actor, SysState.mk.injEq, and_true]
  funext i
  simp

private theorem armed_handle {c : SysState (system (K := K) (J := J) config)}
    (msg : Jobs.Msg K J R) (hnodup : (keys (c.state ())).Nodup)
    (h : ∀ a ∈ (c.state () : List (Active K J)), timer a ≠ msg → timer a ∈ c.timers ()) :
    Armed (c.handle env () msg) := by
  intro _ a ha
  rw [handle_eq] at ha ⊢
  simp only [update_self] at ha ⊢
  exact armed_step config msg hnodup h a ha

private theorem armed_start (c : SysState (system (K := K) (J := J) config)) :
    Armed (c.startActor env ()) := by
  intro _ a ha
  rw [startActor_eq] at ha ⊢
  simp only [update_self] at ha ⊢
  have hafter : rearm config a = .after (match a.phase with
      | .running => config.attempt_ms
      | .backoff => config.backoff a.attempt) (timer a) := by
    unfold rearm timer
    cases a.phase <;> rfl
  refine Effect.mem_retime_of_after (List.mem_map.mpr ⟨a, ha, hafter⟩) ?_
  intro hc
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hc
  unfold rearm at hb
  split at hb <;> cases hb

/-- The jobs actor cannot forget an active job, in any environment: while it is up, the timer
the job waits on is armed. -/
theorem armed (config : Config R) (env : EnvModel (sig K J R)) :
    (system (K := K) (J := J) config).Invariant env Armed := by
  intro c hc
  induction hc with
  | init => exact armed_start (env := env) (SysState.blank _)
  | @step c c' ev hc hstep ih =>
    have hnodup : (keys (c.state ())).Nodup := (within config env c hc).2
    cases ev with
    | input x =>
      obtain rfl := SysState.step_input.mp hstep
      exact ih
    | deliver e =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_deliver.mp hstep
      exact armed_handle (c := { c with net := c.net.erase e }) e.msg hnodup
        fun a ha _ => ih hup a ha
    | duplicate e =>
      obtain ⟨hup, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
      exact armed_handle e.msg hnodup fun a ha _ => ih hup a ha
    | drop e =>
      obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
      exact ih
    | timeout i msg =>
      obtain ⟨hup, _, rfl⟩ := SysState.step_timeout.mp hstep
      refine armed_handle msg hnodup fun a ha hne => ?_
      simpa using (List.mem_erase_of_ne hne).mpr (ih hup a ha)
    | output out =>
      obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
      exact ih
    | crash i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
      simp [Armed, SysState.down]
    | start i =>
      obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
      exact armed_start c

/-! ### No key is answered more often than it is submitted -/

/-- The keys answered, as often as they were. -/
def answered (shown : List (Deed (sig K J R))) : List K :=
  shown.filterMap fun
    | .output (.answer key _) => some key
    | _ => none

/-- The submissions the jobs actor handled, by key, as often as it handled them. -/
def handled (shown : List (Deed (sig K J R))) : List K :=
  shown.filterMap fun
    | .handle _ (.submit key _) => some key
    | _ => none

private def answers (key : K) : Output K J R → Bool
  | .answer key' _ => key' == key
  | .dispatch .. => false

private def submits (key : K) : Jobs.Msg K J R → Bool
  | .submit key' _ => key' == key
  | _ => false

/-- What the jobs actor owes `key`: the answers waiting to leave and its entry. -/
private def owed (key : K) (c : SysState (system (K := K) (J := J) config)) : Nat :=
  c.outbox.countP (answers key) + (keys (c.state ())).count key

omit [DecidableEq J] in
private theorem count_remove_le (active : List (Active K J)) (key key' : K) :
    (keys (remove active key')).count key ≤ (keys active).count key := by
  rw [keys_remove]
  exact (List.filter_sublist).count_le _

omit [DecidableEq J] in
private theorem count_remove_self (active : List (Active K J)) (key : K) :
    (keys (remove active key)).count key = 0 := by
  rw [keys_remove]
  exact List.count_eq_zero.mpr (by simp)

omit [DecidableEq J] in
private theorem one_le_count {active : List (Active K J)} {key : K} {a : Active K J}
    (ha : entry active key = some a) : 1 ≤ (keys active).count key :=
  List.count_pos_iff.mpr (mem_keys.mpr ⟨a, entry_some ha |>.1, entry_some ha |>.2⟩)

private theorem owed_fail (key : K) {active : List (Active K J)} {a : Active K J}
    (outcome : Outcome R) (first : List (Eff K J R))
    (hfirst : (Effect.emits first).countP (answers key) = 0) (ha : a ∈ active) :
    (Effect.emits (fail config active a outcome first).2).countP (answers key)
        + (keys (fail config active a outcome first).1).count key
      ≤ (keys active).count key := by
  unfold fail
  split
  · rw [Effect.emits_append, List.countP_append, hfirst]
    simp [Effect.emits_cons, Effect.emits_nil]
  · rw [Effect.emits_append, List.countP_append, hfirst]
    simp only [Effect.emits_cons, Effect.emits_nil, List.append_nil, List.countP_singleton,
      answers, Nat.zero_add]
    by_cases hkey : a.key = key
    · subst hkey
      have := List.count_pos_iff.mpr (mem_keys.mpr ⟨a, ha, rfl⟩)
      simp only [beq_self_eq_true, ite_true, count_remove_self]
      omega
    · have := count_remove_le active key a.key
      simp only [beq_iff_eq, hkey, ite_false]
      omega

/-- One step adds at most one to what the jobs actor owes `key`, and only for a submission of
it. -/
private theorem owed_step (key : K) (active : List (Active K J)) (msg : Jobs.Msg K J R) :
    (Effect.emits (step config active msg).2).countP (answers key)
        + (keys (step config active msg).1).count key
      ≤ (keys active).count key + (submits key msg).toNat := by
  cases msg with
  | submit key' job =>
    simp only [step]
    split
    · simp [Effect.emits]
    · split
      · by_cases hkey : key' = key <;> simp [Effect.emits, answers, submits, hkey] <;> omega
      · by_cases hkey : key' = key <;> simp [Effect.emits, answers, submits, hkey]
  | result key' attempt r =>
    simp only [step]
    split
    · next a ha =>
      split
      · split
        · exact Nat.le_trans (owed_fail key _ _ (by simp [Effect.emits]) (entry_some ha).1)
            (Nat.le_add_right ..)
        · simp only [Effect.emits, List.filterMap_cons, List.filterMap_nil, List.countP_singleton,
            answers, submits, Bool.toNat_false, Nat.add_zero]
          by_cases hkey : key' = key
          · subst hkey
            simp only [beq_self_eq_true, ite_true, count_remove_self]
            exact one_le_count ha
          · have := count_remove_le active key key'
            simp only [beq_iff_eq, hkey, ite_false]
            omega
      · simp [Effect.emits]
    · simp [Effect.emits]
  | expire key' =>
    simp only [step]
    split
    · next a ha =>
      split
      · exact Nat.le_trans (owed_fail key _ _ (by simp [Effect.emits]) (entry_some ha).1)
          (Nat.le_add_right ..)
      · simp [Effect.emits]
    · simp [Effect.emits]
  | retry key' =>
    simp only [step]
    split
    · split
      · simp [Effect.emits, answers]
      · simp [Effect.emits]
    · simp [Effect.emits]

private theorem owed_handle (key : K) (c : SysState (system (K := K) (J := J) config))
    (i : Unit) (msg : Jobs.Msg K J R) :
    owed key (c.handle env i msg) ≤ owed key c + (submits key msg).toNat := by
  obtain rfl : i = () := rfl
  have h := owed_step (config := config) key (c.state ()) msg
  rw [handle_eq]
  simp only [owed, update_self, List.countP_append]
  omega

private theorem owed_start (key : K) (c : SysState (system (K := K) (J := J) config)) :
    owed key (c.startActor env ()) = owed key c := by
  have hquiet : Effect.emits ((c.state ()).map (rearm config)) = [] := by
    rw [Effect.emits_map]
    exact List.filterMap_eq_nil_iff.mpr fun a _ => by unfold rearm; cases a.phase <;> rfl
  rw [startActor_eq]
  simp [owed, hquiet]

private theorem owed_output (key : K) {c c' : SysState (system (K := K) (J := J) config)}
    {out : Output K J R} (hstep : c.step env (.output out) = some c') :
    owed key c' + (answers key out).toNat = owed key c := by
  have h := SysState.countP_outbox_of_output (answers key) hstep
  obtain ⟨-, rfl⟩ := SysState.step_output.mp hstep
  simp only [owed] at h ⊢
  omega

private theorem handled_snoc (events : List (Event (sig K J R))) (ev : Event (sig K J R))
    (key : K) :
    (handled (deeds (events ++ [ev]))).count key
      = (handled (deeds events)).count key + (handled ev.deed.toList).count key := by
  simp only [handled, deeds, List.filterMap_append, List.count_append]
  cases h : ev.deed <;> simp [h]

private theorem answered_snoc (events : List (Event (sig K J R))) (ev : Event (sig K J R))
    (key : K) :
    (answered (deeds (events ++ [ev]))).count key
      = (answered (deeds events)).count key + (answered ev.deed.toList).count key := by
  simp only [answered, deeds, List.filterMap_append, List.count_append]
  cases h : ev.deed <;> simp [h]

private theorem handled_handle (i : Unit) (msg : Jobs.Msg K J R) (key : K) :
    (handled [Deed.handle (σ := sig K J R) i msg]).count key = (submits key msg).toNat := by
  cases msg <;> simp [handled, submits, Bool.toNat, List.count_cons]

private theorem answered_output (out : Output K J R) (key : K) :
    (answered [Deed.output (σ := sig K J R) out]).count key = (answers key out).toNat := by
  cases out <;> simp [answered, answers, Bool.toNat, List.count_cons]

/-- One event: the answer it hands over and what the jobs actor owes after it are covered by
what it owed before and the submission it handles. -/
private theorem owed_event (key : K) {c c' : SysState (system (K := K) (J := J) config)}
    {ev : Event (sig K J R)} (hstep : c.step env ev = some c') :
    (answered ev.deed.toList).count key + owed key c'
      ≤ owed key c + (handled ev.deed.toList).count key := by
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    simp [owed, Event.deed, answered, handled]
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    have h := owed_handle (env := env) key { c with net := c.net.erase e } e.dst e.msg
    have hhandled := handled_handle e.dst e.msg key
    have hsame : owed key { c with net := c.net.erase e } = owed key c := rfl
    have hanswered : (answered [Deed.handle (σ := sig K J R) e.dst e.msg]).count key = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    have h := owed_handle (env := env) key c e.dst e.msg
    have hhandled := handled_handle e.dst e.msg key
    have hanswered : (answered [Deed.handle (σ := sig K J R) e.dst e.msg]).count key = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    simp [owed, Event.deed, answered, handled]
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    have h := owed_handle (env := env) key
      { c with timers := update c.timers i ((c.timers i).erase msg) } i msg
    have hhandled := handled_handle i msg key
    have hsame : owed key { c with timers := update c.timers i ((c.timers i).erase msg) }
        = owed key c := rfl
    have hanswered : (answered [Deed.handle (σ := sig K J R) i msg]).count key = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | output out =>
    have h := owed_output key hstep
    have hanswered := answered_output out key
    have hhandled : (handled [Deed.output (σ := sig K J R) out]).count key = 0 := rfl
    simp only [Event.deed, Option.toList_some]
    omega
  | crash i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_crash.mp hstep
    simp [owed, SysState.down, Event.deed, answered, handled]
  | start i =>
    obtain ⟨_, _, rfl⟩ := SysState.step_start.mp hstep
    have h := owed_start (env := env) key c
    simp [h, Event.deed, answered, handled]

/-- The jobs actor answers no key more often than it handles a submission of it: in every
environment, whatever arrives and however often. It may crash and restart, and its links may
lose, reorder and duplicate. -/
theorem answered_le_handled (env : EnvModel (sig K J R)) {events : List (Event (sig K J R))}
    {c : SysState (system (K := K) (J := J) config)}
    (hrun : (SysState.init (system config) env).run env events = some c) (key : K) :
    (answered (deeds events)).count key ≤ (handled (deeds events)).count key := by
  suffices h : (answered (deeds events)).count key + owed key c
      ≤ (handled (deeds events)).count key from Nat.le_trans (Nat.le_add_right _ _) h
  refine System.Reachable.run_induction
    (P := fun events c => (answered (deeds events)).count key + owed key c
      ≤ (handled (deeds events)).count key) .init hrun ?_ ?_
  · have hinit : owed key (SysState.init (system (K := K) (J := J) config) env) = 0 :=
      (owed_start (env := env) key (SysState.blank _)).trans
        (by simp [owed, SysState.blank, actor])
    simp [hinit, answered, handled, deeds]
  rintro evs c₁ ev c₂ - hle hstep
  have h := owed_event (env := env) key hstep
  rw [handled_snoc, answered_snoc]
  omega

/-- Beside any system, the jobs actor keeps no more jobs active than its slots. -/
theorem attach_within {τ : Signature} (sys : System τ) (config : Config R) (use : Use τ K J R)
    (env : EnvModel (joinSig (sig K J R) τ)) :
    (attach sys config use).Invariant env
      fun c => Within config (c.state (.inl ()) : List (Active K J)) :=
  System.Invariant.join_left_state (a := system config) (b := sys) (w := use.wiring)
    (Q := fun s : (_ : Unit) → List (Active K J) => Within config (s ()))
    fun env => within config env

end Lanes.Jobs
