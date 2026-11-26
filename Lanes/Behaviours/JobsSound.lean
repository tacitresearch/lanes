/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Behaviours.Jobs
public import Lanes.Actors.Deed
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
