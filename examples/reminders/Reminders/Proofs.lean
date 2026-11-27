/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Reminders.App

/-!
# What holds of the reminders

In every run, under every environment model (lost, reordered and repeated messages, crashes and
restarts), the reminders stay within `maxReminders` (`Reminders.bounded`) and the scheduler
beside them holds no more than `maxReminders + 1` jobs, no id twice
(`Reminders.jobs_bounded`). In a fair run in which the scheduler does not crash, the delivery
of every reminder comes to an end, whatever the notification service does
(`Reminders.delivery_ends`): it is sent, given up on, or cancelled.

What an attempt is, that none starts before its time, that none starts while another of its
reminder is out, and that a reminder is called no more often than its attempts, is the
scheduler's (`Lanes.Behaviours.Schedule.Sound`), and holds here because the scheduler's steps
are its own steps in the join.
-/

namespace Reminders

open Lanes

/-- No more reminders are kept than `maxReminders`. -/
def Bounded (config : Config) (s : State) : Prop := s.reminders.length ≤ config.maxReminders

theorem setStage_length (s : State) (id : Nat) (stage : Stage) :
    (setStage s id stage).reminders.length = s.reminders.length := by
  simp [setStage]

theorem step_bounded (config : Config) {s : State} (h : Bounded config s) (x : In) :
    Bounded config (step config s x).1 := by
  unfold Bounded at h ⊢
  cases x with
  | remind req now_ms text in_s =>
    simp only [step, remind]
    split
    · exact h
    · split
      · exact h
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  | cancel req id =>
    simp only [step, cancel]
    split <;> exact h
  | list req => exact h
  | noticed key task =>
    cases key with
    | sweep => exact Nat.le_trans (List.length_filter_le ..) h
    | reminder _ => exact h
  | answered key outcome =>
    cases key with
    | sweep => exact h
    | reminder id =>
      simp only [step, answered]
      split <;> simp only [setStage_length] <;> exact h

theorem app_bounded (config : Config) : (app config).Invariant (Bounded config) :=
  Actor.Inductive.invariant
    ⟨by simp [app, Bounded], fun _ x h => step_bounded config h x, fun _ h => h⟩

/-- The reminders stay within `maxReminders`, in every run and every environment. -/
theorem bounded (config : Config) (env : EnvModel (joinSig (Schedule.sig Key Task Answer) sig)) :
    (system config).Invariant env fun c => Bounded config (c.state (.inr ()) : State) :=
  System.invariant_of_actor (system config) (.inr ()) (Actor.Invariant.mapEff _ (app_bounded config))
    env

/-- The scheduler beside the reminders holds no more than `maxReminders + 1` jobs, no id twice. -/
theorem jobs_bounded (config : Config)
    (env : EnvModel (joinSig (Schedule.sig Key Task Answer) sig)) :
    (system config).Invariant env fun c =>
      (c.state (.inl ()) : Schedule.State Key Task).jobs.length ≤ config.maxReminders + 1 ∧
        (Schedule.keys (c.state (.inl ()) : Schedule.State Key Task).jobs).Nodup :=
  Schedule.attach_within (reminders config) config.scheduler use env

/-- The delivery of a reminder comes to an end: in a fair run in which the scheduler does not
crash, its job, while it is held, stops being held, and the step that ends it tells the
reminders (`Schedule.ends_of_leaves`). -/
theorem delivery_ends (config : Config)
    {env : EnvModel (joinSig (Schedule.sig Key Task Answer) sig)}
    (hcrash : env.mayCrash (.inl ()) = false) (id : Nat) :
    (system config).LeadsTo env
      (fun c => c.up (.inl ()) = true ∧ ∃ j, Schedule.entry
        (c.state (.inl ()) : Schedule.State Key Task).jobs (.reminder id) = some j ∧
          j.work.periodic = false)
      (fun c => Key.reminder id ∉ Schedule.keys (c.state (.inl ()) : Schedule.State Key Task).jobs) :=
  Schedule.attach_held_leaves (reminders config) config.scheduler use hcrash (.reminder id)

end Reminders
