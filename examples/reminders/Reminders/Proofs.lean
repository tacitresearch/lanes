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
(`Reminders.delivery_ends`). If the reminders do not crash either and the link from the
scheduler to them loses nothing, the end reaches them as an answer: sent, given up on, or
cancelled (`Reminders.delivery_answered`).

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
  | noticed key task now_ms =>
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

theorem app_runs (config : Config) (s : State) (x : In) :
    ((app config).step s x).2.any Effect.isStop = false := by
  cases x with
  | remind req now_ms text in_s =>
    simp only [app, step, remind]
    split
    · simp [reply, Effect.isStop]
    · split <;> simp [reply, Effect.isStop]
  | cancel req id =>
    simp only [app, step, cancel]
    split <;> simp [reply, Effect.isStop]
  | list req => simp [app, step, reply, Effect.isStop]
  | noticed key task now_ms => cases key <;> simp [app, step]
  | answered key outcome =>
    cases key with
    | sweep => simp [app, step]
    | reminder id =>
      simp only [app, step]
      cases outcome with
      | failed payload attempts last => cases payload <;> simp [answered, Effect.isStop]
      | _ => simp [answered]

/-- Every reminder held is answered: in a fair run in which neither the scheduler nor the
reminders are crashed and the link from the scheduler to the reminders loses nothing, the job of
a reminder, a call held while the scheduler is up, is answered to the reminders at a later
position. The answer ends it: sent (`succeeded`), given up on (`failed`) or cancelled. -/
theorem delivery_answered (config : Config)
    {env : EnvModel (joinSig (Schedule.sig Key Task Answer) sig)}
    (hcrash : env.mayCrash (.inl ()) = false) (hcrashes : env.mayCrash (.inr ()) = false)
    (hlossless : (env.link (some (.inl ())) (.inr ())).lossy = false) (id : Nat)
    {r : (system config).Run env} (hfair : r.Fair) {n : ℕ}
    (hup : (r.state n).up (.inl ()) = true) {j : Schedule.Job Key Task}
    (hj : Schedule.entry ((r.state n).state (.inl ()) : Schedule.State Key Task).jobs
      (.reminder id) = some j) {retry : Schedule.Retry} (hwork : j.work = .call retry) :
    ∃ m o, n ≤ m ∧ o.isEnd = true ∧
      (r.event m = some (.deliver ⟨some (.inl ()), .inr (), .answered (.reminder id) o⟩) ∨
        r.event m = some (.duplicate ⟨some (.inl ()), .inr (), .answered (.reminder id) o⟩)) :=
  Schedule.attach_answer_handled (reminders config) config.scheduler use hcrash
    (fun _ => hlossless) (fun _ => hcrashes) (fun _ => app_runs config)
    (fun _ s => by simp [app, Effect.isStop]) (.reminder id) hfair hup hj hwork

end Reminders
