/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Watchdog

/-!
# A keeper that pings forever keeps the dog quiet, in a fair run

Fairness obliges a timer to fire if it stays pending and no step arms it again. The dog's
`silence` timer is armed again by every ping. So the run in which the keeper's timer fires, its
ping is delivered, and so on forever, is fair, although `silence` is pending at every position
and never fires (`exists_fair_run_never_barks`). The run is given in full: two states and two
events, in turn.

Fairness that obliged every timer that stays pending to fire would rule this run out. In every
run of that kind the dog barks (`impatient_barks`), whatever the keeper does, because nothing
but barking takes its timer away.
-/

namespace Watchdog

open Lanes

variable {config : Config}

/-- What the dog owes when it has heard nothing: to bark. -/
abbrev silence : Obligation sig := .timeout .dog .silence

/-- Both are up with their timers pending, and nothing is in flight. -/
def quiet (config : Config) : SysState (system config) where
  state _ := ()
  up _ := true
  net := []
  timers
    | .keeper => [.tick]
    | .dog => [.silence]
  outbox := []

def pinged (config : Config) : SysState (system config) :=
  { quiet config with net := [ping] }

local macro "same_state" : tactic => `(tactic|
  (apply SysState.ext' <;> (try funext i; cases i) <;>
    simp [SysState.init, SysState.startActor, SysState.handle, SysState.settle,
      SysState.performAll, SysState.perform, SysState.blank, keeper, dog, quiet, pinged, ping,
      Effect.isStop, update] <;> rfl))

theorem init_eq_quiet : SysState.init (system config) {} = quiet config := by
  same_state

theorem quiet_step :
    (quiet config).step {} (.timeout .keeper .tick) = some (pinged config) := by
  refine SysState.step_timeout.mpr ⟨rfl, by simp [quiet], ?_⟩
  same_state

theorem pinged_step : (pinged config).step {} (.deliver ping) = some (quiet config) := by
  refine SysState.step_deliver.mpr ⟨rfl, ?_, ?_⟩
  · simp [pinged, ping, SysState.deliverable, Envelope.sameLink, Link.reliable]
  · same_state

/-- The keeper's timer fires and its ping is delivered, forever. -/
def pinging (config : Config) : (system config).Run {} where
  state k := if k % 2 = 0 then quiet config else pinged config
  event k := some (if k % 2 = 0 then .timeout .keeper .tick else .deliver ping)
  init := init_eq_quiet.symm
  exec k := by
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : (k + 1) % 2 = 1 := by omega
      simpa [Spec.stutter, System.sem, h, h'] using quiet_step
    · have h' : (k + 1) % 2 = 0 := by omega
      simpa [Spec.stutter, System.sem, h, h'] using pinged_step

theorem pinging_state_even (n : Nat) : (pinging config).state (2 * n) = quiet config := by
  simp [pinging]

theorem pinging_event_even (n : Nat) :
    (pinging config).event (2 * n) = some (.timeout .keeper .tick) := by
  simp [pinging]

theorem pinging_state_odd (n : Nat) : (pinging config).state (2 * n + 1) = pinged config := by
  simp [pinging]

theorem pinging_event_odd (n : Nat) : (pinging config).event (2 * n + 1) = some (.deliver ping) := by
  simp [pinging]

/-- The dog is up and its timer is pending, at every position. -/
theorem pinging_silence_due (n : Nat) : silence.Due {} ((pinging config).state n) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
    simp [pinging, h, Obligation.Due, quiet, pinged]

theorem pinging_never_barks (n : Nat) : (pinging config).event n ≠ some bark := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [pinging, h, bark]

/-- Each delivery of a ping arms the dog's timer again. -/
theorem pinging_restarts (n : Nat) : (pinging config).Restarts (2 * n + 1) silence :=
  ⟨_, pinging_event_odd n, by
    simp [pinging_state_odd, Obligation.Restarted, SysState.arms, Effect.timeouts, ping, dog]⟩

theorem pinging_fair : (pinging config).Fair := by
  refine System.Run.fair_iff.mpr fun ob n hdue => ?_
  have heven := (hdue (2 * n) (by omega)).1
  rw [pinging_state_even] at heven
  cases ob with
  | deliver e => simp [Obligation.Due, quiet, SysState.deliverable] at heven
  | start i => simp [Obligation.Due, quiet] at heven
  | output out => simp [Obligation.Due, quiet] at heven
  | timeout i msg =>
    cases i with
    | keeper =>
      cases msg with
      | tick => exact ⟨2 * n, by omega, pinging_event_even n⟩
      | rest => simp [Obligation.Due, quiet] at heven
    | dog =>
      cases msg with
      | ping => simp [Obligation.Due, quiet] at heven
      | silence => exact absurd (pinging_restarts n) (hdue (2 * n + 1) (by omega)).2

/-- Fairness does not make a timer fire while it keeps being armed again: there is a fair run
in which the dog is up with its timer pending at every position, pings keep being delivered,
and the dog never barks. -/
theorem exists_fair_run_never_barks (config : Config) :
    ∃ r : (system config).Run {}, r.Fair ∧
      (∀ n, silence.Due {} (r.state n)) ∧
      (∀ n, ∃ m, n ≤ m ∧ r.event m = some (.deliver ping)) ∧
      ∀ n, r.event n ≠ some bark :=
  ⟨pinging config, pinging_fair, pinging_silence_due,
    fun n => ⟨2 * n + 1, by omega, pinging_event_odd n⟩, pinging_never_barks⟩

/-- Short of barking, no step takes the dog down or its timer away. -/
theorem silence_due_of_step {c c' : SysState (system config)} {ev : Event sig}
    (hdue : silence.Due {} c) (hstep : c.step {} ev = some c') (hev : ev ≠ bark) :
    silence.Due {} c' := by
  obtain ⟨hup, hmem⟩ := hdue
  refine ⟨SysState.up_of_step rfl (fun _ msg => by cases msg <;> rfl) hup hstep, ?_⟩
  have hdog (c : SysState (system config)) (msg : DogMsg) (h : DogMsg.silence ∈ c.timers .dog) :
      DogMsg.silence ∈ (c.handle {} .dog msg).timers .dog := by
    cases msg <;>
      simp [SysState.handle, SysState.settle, SysState.performAll, SysState.perform, dog,
        Effect.isStop, h]
  have hkeeper (c : SysState (system config)) (r : Unit × List (Effect sig .keeper))
      (h : DogMsg.silence ∈ c.timers .dog) :
      DogMsg.silence ∈ (c.settle {} .keeper r).timers .dog := by
    rw [SysState.settle_timers_of_ne _ (by decide)]
    exact h
  cases ev with
  | input x =>
    obtain rfl := SysState.step_input.mp hstep
    exact hmem
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_deliver.mp hstep
    obtain ⟨src, dst, msg⟩ := e
    cases dst with
    | keeper => exact hkeeper _ _ hmem
    | dog => exact hdog _ msg hmem
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := SysState.step_duplicate.mp hstep
    obtain ⟨src, dst, msg⟩ := e
    cases dst with
    | keeper => exact hkeeper _ _ hmem
    | dog => exact hdog _ msg hmem
  | drop e =>
    obtain ⟨_, _, rfl⟩ := SysState.step_drop.mp hstep
    exact hmem
  | timeout i msg =>
    obtain ⟨_, _, rfl⟩ := SysState.step_timeout.mp hstep
    cases i with
    | keeper => exact hkeeper _ _ (by simpa [update] using hmem)
    | dog =>
      cases msg with
      | silence => exact absurd rfl hev
      | ping => exact hdog _ _ (by simpa [update] using hmem)
  | output out =>
    obtain ⟨_, rfl⟩ := SysState.step_output.mp hstep
    exact hmem
  | crash i =>
    obtain ⟨_, hmay, -⟩ := SysState.step_crash.mp hstep
    cases hmay
  | start i =>
    obtain ⟨hdown, _, rfl⟩ := SysState.step_start.mp hstep
    cases i with
    | keeper => exact hkeeper _ _ hmem
    | dog => simp [hup] at hdown

/-- A run that fires every timer that stays pending has the dog bark, however the keeper
pings: there the timer of a keep-alive fires though it is kept alive. -/
theorem impatient_barks {r : (system config).Run {}} (h : r.Impatient) :
    ∃ n, r.event n = some bark := by
  refine Classical.byContradiction fun hnever => ?_
  have hdue (n : Nat) : silence.Due {} (r.state n) := by
    induction n with
    | zero =>
      rw [r.init, init_eq_quiet]
      simp [Obligation.Due, quiet]
    | succ n ih =>
      cases hev : r.event n with
      | none => exact System.Run.step_none hev ▸ ih
      | some ev =>
        exact silence_due_of_step ih (System.Run.step_some hev) fun hbark =>
          hnever ⟨n, hbark ▸ hev⟩
  obtain ⟨n, _, hbarks⟩ := h silence 0 fun m _ => hdue m
  exact hnever ⟨n, hbarks⟩

/-- So the run in which the keeper pings forever is fair and not impatient. -/
theorem pinging_not_impatient : ¬(pinging config).Impatient := fun h =>
  have ⟨n, hbarks⟩ := impatient_barks h
  pinging_never_barks n hbarks

end Watchdog
