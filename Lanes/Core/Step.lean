/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.World

/-!
# What each event does

One characterisation per event of `SysState.step`: when the event is enabled and exactly which
state it leads to. Proofs of system invariants case on the event and rewrite with these, instead
of unfolding the step function.
-/

public section

namespace Lanes.SysState

variable {σ : Signature} {sys : System σ} {env : EnvModel σ} {c c' : SysState sys}

@[simp] theorem performAll_nil (c : SysState sys) (i : σ.Id) : c.performAll i [] = c := rfl

@[simp] theorem performAll_cons (c : SysState sys) (i : σ.Id) (eff : Effect σ i)
    (effs : List (Effect σ i)) :
    c.performAll i (eff :: effs) = (c.perform i eff).performAll i effs := rfl

theorem performAll_emit (c : SysState sys) (i : σ.Id) (outs : List σ.Out) :
    c.performAll i (outs.map .emit) = { c with outbox := c.outbox ++ outs } := by
  induction outs generalizing c with
  | nil => simp
  | cons out outs ih => simp [ih, perform, List.append_assoc]

theorem any_isStop_emit {i : σ.Id} (outs : List σ.Out) :
    (outs.map (Effect.emit (self := i))).any Effect.isStop = false := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simp [Effect.isStop, ih]

theorem performAll_induction {P : SysState sys → Prop} {i : σ.Id} {effs : List (Effect σ i)}
    (start : P c) (perform : ∀ c, ∀ eff ∈ effs, P c → P (c.perform i eff)) :
    P (c.performAll i effs) := by
  induction effs generalizing c with
  | nil => exact start
  | cons eff effs ih =>
    exact ih (perform c eff (by simp) start) fun c eff' h => perform c eff' (by simp [h])

/-- What a step preserves: whatever the new state, each effect and stopping preserve. -/
theorem settle_induction {P : SysState sys → Prop} {i : σ.Id} {r : sys.State i × List (Effect σ i)}
    (state : P { c with state := update c.state i r.1 })
    (perform : ∀ c, ∀ eff ∈ r.2, P c → P (c.perform i eff))
    (down : ∀ c, P c → P (c.down env i)) : P (c.settle env i r) := by
  unfold settle
  split
  · exact down _ (performAll_induction state perform)
  · exact performAll_induction state perform

theorem settle_up_of_ne {i k : σ.Id} (r : sys.State i × List (Effect σ i)) (h : k ≠ i) :
    (c.settle env i r).up k = c.up k := by
  apply settle_induction (P := fun c' => c'.up k = c.up k) rfl
  · intro c' eff _ hc'
    cases eff <;> exact hc'
  · intro c' hc'
    simpa [down, h] using hc'

theorem settle_up_of_running {i : σ.Id} {r : sys.State i × List (Effect σ i)}
    (h : r.2.any Effect.isStop = false) (k : σ.Id) : (c.settle env i r).up k = c.up k := by
  unfold settle
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  exact performAll_induction (P := fun c' => c'.up k = c.up k) rfl fun c' eff _ hc' => by
    cases eff <;> exact hc'

theorem settle_timers_of_ne {i k : σ.Id} (r : sys.State i × List (Effect σ i)) (h : k ≠ i) :
    (c.settle env i r).timers k = c.timers k := by
  apply settle_induction (P := fun c' => c'.timers k = c.timers k) rfl
  · intro c' eff _ hc'
    cases eff <;> simpa [perform, h] using hc'
  · intro c' hc'
    simpa [down, h] using hc'

theorem init_induction {P : SysState sys → Prop} (blank : P (blank sys))
    (start : ∀ c i, P c → P (c.startActor env i)) : P (init sys env) := by
  unfold init
  generalize SysState.blank sys = c at blank
  induction sys.boot generalizing c with
  | nil => exact blank
  | cons i boot ih => exact ih _ (start c i blank)

theorem mem_of_deliverable {e : Envelope σ} (h : c.deliverable env e = true) : e ∈ c.net := by
  unfold deliverable at h
  split at h
  · exact List.mem_of_find?_eq_some (by simpa using h)
  · simpa using h

theorem step_input {x : σ.In} :
    c.step env (.input x) = some c' ↔
      c' = { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] } := by
  simp only [step, Option.some.injEq]
  exact eq_comm

theorem step_deliver {e : Envelope σ} :
    c.step env (.deliver e) = some c' ↔
      c.up e.dst = true ∧ c.deliverable env e = true ∧
        c' = ({ c with net := c.net.erase e }).handle env e.dst e.msg := by
  simp only [step]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    simp only [Option.some.injEq, h.1, h.2, true_and]
    exact eq_comm
  · next h =>
    simp only [Bool.and_eq_true] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

theorem step_duplicate {e : Envelope σ} :
    c.step env (.duplicate e) = some c' ↔
      c.up e.dst = true ∧ (env.link e.src e.dst).duplicating = true ∧
        c.deliverable env e = true ∧ c' = c.handle env e.dst e.msg := by
  simp only [step]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    simp only [Option.some.injEq, h.1.1, h.1.2, h.2, true_and]
    exact eq_comm
  · next h =>
    simp only [Bool.and_eq_true] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ h₂ h₃ => absurd ⟨⟨h₁, h₂⟩, h₃⟩ h

theorem step_drop {e : Envelope σ} :
    c.step env (.drop e) = some c' ↔
      (env.link e.src e.dst).lossy = true ∧ e ∈ c.net ∧ c' = { c with net := c.net.erase e } := by
  simp only [step]
  split
  · next h =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [Option.some.injEq, h.1, h.2, true_and]
    exact eq_comm
  · next h =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

theorem step_timeout {i : σ.Id} {msg : σ.Msg i} :
    c.step env (.timeout i msg) = some c' ↔
      c.up i = true ∧ msg ∈ c.timers i ∧
        c' = ({ c with timers := update c.timers i ((c.timers i).erase msg) }).handle env i msg := by
  simp only [step]
  split
  · next h =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [Option.some.injEq, h.1, h.2, true_and]
    exact eq_comm
  · next h =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

theorem step_output {out : σ.Out} :
    c.step env (.output out) = some c' ↔
      out ∈ c.outbox ∧ c' = { c with outbox := c.outbox.erase out } := by
  simp only [step]
  split
  · next h =>
    simp only [List.contains_iff_mem] at h
    simp only [Option.some.injEq, h, true_and]
    exact eq_comm
  · next h =>
    simp only [List.contains_iff_mem] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ => absurd h₁ h

theorem step_crash {i : σ.Id} :
    c.step env (.crash i) = some c' ↔
      c.up i = true ∧ env.mayCrash i = true ∧ c' = c.down env i := by
  simp only [step]
  split
  · next h =>
    simp only [Bool.and_eq_true] at h
    simp only [Option.some.injEq, h.1, h.2, true_and]
    exact eq_comm
  · next h =>
    simp only [Bool.and_eq_true] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

theorem step_start {i : σ.Id} :
    c.step env (.start i) = some c' ↔
      c.up i = false ∧ (c.hasMail i = true ∨ env.restarts i = true) ∧
        c' = c.startActor env i := by
  simp only [step]
  split
  · next h =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
    simp only [Option.some.injEq, h.1, h.2, true_and]
    exact eq_comm
  · next h =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h

theorem step_restart :
    c.step env .restart = some c' ↔ env.mayRestart = true ∧ c' = init sys env := by
  simp only [step]
  split
  · next h => simp only [Option.some.injEq, h, true_and]; exact eq_comm
  · next h => simp [h]

theorem step_restart_of_noRestarts (h : env.mayRestart = false) : c.step env .restart = none := by
  simp [step, h]

/-- An actor that never stops itself stays up for as long as the environment neither crashes
it nor restarts the process. -/
theorem up_of_step {i : σ.Id} {ev : Event σ} (hcrash : env.mayCrash i = false)
    (hrestart : env.mayRestart = false)
    (hruns : ∀ s msg, ((sys.actor i).step s msg).2.any Effect.isStop = false)
    (hup : c.up i = true) (hstep : c.step env ev = some c') : c'.up i = true := by
  have hhandle (c : SysState sys) (j : σ.Id) (msg : σ.Msg j) (hc : c.up i = true) :
      (c.handle env j msg).up i = true := by
    by_cases hj : i = j
    · subst hj
      rw [handle, settle_up_of_running (hruns _ _)]
      exact hc
    · rw [handle, settle_up_of_ne _ hj]
      exact hc
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact hup
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := step_deliver.mp hstep
    exact hhandle _ _ _ hup
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := step_duplicate.mp hstep
    exact hhandle _ _ _ hup
  | drop e =>
    obtain ⟨_, _, rfl⟩ := step_drop.mp hstep
    exact hup
  | timeout j msg =>
    obtain ⟨_, _, rfl⟩ := step_timeout.mp hstep
    exact hhandle _ _ _ hup
  | output out =>
    obtain ⟨_, rfl⟩ := step_output.mp hstep
    exact hup
  | crash j =>
    obtain ⟨_, hmay, rfl⟩ := step_crash.mp hstep
    have hj : i ≠ j := by
      rintro rfl
      simp [hcrash] at hmay
    simpa [down, hj] using hup
  | start j =>
    obtain ⟨hdown, _, rfl⟩ := step_start.mp hstep
    have hj : i ≠ j := by
      rintro rfl
      simp [hup] at hdown
    rw [startActor, settle_up_of_ne _ hj]
    simpa [hj] using hup
  | restart => simp [step_restart_of_noRestarts hrestart] at hstep

/-- An emitted output stays in the outbox until it is handed over, unless the process
restarts. -/
theorem mem_outbox_of_step {out : σ.Out} {ev : Event σ} (hout : out ∈ c.outbox)
    (hrestart : env.mayRestart = false) (hstep : c.step env ev = some c')
    (hev : ev ≠ .output out) : out ∈ c'.outbox := by
  have hsettle (c : SysState sys) (j : σ.Id) (r : sys.State j × List (Effect σ j))
      (hc : out ∈ c.outbox) : out ∈ (c.settle env j r).outbox := by
    refine settle_induction (P := fun c' => out ∈ c'.outbox) hc ?_ fun _ h => h
    intro c' eff _ hc'
    cases eff with
    | emit out' => exact List.mem_append_left _ hc'
    | _ => exact hc'
  cases ev with
  | input x =>
    obtain rfl := step_input.mp hstep
    exact hout
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := step_deliver.mp hstep
    exact hsettle _ _ _ hout
  | duplicate e =>
    obtain ⟨_, _, _, rfl⟩ := step_duplicate.mp hstep
    exact hsettle _ _ _ hout
  | drop e =>
    obtain ⟨_, _, rfl⟩ := step_drop.mp hstep
    exact hout
  | timeout j msg =>
    obtain ⟨_, _, rfl⟩ := step_timeout.mp hstep
    exact hsettle _ _ _ hout
  | output out' =>
    obtain ⟨_, rfl⟩ := step_output.mp hstep
    exact (List.mem_erase_of_ne fun h => hev (congrArg Event.output h.symm)).mpr hout
  | crash j =>
    obtain ⟨_, _, rfl⟩ := step_crash.mp hstep
    exact hout
  | start j =>
    obtain ⟨_, _, rfl⟩ := step_start.mp hstep
    exact hsettle _ _ _ hout
  | restart => simp [step_restart_of_noRestarts hrestart] at hstep

end Lanes.SysState

/-! A restart leads to the initial state, which every run starts from, and every other event
steps the same whether or not the environment allows restarts. So a system reaches the same
states with restarts and without: an invariant proved where the process never restarts holds
where it does (`System.Invariant.of_withoutRestarts`). What a restart breaks is what relates two
moments, such as a liveness property or a count over a run. -/

namespace Lanes

variable {σ : Signature} {sys : System σ}

/-- `env` with process restarts ruled out. -/
@[expose] def EnvModel.withoutRestarts (env : EnvModel σ) : EnvModel σ :=
  { env with mayRestart := false }

@[simp] theorem EnvModel.withoutRestarts_mayRestart (env : EnvModel σ) :
    env.withoutRestarts.mayRestart = false := rfl

/-- Where the process may restart and nothing else fails, the same environment without
restarts is faultless. -/
theorem EnvModel.Restarts.withoutRestarts {env : EnvModel σ} (h : env.Restarts) :
    env.withoutRestarts.Faultless :=
  ⟨⟨h.lossless, h.noDuplicates, h.noCrashes⟩, rfl⟩

namespace SysState

variable {env : EnvModel σ}

@[simp] theorem init_withoutRestarts : init sys env.withoutRestarts = init sys env := rfl

/-- Every event but a restart steps the same whether or not the environment allows
restarts. -/
theorem step_withoutRestarts {c : SysState sys} {ev : Event σ} (hev : ev ≠ .restart) :
    c.step env.withoutRestarts ev = c.step env ev := by
  cases ev with
  | restart => exact absurd rfl hev
  | _ => rfl

end SysState

namespace System

variable {env : EnvModel σ}

/-- A system reaches the same states whether or not the process may restart: a restart only
leads back to where every run starts. -/
theorem reachable_withoutRestarts {c : SysState sys} :
    sys.Reachable env.withoutRestarts c ↔ sys.Reachable env c := by
  constructor
  · intro h
    induction h with
    | init => exact .init
    | @step c c' ev _ hstep ih =>
      have hev : ev ≠ .restart := by
        rintro rfl
        simp [SysState.step] at hstep
      exact .step ev ih (by rwa [SysState.step_withoutRestarts hev] at hstep)
  · intro h
    induction h with
    | init => exact .init
    | @step c c' ev _ hstep ih =>
      by_cases hev : ev = .restart
      · subst hev
        obtain ⟨-, rfl⟩ := SysState.step_restart.mp hstep
        exact .init
      · exact .step ev ih (by rwa [SysState.step_withoutRestarts hev])

/-- An invariant proved where the process never restarts holds where it may. -/
theorem Invariant.of_withoutRestarts {P : SysState sys → Prop}
    (h : sys.Invariant env.withoutRestarts P) : sys.Invariant env P :=
  fun c hc => h c (reachable_withoutRestarts.mpr hc)

theorem invariant_withoutRestarts {P : SysState sys → Prop} :
    sys.Invariant env.withoutRestarts P ↔ sys.Invariant env P :=
  ⟨Invariant.of_withoutRestarts, fun h c hc => h c (reachable_withoutRestarts.mp hc)⟩

/-- An invariant proved for every faultless environment holds where the process may restart. -/
theorem Invariant.restarts {P : SysState sys → Prop}
    (h : ∀ env : EnvModel σ, env.Faultless → sys.Invariant env P) (henv : env.Restarts) :
    sys.Invariant env P :=
  (h _ henv.withoutRestarts).of_withoutRestarts

end System

end Lanes
