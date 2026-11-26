/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.World

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

end Lanes.SysState
