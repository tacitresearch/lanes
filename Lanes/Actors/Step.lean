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

## Main statements

- `SysState.step_input`, `step_deliver`, `step_duplicate`, `step_drop`, `step_timeout`,
  `step_output`, `step_crash`, `step_start`: one `iff` per event.
- `SysState.mem_of_deliverable`: a deliverable message is in flight.
- `SysState.performAll_nil`, `performAll_cons`: effects are performed in order.
- `SysState.performAll_emit`: what a step that only emits outputs does.
-/

public section

namespace Lanes.SysState

variable {σ : Signature} {sys : System σ} {env : EnvModel σ} {c c' : SysState sys}

@[simp] theorem performAll_nil (c : SysState sys) (i : σ.Id) : c.performAll i [] = c := rfl

@[simp] theorem performAll_cons (c : SysState sys) (i : σ.Id) (eff : Effect σ i)
    (effs : List (Effect σ i)) :
    c.performAll i (eff :: effs) = (c.perform i eff).performAll i effs := rfl

/-- Emitting outputs appends them to the outbox and touches nothing else. -/
theorem performAll_emit (c : SysState sys) (i : σ.Id) (outs : List σ.Out) :
    c.performAll i (outs.map .emit) = { c with outbox := c.outbox ++ outs } := by
  induction outs generalizing c with
  | nil => simp
  | cons out outs ih => simp [ih, perform, List.append_assoc]

/-- A list of emits never asks to stop. -/
theorem any_isStop_emit {i : σ.Id} (outs : List σ.Out) :
    (outs.map (Effect.emit (self := i))).any Effect.isStop = false := by
  induction outs with
  | nil => rfl
  | cons out outs ih => simp [Effect.isStop, ih]

/-- A deliverable message is in flight. -/
theorem mem_of_deliverable {e : Envelope σ} (h : c.deliverable env e = true) : e ∈ c.net := by
  unfold deliverable at h
  split at h
  · exact List.mem_of_find?_eq_some (by simpa using h)
  · simpa using h

/-- An input is always enabled: it is queued for the actor that accepts it. -/
theorem step_input {x : σ.In} :
    c.step env (.input x) = some c' ↔
      c' = { c with net := c.net ++ [⟨none, (sys.accept x).1, (sys.accept x).2⟩] } := by
  simp only [step, Option.some.injEq]
  exact eq_comm

/-- A delivery needs the receiver up and the message deliverable; the message is consumed and
handled. -/
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

/-- A duplicate delivery needs a duplicating link; the message is handled and stays in flight. -/
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

/-- A message is lost only on a lossy link. -/
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

/-- A timeout needs the actor up and the timer pending; the timer is consumed and its message
handled. -/
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

/-- An output leaves the outbox. -/
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

/-- A crash needs the actor up and the environment model to allow it. -/
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

/-- A start needs the actor down, and mail waiting or a restart policy. -/
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
