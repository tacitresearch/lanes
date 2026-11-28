/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.World

/-!
# From one actor to the whole system

Frame lemmas for `SysState.step`, and the lifting theorem: whatever is proved about one actor in
isolation holds for that actor in every reachable state of every system it is part of, under
every environment model. This is what makes per-actor proofs worth writing: no other actor, no
message order and no fault can break them.
-/

public section

namespace Lanes

variable {σ : Signature} {sys : System σ}

namespace SysState

@[simp] theorem perform_state (c : SysState sys) (i : σ.Id) (eff : Effect σ i) :
    (c.perform i eff).state = c.state := by
  cases eff <;> rfl

@[simp] theorem performAll_state (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    (c.performAll i effs).state = c.state := by
  unfold performAll
  induction effs generalizing c with
  | nil => rfl
  | cons eff effs ih => rw [List.foldl_cons, ih, perform_state]

@[simp] theorem perform_up (c : SysState sys) (i : σ.Id) (eff : Effect σ i) :
    (c.perform i eff).up = c.up := by
  cases eff <;> rfl

@[simp] theorem performAll_up (c : SysState sys) (i : σ.Id) (effs : List (Effect σ i)) :
    (c.performAll i effs).up = c.up := by
  unfold performAll
  induction effs generalizing c with
  | nil => rfl
  | cons eff effs ih => rw [List.foldl_cons, ih, perform_up]

@[simp] theorem down_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id) :
    (c.down env i).state = c.state := rfl

@[simp] theorem settle_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (c.settle env i r).state = update c.state i r.1 := by
  unfold settle
  split <;> simp

@[simp] theorem handle_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id) (msg : σ.Msg i)
    (src : Sender σ.Id) :
    (c.handle env i msg src).state
      = update c.state i ((sys.actor i).stepAt { toMoment := c.clock, src } (c.state i) msg).1 := by
  simp [handle]

@[simp] theorem startActor_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id) :
    (c.startActor env i).state = update c.state i ((sys.actor i).recoverAt c.clock (c.state i)).1 := by
  simp [startActor]

/--
How one event changes actor states: not at all, or one actor `i` moves by its own `step` on some
message in some context, or one actor `i` moves by its own `recover` at some moment, or a restart
puts every actor back in its state at `SysState.init`.
-/
theorem step_state {env : EnvModel σ} {c c' : SysState sys} {ev : Event σ}
    (h : c.step env ev = some c') :
    c'.state = c.state ∨
    (∃ i ctx msg, c'.state = update c.state i ((sys.actor i).stepAt ctx (c.state i) msg).1) ∨
    (∃ i t, c'.state = update c.state i ((sys.actor i).recoverAt t (c.state i)).1) ∨
    (ev = .restart ∧ c'.state = (init sys env).state) := by
  cases ev with
  | input x =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact .inl rfl
  | deliver e =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inr (.inl ⟨e.dst, _, e.msg, by simp; rfl⟩)
    · contradiction
  | duplicate e =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inr (.inl ⟨e.dst, _, e.msg, by simp; rfl⟩)
    · contradiction
  | drop e =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl rfl
    · contradiction
  | timeout i msg =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inr (.inl ⟨i, _, msg, by simp; rfl⟩)
    · contradiction
  | output out =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl rfl
    · contradiction
  | crash i =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inl rfl
    · contradiction
  | start i =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inr (.inr (.inl ⟨i, _, by simp; rfl⟩))
    · contradiction
  | restart =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inr (.inr (.inr ⟨rfl, rfl⟩))
    · contradiction
  | tick m =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact .inl rfl

/-- `step_state` for an event other than a restart. -/
theorem step_state_of_ne_restart {env : EnvModel σ} {c c' : SysState sys} {ev : Event σ}
    (h : c.step env ev = some c') (hev : ev ≠ .restart) :
    c'.state = c.state ∨
    (∃ i ctx msg, c'.state = update c.state i ((sys.actor i).stepAt ctx (c.state i) msg).1) ∨
    (∃ i t, c'.state = update c.state i ((sys.actor i).recoverAt t (c.state i)).1) :=
  (step_state h).imp_right fun h => h.imp_right fun h => h.resolve_right fun h' => hev h'.1

/-- `step_state` where the environment never restarts the process. -/
theorem step_state_of_noRestarts {env : EnvModel σ} {c c' : SysState sys} {ev : Event σ}
    (h : c.step env ev = some c') (hrestart : env.mayRestart = false) :
    c'.state = c.state ∨
    (∃ i ctx msg, c'.state = update c.state i ((sys.actor i).stepAt ctx (c.state i) msg).1) ∨
    (∃ i t, c'.state = update c.state i ((sys.actor i).recoverAt t (c.state i)).1) :=
  step_state_of_ne_restart h (by rintro rfl; simp [step, hrestart] at h)

theorem startActor_reachable {env : EnvModel σ} {c : SysState sys}
    (h : ∀ j, (sys.actor j).Reachable (c.state j)) (i : σ.Id) :
    ∀ j, (sys.actor j).Reachable ((c.startActor env i).state j) := by
  intro j
  rw [SysState.startActor_state]
  by_cases hj : j = i
  · subst hj
    rw [update_self]
    exact .recover _ (h j)
  · rw [update_of_ne _ _ hj]
    exact h j

/-- At the start, and so after every restart, each actor is in a state it can reach on its
own. -/
theorem init_reachable (env : EnvModel σ) (i : σ.Id) :
    (sys.actor i).Reachable ((init sys env).state i) := by
  unfold SysState.init
  suffices h : ∀ (l : List σ.Id) (c : SysState sys),
      (∀ j, (sys.actor j).Reachable (c.state j)) →
      ∀ j, (sys.actor j).Reachable ((l.foldl (fun c i => c.startActor env i) c).state j) from
    h sys.boot (SysState.blank sys) (fun _ => .init) i
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons k l ih => exact fun c h => ih _ (startActor_reachable h k)

/-- A property of each actor that its own steps and recoveries keep, and that its initial state
has, holds along every run, from whatever state the run starts in, under every environment
model, restarts included. -/
theorem run_inductive {env : EnvModel σ} {P : ∀ i, sys.State i → Prop}
    (hP : ∀ i, (sys.actor i).Inductive (P i)) {c c' : SysState sys} {evs : List (Event σ)}
    (hrun : c.run env evs = some c') (hc : ∀ i, P i (c.state i)) : ∀ i, P i (c'.state i) := by
  induction evs generalizing c with
  | nil =>
    simp only [run, Option.some.injEq] at hrun
    exact hrun ▸ hc
  | cons ev evs ih =>
    simp only [run] at hrun
    cases hstep : c.step env ev with
    | none => simp [hstep] at hrun
    | some c₁ =>
      refine ih (by simpa [hstep] using hrun) fun i => ?_
      rcases step_state hstep with h | ⟨j, ctx, msg, h⟩ | ⟨j, t, h⟩ | ⟨-, h⟩ <;> rw [h]
      · exact hc i
      · by_cases hi : i = j
        · subst hi
          rw [update_self]
          exact (hP i).step ctx _ msg (hc i)
        · rw [update_of_ne _ _ hi]
          exact hc i
      · by_cases hi : i = j
        · subst hi
          rw [update_self]
          exact (hP i).recover t _ (hc i)
        · rw [update_of_ne _ _ hi]
          exact hc i
      · exact (hP i).invariant _ (init_reachable env i)

end SysState

namespace System

/--
In a reachable system state, every actor is in a state it can reach on its own. No other actor,
no message order and no fault takes an actor outside its own reachable states.
-/
theorem Reachable.actor {env : EnvModel σ} {c : SysState sys} (hc : sys.Reachable env c)
    (i : σ.Id) : (sys.actor i).Reachable (c.state i) := by
  induction hc generalizing i with
  | init => exact SysState.init_reachable env i
  | step ev _ hstep ih =>
    rcases SysState.step_state hstep with h | ⟨k, ctx, msg, h⟩ | ⟨k, t, h⟩ | ⟨-, h⟩
    · rw [h]
      exact ih i
    · rw [h]
      by_cases hi : i = k
      · subst hi
        rw [update_self]
        exact .step ctx msg (ih i)
      · rw [update_of_ne _ _ hi]
        exact ih i
    · rw [h]
      by_cases hi : i = k
      · subst hi
        rw [update_self]
        exact .recover t (ih i)
      · rw [update_of_ne _ _ hi]
        exact ih i
    · rw [h]
      exact SysState.init_reachable env i

/--
A per-actor invariant is a system invariant: if `P` holds in every state actor `i` can reach on
its own, it holds for actor `i` in every reachable state of the system, under every environment
model, restarts included (`System.invariant_of_inductive`).
-/
theorem invariant_of_actor (sys : System σ) (i : σ.Id) {P : sys.State i → Prop}
    (h : (sys.actor i).Invariant P) (env : EnvModel σ) :
    sys.Invariant env (fun c => P (c.state i)) :=
  fun _ hc => h _ (hc.actor i)

/-- A per-actor invariant that `init` has and that every step and every recovery keep holds in
every reachable state of every system the actor is part of, under every environment model, and
so across process restarts: a restart puts each actor back in its state at `SysState.init`,
which it reaches from `init` by recovering. -/
theorem invariant_of_inductive (sys : System σ) (i : σ.Id) {P : sys.State i → Prop}
    (h : (sys.actor i).Inductive P) (env : EnvModel σ) :
    sys.Invariant env (fun c => P (c.state i)) :=
  invariant_of_actor sys i h.invariant env

end System

end Lanes
