/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.World

/-!
# From one actor to the whole system

Frame lemmas for `SysState.step`, and the lifting theorem: whatever is proved about one actor in
isolation holds for that actor in every reachable state of every system it is part of, under
every environment model. This is what makes per-actor proofs worth writing: no other actor, no
message order and no fault can break them.

## Main statements

- `SysState.step_state`: an event changes the private state of at most one actor, and only by
  that actor's own `step` or `recover`.
- `System.Reachable.actor`: each actor's state in a reachable system state is reachable for that
  actor alone.
- `System.invariant_of_actor`: a per-actor invariant is a system invariant.
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

@[simp] theorem down_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id) :
    (c.down env i).state = c.state := rfl

@[simp] theorem settle_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id)
    (r : sys.State i × List (Effect σ i)) :
    (c.settle env i r).state = update c.state i r.1 := by
  unfold settle
  split <;> simp

@[simp] theorem handle_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id) (msg : σ.Msg i) :
    (c.handle env i msg).state = update c.state i ((sys.actor i).step (c.state i) msg).1 := by
  simp [handle]

@[simp] theorem startActor_state (env : EnvModel σ) (c : SysState sys) (i : σ.Id) :
    (c.startActor env i).state = update c.state i ((sys.actor i).recover (c.state i)).1 := by
  simp [startActor]

/--
How one event changes actor states: not at all, or one actor `i` moves by its own `step` on some
message, or one actor `i` moves by its own `recover`.
-/
theorem step_state {env : EnvModel σ} {c c' : SysState sys} {ev : Event σ}
    (h : c.step env ev = some c') :
    c'.state = c.state ∨
    (∃ i msg, c'.state = update c.state i ((sys.actor i).step (c.state i) msg).1) ∨
    (∃ i, c'.state = update c.state i ((sys.actor i).recover (c.state i)).1) := by
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
      exact .inr (.inl ⟨e.dst, e.msg, by simp⟩)
    · contradiction
  | duplicate e =>
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact .inr (.inl ⟨e.dst, e.msg, by simp⟩)
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
      exact .inr (.inl ⟨i, msg, by simp⟩)
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
      exact .inr (.inr ⟨i, by simp⟩)
    · contradiction

end SysState

namespace System

/-- Reachability of each actor's own state is preserved by starting an actor. -/
private theorem actor_reachable_startActor {env : EnvModel σ} {c : SysState sys}
    (h : ∀ j, (sys.actor j).Reachable (c.state j)) (i : σ.Id) :
    ∀ j, (sys.actor j).Reachable ((c.startActor env i).state j) := by
  intro j
  rw [SysState.startActor_state]
  by_cases hj : j = i
  · subst hj
    rw [update_self]
    exact .recover (h j)
  · rw [update_of_ne _ _ hj]
    exact h j

/--
In a reachable system state, every actor is in a state it can reach on its own. No other actor,
no message order and no fault takes an actor outside its own reachable states.
-/
theorem Reachable.actor {env : EnvModel σ} {c : SysState sys} (hc : sys.Reachable env c)
    (i : σ.Id) : (sys.actor i).Reachable (c.state i) := by
  induction hc generalizing i with
  | init =>
    unfold SysState.init
    suffices h : ∀ (l : List σ.Id) (c : SysState sys),
        (∀ j, (sys.actor j).Reachable (c.state j)) →
        ∀ j, (sys.actor j).Reachable ((l.foldl (fun c i => c.startActor env i) c).state j) from
      h sys.boot (SysState.blank sys) (fun _ => .init) i
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons k l ih => exact fun c h => ih _ (actor_reachable_startActor h k)
  | step ev _ hstep ih =>
    rcases SysState.step_state hstep with h | ⟨k, msg, h⟩ | ⟨k, h⟩
    · rw [h]
      exact ih i
    · rw [h]
      by_cases hi : i = k
      · subst hi
        rw [update_self]
        exact .step msg (ih i)
      · rw [update_of_ne _ _ hi]
        exact ih i
    · rw [h]
      by_cases hi : i = k
      · subst hi
        rw [update_self]
        exact .recover (ih i)
      · rw [update_of_ne _ _ hi]
        exact ih i

/--
A per-actor invariant is a system invariant: if `P` holds in every state actor `i` can reach on
its own, it holds for actor `i` in every reachable state of the system, under every environment
model.
-/
theorem invariant_of_actor (sys : System σ) (i : σ.Id) {P : sys.State i → Prop}
    (h : (sys.actor i).Invariant P) (env : EnvModel σ) :
    sys.Invariant env (fun c => P (c.state i)) :=
  fun _ hc => h _ (hc.actor i)

end System

end Lanes
