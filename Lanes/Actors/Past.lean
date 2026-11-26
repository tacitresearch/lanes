/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Ghost
public import Lanes.Actors.Monotone

/-!
# The ghost that remembers every state

`Ghost.past` gives each actor the list of the states it has left, by a step or by a recovery.
With the state it is in now that is everything the actor has ever been (`SysState.seen`), and it
only grows. A proof that needs the past ("this node voted for that candidate in term 3", "this
log was once a leader's") states it over `seen`, and several such proofs share the one ghost, so
their invariants can be used together.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

abbrev Ghost.past (sys : System σ) : Ghost sys where
  Hist i := List (sys.State i)
  init _ := []
  step _ hist s _ := s :: hist
  recover _ hist s := s :: hist

abbrev System.withPast (sys : System σ) : System σ :=
  sys.withGhost (.past sys)

namespace SysState

variable {sys : System σ}

/-- Every state actor `i` has been in, the present one first. -/
def seen (c : SysState sys.withPast) (i : σ.Id) : List (sys.State i) :=
  (c.state i).1 :: (c.state i).2

theorem mem_seen_self (c : SysState sys.withPast) (i : σ.Id) : (c.state i).1 ∈ c.seen i :=
  List.mem_cons_self

theorem seen_blank (sys : System σ) (i : σ.Id) :
    (SysState.blank sys.withPast).seen i = [(sys.actor i).init] := rfl

theorem Below.seen {c' c : SysState sys.withPast} (h : c'.Below c) (i : σ.Id) :
    c'.seen i = c.seen i := by
  simp only [SysState.seen, h.state]

variable {c : SysState sys.withPast} {i : σ.Id} {s' : sys.State i} {effs : List (Effect σ i)}

/-- The state after a step or a recovery of actor `i`, written with `seen`. Both are an instance
by `rfl`, with `s'` and `effs` what the actor of `sys` returns. -/
theorem seen_grow_self : (c.grow i ((s', c.seen i), effs)).seen i = s' :: c.seen i := by
  simp [seen]

theorem seen_grow_of_ne {j : σ.Id} (h : j ≠ i) :
    (c.grow i ((s', c.seen i), effs)).seen j = c.seen j := by
  simp [seen, h]

theorem mem_seen_grow_of_mem {j : σ.Id} {p : sys.State j} (h : p ∈ c.seen j) :
    p ∈ (c.grow i ((s', c.seen i), effs)).seen j := by
  by_cases hj : j = i
  · subst hj
    rw [seen_grow_self]
    exact List.mem_cons_of_mem _ h
  · rwa [seen_grow_of_ne hj]

/-- Where every actor has states of one type, as the nodes of a cluster do: after a step or a
recovery of actor `i`, an actor has been in the states it had been in, and `i` in the new one. -/
theorem mem_seen_grow {S : Type} {actor : (i : σ.Id) → σ.Actor i S}
    {accept : σ.In → (i : σ.Id) × σ.Msg i} {boot : List σ.Id}
    {c : SysState (System.withPast ⟨fun _ => S, actor, accept, boot⟩)} {i j : σ.Id} {s' p : S}
    {effs : List (Effect σ i)} :
    p ∈ (c.grow i ((s', c.seen i), effs)).seen j ↔ p ∈ c.seen j ∨ (j = i ∧ p = s') := by
  by_cases hj : j = i
  · subst hj
    rw [seen_grow_self]
    simp [or_comm]
  · rw [seen_grow_of_ne hj]
    simp [hj]

/-- No event takes a state out of an actor's past. -/
theorem mem_seen_step {env : EnvModel σ} {c c' : SysState sys.withPast} {ev : Event σ}
    (h : c.step env ev = some c') {i : σ.Id} {p : sys.State i} (hp : p ∈ c.seen i) :
    p ∈ c'.seen i := by
  rcases step_state h with hs | ⟨k, msg, hs⟩ | ⟨k, hs⟩ <;> simp only [seen, hs]
  · exact hp
  · by_cases hik : i = k
    · subst hik
      rw [update_self]
      exact List.mem_cons_of_mem _ hp
    · rwa [update_of_ne _ _ hik]
  · by_cases hik : i = k
    · subst hik
      rw [update_self]
      exact List.mem_cons_of_mem _ hp
    · rwa [update_of_ne _ _ hik]

theorem mem_seen_run {env : EnvModel σ} {c c' : SysState sys.withPast} {evs : List (Event σ)}
    (h : c.run env evs = some c') {i : σ.Id} {p : sys.State i} (hp : p ∈ c.seen i) :
    p ∈ c'.seen i := by
  induction evs generalizing c with
  | nil => simp only [run, Option.some.injEq] at h; exact h ▸ hp
  | cons ev evs ih =>
    simp only [run] at h
    cases hstep : c.step env ev with
    | none => simp [hstep] at h
    | some c₁ => exact ih (by simpa [hstep] using h) (mem_seen_step hstep hp)

end SysState

/-- Two points of a run of the real system, with the past: what an actor was at the earlier it
has been at the later. A statement about two times is proved from an invariant over `seen`
through this. -/
theorem System.Reachable.exists_past {sys : System σ} {env : EnvModel σ} {c c' : SysState sys}
    {evs : List (Event σ)} (h : sys.Reachable env c) (hrun : c.run env evs = some c') :
    ∃ d' : SysState sys.withPast, sys.withPast.Reachable env d' ∧ d'.erase = c' ∧
      ∀ i, c.state i ∈ d'.seen i := by
  obtain ⟨d, d', hreach, rfl, hrun', rfl⟩ := h.exists_ghost_run (.past sys) hrun
  exact ⟨d', hreach.run hrun', rfl, fun i => SysState.mem_seen_run hrun' (d.mem_seen_self i)⟩

end Lanes
