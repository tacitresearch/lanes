/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Inspect
public import Lanes.Core.Step

/-!
The checker explores a state through `SysState.successors`. `step_of_mem_successors` says it
only follows real steps. This file proves the other direction: it misses none. Inputs are the
one exception, by design: they are the driver's choice.
-/

public section

namespace Lanes.SysState

variable {σ : Signature} {sys : System σ} [Enum σ.Id] {env : EnvModel σ} {c c' : SysState sys}

theorem mem_candidates {ev : Event σ} (hstep : c.step env ev = some c')
    (hinput : ∀ x, ev ≠ .input x) : ev ∈ c.candidates := by
  simp only [candidates, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_eraseDups]
  cases ev with
  | input x => exact absurd rfl (hinput x)
  | deliver e =>
    exact .inl (.inl (.inl (.inl (.inl (.inl
      ⟨e, mem_of_deliverable (step_deliver.mp hstep).2.1, rfl⟩)))))
  | duplicate e =>
    exact .inl (.inl (.inl (.inl (.inl (.inr
      ⟨e, mem_of_deliverable (step_duplicate.mp hstep).2.2.1, rfl⟩)))))
  | drop e => exact .inl (.inl (.inl (.inl (.inr ⟨e, (step_drop.mp hstep).2.1, rfl⟩))))
  | timeout i msg =>
    exact .inl (.inl (.inl (.inr ⟨i, Enum.complete i, msg, (step_timeout.mp hstep).2.1, rfl⟩)))
  | output out => exact .inl (.inl (.inr ⟨out, (step_output.mp hstep).1, rfl⟩))
  | crash i => exact .inl (.inr ⟨i, Enum.complete i, rfl⟩)
  | start i => exact .inr ⟨i, Enum.complete i, rfl⟩

/-- The checker misses no step: every enabled event other than an input is a listed successor. -/
theorem mem_successors {ev : Event σ} (hstep : c.step env ev = some c')
    (hinput : ∀ x, ev ≠ .input x) : (ev, c') ∈ c.successors env := by
  simp only [successors, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  exact ⟨ev, mem_candidates hstep hinput, c', hstep, rfl, rfl⟩

/-- The listed successors are exactly the enabled events other than inputs. -/
theorem mem_successors_iff {ev : Event σ} :
    (ev, c') ∈ c.successors env ↔ c.step env ev = some c' ∧ ∀ x, ev ≠ .input x := by
  refine ⟨fun h => ⟨step_of_mem_successors h, ?_⟩, fun h => mem_successors h.1 h.2⟩
  intro x hx
  subst hx
  simp only [successors, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨ev, hmem, _, _, rfl, _⟩ := h
  simp [candidates] at hmem

end Lanes.SysState
