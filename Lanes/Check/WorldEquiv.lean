/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Scheduler
public import Lanes.Check.Complete
public import Lanes.Check.Equiv

/-!
`World.next` is what the checker and the scheduler explore: the system's enabled events, the
driver's inputs and a crash budget. This file lifts `SysState.Equiv.step` to it: worlds the
checker merges have the same next steps, up to merging.
-/

public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {D : Type}

structure World.Equiv (env : EnvModel σ) (a b : World sys D) : Prop where
  state : SysState.Equiv env a.state b.state
  driver : a.driver = b.driver
  crashes : a.crashes = b.crashes

/-- Worlds the checker merges take the same steps to worlds it merges. -/
theorem World.Equiv.next [Enum σ.Id] {sc : Scenario σ D} {a b a' : World sys D} {ev : Event σ}
    (h : World.Equiv sc.env a b) (hmem : (ev, a') ∈ a.next sc) :
    ∃ b', (ev, b') ∈ b.next sc ∧ World.Equiv sc.env a' b' := by
  obtain ⟨hstate, hdriver, hcrashes⟩ := h
  simp only [World.next, List.mem_append, List.mem_filterMap] at hmem ⊢
  rcases hmem with ⟨⟨ev₀, c⟩, hsucc, hsome⟩ | ⟨⟨x, d⟩, hinput, hsome⟩
  · obtain ⟨hstep, hnotInput⟩ := SysState.mem_successors_iff.mp hsucc
    obtain ⟨c₂, hstep₂, hequiv⟩ := hstate.step hstep
    have hsucc₂ := SysState.mem_successors_iff.mpr ⟨hstep₂, hnotInput⟩
    cases ev₀ with
    | input x => exact absurd rfl (hnotInput x)
    | output out =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨_, .inl ⟨(_, c₂), hsucc₂, rfl⟩, by simpa using hequiv, by simp [hdriver], hcrashes⟩
    | crash i =>
      simp only at hsome
      split at hsome
      · next hbudget =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        refine ⟨_, .inl ⟨(_, c₂), hsucc₂, by simp [← hcrashes, hbudget]; rfl⟩, ?_⟩
        exact ⟨by simpa using hequiv, hdriver, by simp [hcrashes]⟩
      · exact absurd hsome (by simp)
    | deliver e | duplicate e | drop e | timeout i msg | start i =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨_, .inl ⟨(_, c₂), hsucc₂, rfl⟩, by simpa using hequiv, hdriver, hcrashes⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨c, hstep, rfl, rfl⟩ := hsome
    obtain ⟨c₂, hstep₂, hequiv⟩ := hstate.step hstep
    refine ⟨_, .inr ⟨(x, d), hdriver ▸ hinput, by simp [hstep₂]; rfl⟩, ?_⟩
    exact ⟨by simpa using hequiv, rfl, hcrashes⟩

end Lanes
