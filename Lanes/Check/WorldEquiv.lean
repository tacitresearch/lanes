/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Scheduler
public import Lanes.Check.Complete
public import Lanes.Proof.Equiv

/-!
`World.next` is what the checker and the scheduler explore: the system's enabled events, the
driver's inputs and a crash budget. This file lifts `SysState.Equiv.step` to it: worlds the
checker merges have the same next steps, up to merging.

The checker compares driver states with `==`, which need not be equality: a monitor is a set of
candidates kept as a list. `Driver.Respects` is what the driver must then satisfy.
-/

public section

namespace Lanes

variable {σ : Signature} {sys : System σ} {D : Type}

/-- The driver cannot tell `==` states apart: they offer the same inputs, leading to `==`
states, and stay `==` after seeing an output, a timer fire or a message handed over. -/
structure Driver.Respects [BEq D] (driver : Driver σ D) : Prop where
  inputs : ∀ a b, (a == b) = true → ∀ x a', (x, a') ∈ driver.inputs a →
    ∃ b', (x, b') ∈ driver.inputs b ∧ (a' == b') = true
  observe : ∀ a b out, (a == b) = true → (driver.observe a out == driver.observe b out) = true
  timeout : ∀ a b i msg, (a == b) = true →
    (driver.timeout a i msg == driver.timeout b i msg) = true
  deliver : ∀ a b i msg, (a == b) = true →
    (driver.deliver a i msg == driver.deliver b i msg) = true

theorem Driver.Respects.of_lawful [BEq D] [LawfulBEq D] (driver : Driver σ D) :
    driver.Respects where
  inputs _ _ hab _ a' ha' := ⟨a', eq_of_beq hab ▸ ha', BEq.rfl⟩
  observe _ _ _ hab := eq_of_beq hab ▸ BEq.rfl
  timeout _ _ _ _ hab := eq_of_beq hab ▸ BEq.rfl
  deliver _ _ _ _ hab := eq_of_beq hab ▸ BEq.rfl

structure World.Equiv [BEq D] (env : EnvModel σ) (a b : World sys D) : Prop where
  state : SysState.Equiv env a.state b.state
  driver : (a.driver == b.driver) = true
  crashes : a.crashes = b.crashes
  restarts : a.restarts = b.restarts

/-- Worlds the checker merges take the same steps to worlds it merges. -/
theorem World.Equiv.next [Enum σ.Id] [BEq D] {sc : Scenario σ D} (hresp : sc.driver.Respects)
    {a b a' : World sys D} {ev : Event σ} (h : World.Equiv sc.env a b)
    (hmem : (ev, a') ∈ a.next sc) : ∃ b', (ev, b') ∈ b.next sc ∧ World.Equiv sc.env a' b' := by
  obtain ⟨hstate, hdriver, hcrashes, hrestarts⟩ := h
  simp only [World.next, List.mem_append, List.mem_filterMap, List.mem_map, List.mem_filter]
    at hmem ⊢
  rcases hmem with (⟨⟨ev₀, c⟩, hsucc, hsome⟩ | ⟨⟨x, d⟩, hinput, hsome⟩) | ⟨m, ⟨hm, hlater⟩, hsome⟩
  · obtain ⟨hstep, hnotInput, hnotTick⟩ := SysState.mem_successors_iff.mp hsucc
    obtain ⟨c₂, hstep₂, hequiv⟩ := hstate.step hstep
    have hsucc₂ := SysState.mem_successors_iff.mpr ⟨hstep₂, hnotInput, hnotTick⟩
    cases ev₀ with
    | input x => exact absurd rfl (hnotInput x)
    | tick m => exact absurd rfl (hnotTick m)
    | output out =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨_, .inl (.inl ⟨(_, c₂), hsucc₂, rfl⟩), by simpa using hequiv,
        hresp.observe _ _ out hdriver, hcrashes, hrestarts⟩
    | crash i =>
      simp only at hsome
      split at hsome
      · next hbudget =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        refine ⟨_, .inl (.inl ⟨(_, c₂), hsucc₂, by simp [← hcrashes, hbudget]; rfl⟩), ?_⟩
        exact ⟨by simpa using hequiv, hdriver, by simp [hcrashes], hrestarts⟩
      · exact absurd hsome (by simp)
    | restart =>
      simp only at hsome
      split at hsome
      · next hbudget =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        refine ⟨_, .inl (.inl ⟨(_, c₂), hsucc₂, by simp [← hrestarts, hbudget]; rfl⟩), ?_⟩
        exact ⟨by simpa using hequiv, hdriver, hcrashes, by simp [hrestarts]⟩
      · exact absurd hsome (by simp)
    | timeout i msg =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨_, .inl (.inl ⟨(_, c₂), hsucc₂, rfl⟩), by simpa using hequiv,
        hresp.timeout _ _ i msg hdriver, hcrashes, hrestarts⟩
    | deliver e | duplicate e =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨_, .inl (.inl ⟨(_, c₂), hsucc₂, rfl⟩), by simpa using hequiv,
        hresp.deliver _ _ e.dst e.msg hdriver, hcrashes, hrestarts⟩
    | drop e | start i =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨_, .inl (.inl ⟨(_, c₂), hsucc₂, rfl⟩), by simpa using hequiv, hdriver, hcrashes,
        hrestarts⟩
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨c, hstep, rfl, rfl⟩ := hsome
    obtain ⟨c₂, hstep₂, hequiv⟩ := hstate.step hstep
    obtain ⟨d₂, hinput₂, hd⟩ := hresp.inputs _ _ hdriver x d hinput
    refine ⟨_, .inl (.inr ⟨(x, d₂), hinput₂, by simp [hstep₂]; rfl⟩), ?_⟩
    exact ⟨by simpa using hequiv, hd, hcrashes, hrestarts⟩
  · simp only [Prod.mk.injEq] at hsome
    obtain ⟨rfl, rfl⟩ := hsome
    refine ⟨_, .inr ⟨m, ⟨hm, by rw [← hstate.clock]; exact hlater⟩, rfl⟩, ?_⟩
    exact ⟨⟨hstate.state, hstate.up, hstate.timers, hstate.net, hstate.outbox, rfl⟩, hdriver,
      hcrashes, hrestarts⟩

end Lanes
