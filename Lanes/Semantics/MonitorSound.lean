/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.MonitorEquiv
public import Lanes.Check.SystemSound
public import Lanes.Semantics.Monitor

/-!
# A PASS of a refinement check is sound

A refinement check is `Check.system` run under a monitored driver with the property
`Check.refines`. The checker merges worlds whose monitors are `==`, which is not equality: two
monitors are `==` when they hold the same candidates in any order. This file proves that the
merge is safe and concludes what a complete PASS means.

Two monitors are `==` exactly when they hold the same mathematical states (`Monitor.abs`), and
what a monitor holds after an input or an output depends only on what it held before. So a
monitored driver respects `==` (`Driver.Respects`) whenever the driver it wraps does, and
`Check.system_sound_of_respects` applies.

## Main definitions

- `Check.Monitor.abs`: the mathematical states a monitor holds.

## Main statements

- `Check.Monitor.beq_iff_abs_eq`: `==` on monitors is equality of what they hold.
- `Service.monitored_respects`: a monitored driver respects `==` if the driver it wraps does.
- `Check.refines_sound`: after a complete PASS the monitor has a candidate in every world of
  the checked instance.
- `Check.refines_traces`: after a complete PASS the inputs, outputs and deadlines passing of
  every run of the checked instance are a trace of the spec.
-/

@[expose] public section

namespace Lanes

open Cslib

variable {In Out S T : Type} [DecidableEq In] [DecidableEq Out] [BEq S] [LawfulBEq S]

/-- The checker treats two states as the same exactly when they stand for the same mathematical
state. -/
theorem Service.State.equiv_iff_toAbs_eq {a b : Service.State In Out S} :
    a.equiv b = true ↔ a.toAbs = b.toAbs := by
  refine ⟨State.toAbs_eq_of_equiv, fun h => ?_⟩
  simp only [State.toAbs, Abs.mk.injEq, Multiset.coe_eq_coe] at h
  simp [State.equiv, List.isPerm_iff, h.1, h.2.1, h.2.2]

namespace Check.Monitor

open Service

/-- The mathematical states a monitor holds as candidates. -/
def abs (m : Monitor In Out S) : Set (Abs In Out S) :=
  {a | ∃ s ∈ m.candidates, s.toAbs = a}

/-- Inclusion of candidates up to `State.equiv` is inclusion of the states held. -/
theorem within_iff_abs_subset {m₁ m₂ : Monitor In Out S} :
    Within m₁.candidates m₂.candidates ↔ m₁.abs ⊆ m₂.abs := by
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hst⟩ := h s hs
    exact ⟨t, ht, (State.toAbs_eq_of_equiv hst).symm⟩
  · intro h s hs
    obtain ⟨t, ht, hts⟩ := h ⟨s, hs, rfl⟩
    exact ⟨t, ht, State.equiv_iff_toAbs_eq.mpr hts.symm⟩

/-- Two monitors are `==` exactly when they hold the same mathematical states. -/
theorem beq_iff_abs_eq {m₁ m₂ : Monitor In Out S} : (m₁ == m₂) = true ↔ m₁.abs = m₂.abs := by
  rw [beq_iff, within_iff_abs_subset, within_iff_abs_subset]
  exact Set.Subset.antisymm_iff.symm

/-- After an input the monitor holds every state reached, from a state it held, by the input
arriving and then any number of pending inputs taking effect. -/
theorem abs_input (svc : Service In Out S T) (m : Monitor In Out S) (x : In) :
    (m.input svc x).abs =
      {a | ∃ b ∈ m.abs, svc.spec.lts.τSTr { b with pending := x ::ₘ b.pending } a} := by
  ext a
  constructor
  · rintro ⟨st, hst, rfl⟩
    obtain ⟨seed, hseed, hτ⟩ := close_sound svc hst
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hseed
    exact ⟨s.toAbs, ⟨s, hs, rfl⟩, State.toAbs_call s x ▸ hτ⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, hτ⟩
    rw [← State.toAbs_call] at hτ
    exact close_complete svc (List.mem_map_of_mem hs) hτ

/-- After an output the monitor holds every state it held that was waiting to deliver that
output, with the output delivered. -/
theorem abs_output (m : Monitor In Out S) (out : Out) :
    (m.output out).abs =
      {a | ∃ b ∈ m.abs, out ∈ b.outbox ∧ a = { b with outbox := b.outbox.erase out }} := by
  ext a
  constructor
  · rintro ⟨st, hst, rfl⟩
    rcases mem_or_mem_of_mem_insertAll hst with h | h
    · cases h
    · obtain ⟨s, hs, hret⟩ := List.mem_filterMap.mp h
      exact ⟨s.toAbs, ⟨s, hs, rfl⟩, State.ret_eq_some hret⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, hmem, rfl⟩
    obtain ⟨s', hret⟩ := State.ret_of_mem hmem
    have hmem : s' ∈ m.candidates.filterMap (·.ret out) := List.mem_filterMap.mpr ⟨s, hs, hret⟩
    obtain ⟨t, ht, hts⟩ := exists_mem_insertAll_toAbs_eq (known := []) hmem
    exact ⟨t, ht, hts.trans (State.ret_eq_some hret).2⟩

/-- After a deadline passes the monitor holds every state reached, from a state it held in which
the deadline is armed, by its passing and then any number of pending inputs taking effect. -/
theorem abs_fire (svc : Service In Out S T) (m : Monitor In Out S) (t : T) :
    (m.fire svc t).abs =
      {a | ∃ b ∈ m.abs, ∃ b', svc.spec.lts.Tr b (some (.fire t)) b' ∧ svc.spec.lts.τSTr b' a} := by
  ext a
  constructor
  · rintro ⟨st, hst, rfl⟩
    obtain ⟨seed, hseed, hτ⟩ := close_sound svc hst
    obtain ⟨s, hs, hfire⟩ := List.mem_filterMap.mp hseed
    exact ⟨s.toAbs, ⟨s, hs, rfl⟩, seed.toAbs, State.fire_eq_some hfire, hτ⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, b', htr, hτ⟩
    obtain ⟨s', hfire, rfl⟩ := State.exists_fire htr
    exact close_complete svc (List.mem_filterMap.mpr ⟨s, hs, hfire⟩) hτ

/-- `==` monitors stay `==` after the same input. -/
theorem input_congr (svc : Service In Out S T) {m₁ m₂ : Monitor In Out S} (h : (m₁ == m₂) = true)
    (x : In) : (m₁.input svc x == m₂.input svc x) = true := by
  rw [beq_iff_abs_eq] at h ⊢
  rw [abs_input, abs_input, h]

/-- `==` monitors stay `==` after the same output. -/
theorem output_congr {m₁ m₂ : Monitor In Out S} (h : (m₁ == m₂) = true) (out : Out) :
    (m₁.output out == m₂.output out) = true := by
  rw [beq_iff_abs_eq] at h ⊢
  rw [abs_output, abs_output, h]

/-- `==` monitors stay `==` after the same deadline passes. -/
theorem fire_congr (svc : Service In Out S T) {m₁ m₂ : Monitor In Out S} (h : (m₁ == m₂) = true)
    (t : T) : (m₁.fire svc t == m₂.fire svc t) = true := by
  rw [beq_iff_abs_eq] at h ⊢
  rw [abs_fire, abs_fire, h]

end Check.Monitor

variable {σ : Signature}

/-- A monitored driver respects `==` whenever the driver it wraps does. -/
theorem Service.monitored_respects {D : Type} [BEq D] (svc : Service σ.In σ.Out S T)
    {driver : Driver σ D} (h : driver.Respects) {deadlines delivered : Deadlines σ T} :
    (svc.monitored driver deadlines delivered).Respects where
  inputs a b hab x a' ha' := by
    obtain ⟨hd, hm⟩ := prod_beq_iff.mp hab
    obtain ⟨⟨x', d⟩, hmem, heq⟩ := List.mem_map.mp ha'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨d', hmem', hd'⟩ := h.inputs _ _ hd _ _ hmem
    exact ⟨(d', b.2.input svc x'), List.mem_map.mpr ⟨(x', d'), hmem', rfl⟩,
      prod_beq_iff.mpr ⟨hd', Check.Monitor.input_congr svc hm x'⟩⟩
  observe a b out hab := prod_beq_iff.mpr ⟨h.observe _ _ out (prod_beq_iff.mp hab).1,
    Check.Monitor.output_congr (prod_beq_iff.mp hab).2 out⟩
  timeout a b i msg hab := by
    refine prod_beq_iff.mpr ⟨h.timeout _ _ i msg (prod_beq_iff.mp hab).1, ?_⟩
    simp only [Service.monitored]
    cases deadlines i msg with
    | none => exact (prod_beq_iff.mp hab).2
    | some t => exact Check.Monitor.fire_congr svc (prod_beq_iff.mp hab).2 t
  deliver a b i msg hab := by
    refine prod_beq_iff.mpr ⟨h.deliver _ _ i msg (prod_beq_iff.mp hab).1, ?_⟩
    simp only [Service.monitored]
    cases delivered i msg with
    | none => exact (prod_beq_iff.mp hab).2
    | some t => exact Check.Monitor.fire_congr svc (prod_beq_iff.mp hab).2 t

namespace Check

variable [σ.Inspect] {sys : System σ} [sys.Inspect] {D : Type} [BEq D]

omit [σ.Inspect] [sys.Inspect] [BEq D] [LawfulBEq S] in
/-- The monitor of a world is the monitor after the visible events of any run of the instance
that ends in that world. -/
theorem Monitor.eq_after_of_run [Enum σ.Id] {svc : Service σ.In σ.Out S T}
    {driver : Driver σ D} {deadlines delivered : Deadlines σ T} {env : EnvModel σ}
    {maxCrashes : Nat} {constraint : World sys (D × Monitor σ.In σ.Out S) → Bool}
    {events : List (Event σ)} {w : World sys (D × Monitor σ.In σ.Out S)}
    (h : Scenario.Run sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes } constraint events w) :
    w.driver.2 = Monitor.after svc (events.filterMap (Event.timed deadlines delivered)) := by
  induction h with
  | init => rfl
  | @step events w w' ev _ hnext _ ih =>
    rw [List.filterMap_append]
    obtain ⟨c, -, hw'⟩ := World.mem_next_iff.mp hnext
    cases ev with
    | input x =>
      obtain ⟨d, hd, rfl⟩ := hw'
      obtain ⟨⟨x', d'⟩, -, heq⟩ := List.mem_map.mp hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp [after_concat, observe, ih]
    | output out =>
      subst hw'
      simp [after_concat, observe, ih, Service.monitored]
    | timeout i msg =>
      subst hw'
      cases ht : deadlines i msg with
      | none => simp [Service.monitored, ht, ih]
      | some t => simp [Service.monitored, ht, ih, after_concat, observe]
    | deliver e | duplicate e =>
      subst hw'
      cases ht : delivered e.dst e.msg with
      | none => simp [Service.monitored, ht, ih]
      | some t => simp [Service.monitored, ht, ih, after_concat, observe]
    | crash i =>
      obtain ⟨-, rfl⟩ := hw'
      rw [show List.filterMap (Event.timed deadlines delivered) [Event.crash i] = [] from rfl,
        List.append_nil]
      exact ih
    | drop e | start i =>
      subst hw'
      rw [show List.filterMap (Event.timed deadlines delivered) [_] = [] from rfl,
        List.append_nil]
      exact ih

variable [Hashable D] [EquivBEq D] [Hashable S]
  [∀ i, LawfulBEq (sys.State i)]

/--
A complete PASS of a refinement check is sound: in every world of the checked instance the
monitor still has a candidate.

Actor states and the spec's state must compare with `==` exactly when they are equal. The state
of the wrapped driver needs only an equivalence `==` that the driver respects. The properties
and the constraint must not tell merged worlds apart; for the refinement property itself that
is `World.Equiv.holds_refines`.
-/
theorem refines_sound (svc : Service σ.In σ.Out S T) {driver : Driver σ D}
    (hdriver : driver.Respects) {deadlines delivered : Deadlines σ T} (env : EnvModel σ)
    (maxCrashes : Nat)
    (props : List (Property (World sys (D × Monitor σ.In σ.Out S))))
    (opts : Options (World sys (D × Monitor σ.In σ.Out S)))
    (hprops : ∀ p ∈ props, ∀ a b, World.Equiv env a b → p.holds a = p.holds b)
    (hconstraint : ∀ a b, World.Equiv env a b → opts.constraint a = opts.constraint b)
    (hfailure : (system sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes } props
      opts).failure = none)
    (hcomplete : (system sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes } props
      opts).complete = true)
    {name : String} (hrefines : refines name ∈ props) {w : World sys (D × Monitor σ.In σ.Out S)}
    (hw : Scenario.Reachable sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes } opts.constraint w) :
    w.driver.2.ok = true :=
  system_sound_of_respects _ (svc.monitored_respects hdriver) props opts hprops hconstraint
    hfailure hcomplete hrefines hw

/--
What a complete PASS of a refinement check means in the spec's terms: the inputs, outputs and
deadlines passing of every run of the checked instance, in the order they happened, are a trace
of the spec. The hypotheses are those of `refines_sound`.
-/
theorem refines_traces (svc : Service σ.In σ.Out S T) {driver : Driver σ D}
    (hdriver : driver.Respects) {deadlines delivered : Deadlines σ T} (env : EnvModel σ)
    (maxCrashes : Nat)
    (props : List (Property (World sys (D × Monitor σ.In σ.Out S))))
    (opts : Options (World sys (D × Monitor σ.In σ.Out S)))
    (hprops : ∀ p ∈ props, ∀ a b, World.Equiv env a b → p.holds a = p.holds b)
    (hconstraint : ∀ a b, World.Equiv env a b → opts.constraint a = opts.constraint b)
    (hfailure : (system sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes } props
      opts).failure = none)
    (hcomplete : (system sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes } props
      opts).complete = true)
    {name : String} (hrefines : refines name ∈ props) {events : List (Event σ)}
    {w : World sys (D × Monitor σ.In σ.Out S)}
    (hrun : Scenario.Run sys
      { env, driver := svc.monitored driver deadlines delivered, maxCrashes }
      opts.constraint events w) :
    ∃ a, svc.spec.lts.SMTr ⟨svc.init, 0, 0⟩
      ((events.filterMap (Event.timed deadlines delivered)).map some) a := by
  rw [← Monitor.ok_iff, ← Monitor.eq_after_of_run hrun]
  exact refines_sound svc hdriver env maxCrashes props opts hprops hconstraint hfailure hcomplete
    hrefines hrun.reachable

end Check

end Lanes
