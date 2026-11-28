/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Proofs
import Tests.Reduce

/-!
What a PASS of `Tests.Reduce`'s reduced check means: by `Check.systemReduced_sound`, the
properties hold in every world of the plain scenario. Sorting the log is a reduction because the
driver, and the properties, only ever read the log as a set (`Driver.Simulation`). The kernel
cannot run the search, so the PASS stays a hypothesis.
-/

namespace Tests.ReduceProofs

open Lanes Tests.Reduce

/-- The driver's states with the same inputs to send and the same outputs seen, in any order. -/
def Same (a b : D) : Prop :=
  a.1 = b.1 ∧ a.2.Perm b.2

theorem simulation : (driver inputs).Simulation Same where
  inputs a b h x a' ha' := by
    obtain ⟨⟨x₀, rest⟩, hmem, heq⟩ := List.mem_map.mp ha'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨(rest, b.2), List.mem_map.mpr ⟨(x₀, rest), h.1 ▸ hmem, rfl⟩, rfl, h.2⟩
  observe a b out h := ⟨h.1, h.2.cons out⟩
  timeout _ _ _ _ h := h
  deliver _ _ _ _ h := h

theorem sees {a b : World echo D} (h : Check.World.SameUpTo Same a b) :
    a.driver.2.Perm b.driver.2 ∧ a.driver.1 = b.driver.1 :=
  ⟨h.2.1.2, h.2.1.1⟩

theorem reduction : Check.World.Reduction scenario (fun _ => true) props canon
    (Check.World.SameUpTo Same) :=
  Check.World.Reduction.ofDriver (sc := scenario) (props := props) (fun d => (d.1, d.2.mergeSort)) simulation
    (fun d => ⟨rfl, (List.mergeSort_perm _ _).symm⟩) (fun h => ⟨h.1.symm, h.2.symm⟩)
    (fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩) (fun _ => rfl) fun p hp {a b} h => by
      obtain ⟨hperm, hrest⟩ := sees h
      simp only [props, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · refine Bool.eq_iff_iff.mpr ?_
        change (a.driver.2.all (inputs.contains ·)) = true ↔ (b.driver.2.all (inputs.contains ·)) = true
        simp only [List.all_eq_true]
        exact ⟨fun hall x hx => hall x (hperm.mem_iff.mpr hx),
          fun hall x hx => hall x (hperm.mem_iff.mp hx)⟩
      · simp [Check.Property.holds, hperm.length_eq, hrest]
      · simp [Check.Property.holds, hperm.length_eq]

/-- A complete PASS of the reduced check: every world of the plain scenario has seen only inputs,
and no more outputs than inputs sent. -/
theorem reduced_pass
    (hfailure : (Check.systemReduced echo scenario canon props).failure = none)
    (hcomplete : (Check.systemReduced echo scenario canon props).complete = true)
    {w : World echo D} (hw : scenario.Reachable echo (fun _ => true) w) :
    w.driver.2.all (inputs.contains ·) = true :=
  Check.systemReduced_sound scenario (.of_lawful _) canon props {} reduction
    (fun a b h => ⟨h.state, by simp [canon, eq_of_beq h.driver], h.crashes, h.restarts⟩)
    (fun p hp a b h => by
      have hd := eq_of_beq h.driver
      simp only [props, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [Check.Property.holds, hd])
    (fun _ _ _ => rfl)
    hfailure hcomplete (.head _) hw

end Tests.ReduceProofs
