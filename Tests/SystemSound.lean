/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.Bank
import Tests.Election
import Tests.Gate
import Tests.KV

/-!
`Check.system_sound` applied to the bank, election and gate checks of the test suite, and
`Check.refines_sound` and `Check.refines_traces` to the refinement check of the key-value store:
what their PASS means, as theorems. The kernel cannot run the search, so the PASS itself stays a
hypothesis.
-/

namespace Tests.SystemSound

open Lanes

theorem sum_perm {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Bank

open Tests.Bank Examples.Bank

example (hfailure : reliable.failure = none) (hcomplete : reliable.complete = true) {w : W}
    (hw : Scenario.Reachable Bank2 { driver := Driver.anyOrder transfers } (fun _ => true) w) :
    conserved w.state = true := by
  refine Check.system_sound _ props {} ?_ (fun _ _ _ => rfl) hfailure hcomplete (.head _) hw
  intro p hp a b h
  simp only [props, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine h.eq_of_perm fun w net outbox hnet _ => ?_
    simp only [Check.Property.holds, conserved, total, sum_perm (hnet.map _)]
  · exact h.eq_of_quiet fun _ => rfl
  · exact h.eq_of_quiet fun _ => rfl
  · exact h.eq_of_perm fun _ _ _ _ houtbox => houtbox.any_eq

end Bank

section Election

open Tests.Election Examples.Election

example (hfailure : (check {} 1).failure = none) (hcomplete : (check {} 1).complete = true)
    {w : World (cluster N {}) Unit}
    (hw : Scenario.Reachable (cluster N {}) { env, driver := Driver.silent, maxCrashes := 1 }
      (fun w => (Enum.all (α := N)).all fun a => (w.state.state a).term ≤ 2) w) :
    atMostOneLeaderPerTerm w.state = true := by
  refine Check.system_sound _ _ _ ?_ (fun _ _ h => h.eq_of_quiet fun _ => rfl) hfailure hcomplete
    (.head _) hw
  intro p hp a b h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact h.eq_of_quiet fun _ => rfl

/-- The same of the check run in tasks: the theorem is about the search whatever the option. -/
example (hfailure : (check {} 1 (tasks := true)).failure = none)
    (hcomplete : (check {} 1 (tasks := true)).complete = true) {w : World (cluster N {}) Unit}
    (hw : Scenario.Reachable (cluster N {}) { env, driver := Driver.silent, maxCrashes := 1 }
      (fun w => (Enum.all (α := N)).all fun a => (w.state.state a).term ≤ 2) w) :
    atMostOneLeaderPerTerm w.state = true := by
  refine Check.system_sound _ _ _ ?_ (fun _ _ h => h.eq_of_quiet fun _ => rfl) hfailure hcomplete
    (.head _) hw
  intro p hp a b h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact h.eq_of_quiet fun _ => rfl

end Election

section Gate

open Tests.Gate Lanes.Http

instance (config : GateConfig) : ∀ i, @LawfulBEq
    ((served (Server.system echo) bridge config).State i)
    (System.Inspect.beqState (sys := served (Server.system echo) bridge config) i) := by
  instance_by_cases

def twoRequests : List (ReqId × Request) := [(1, get []), (2, get [])]

example (hfailure : (check {} twoRequests).failure = none)
    (hcomplete : (check {} twoRequests).complete = true)
    {w : World (served (Server.system echo) bridge {}) Client}
    (hw : Scenario.Reachable (served (Server.system echo) bridge {})
      { driver := client twoRequests } (fun _ => true) w) :
    ((w.driver.answered.map (·.1)).eraseDups.length == w.driver.answered.length) = true := by
  refine Check.system_sound _ _ _ ?_ (fun _ _ _ => rfl) hfailure hcomplete (.tail _ (.head _)) hw
  intro p hp a b h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    refine h.eq_of_perm fun w net outbox hnet _ => ?_
    simp only [Check.Property.holds, deadlinesLeftAlone]
    rw [hnet.all_eq]
    rfl
  case inr.inr.inr.inr.inr.inl =>
    refine h.eq_of_quiet fun w => ?_
    simp only [Check.Property.holds, deadlinesFire, World.quiet, SysState.step]
    congr 2
    funext id
    by_cases hfires : (w.state.up gateId && (w.state.timers gateId).contains (.expire id)) = true
    · simp only [hfires, ↓reduceIte, SysState.handle_state]
    · simp only [hfires, Bool.false_eq_true, ↓reduceIte]
  all_goals exact h.eq_of_quiet fun _ => rfl

end Gate

section KV

open Tests.KV Examples.KV

/- Mathlib decides equality of functions on a finite type its own way. The check compared the
store's state with `Enum.funBEq`, so that is the instance these statements must be about. -/
attribute [local instance high] Enum.funBEq

instance (caching : Bool) : ∀ i, @LawfulBEq ((system K V F caching).State i)
    (System.Inspect.beqState (sys := system K V F caching) i) := by
  instance_by_cases

theorem kv_props {p : Check.Property (W false)} (hp : p ∈ props false) {a b : W false}
    (h : World.Equiv {} a b) : p.holds a = p.holds b := by
  simp only [props, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h.holds_refines _
  · exact h.congr fun _ _ _ _ _ houtbox _ => houtbox.any_eq
  · exact h.congr fun _ _ _ _ _ houtbox _ => houtbox.any_eq

example (hfailure : (check false).failure = none) (hcomplete : (check false).complete = true)
    {w : W false}
    (hw : Scenario.Reachable (system K V F false)
      { driver := (spec K V F).monitored (Driver.anyOrder requests) } (fun _ => true) w) :
    w.driver.2.ok = true :=
  Check.refines_sound (σ := sig K V F) (spec K V F) (.of_lawful _) {} 0 (props false) {}
    (fun _ hp _ _ => kv_props hp) (fun _ _ _ => rfl) hfailure hcomplete (.head _) hw

open Cslib in
example (hfailure : (check false).failure = none) (hcomplete : (check false).complete = true)
    {events : List (Event (sig K V F))} {w : W false}
    (hrun : Scenario.Run (system K V F false)
      { driver := (spec K V F).monitored (Driver.anyOrder requests) } (fun _ => true) events w) :
    ∃ a, (spec K V F).spec.lts.SMTr ⟨fun _ => none, 0, 0⟩
      ((events.filterMap Event.visible).map some) a :=
  Check.refines_traces (σ := sig K V F) (spec K V F) (.of_lawful _) {} 0 (props false) {}
    (fun _ hp _ _ => kv_props hp) (fun _ _ _ => rfl) hfailure hcomplete (.head _) hrun

end KV

end Tests.SystemSound
