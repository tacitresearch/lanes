/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Check

/-!
# What a PASS of `raftCheck` means

`Check.system_sound_of_respects`, `Check.refines_sound` and `Check.refines_traces` applied to
the checks of `Check.lean`: for every `Config`, environment model, list of requests and bounds,
and every list of properties that give one verdict on states the checker merges. The kernel
cannot run the search, so the PASS itself stays a hypothesis.

The checker merges states that differ in the order of messages in flight and of answers not
yet handed over, and compares nodes with `==`. So the theorems need `==` on a node to be
equality (`LawfulBEq (Node N C M)`, in `RaftKV/Protocol.lean`), and every property and the bounds
to give the same verdict on merged states (`Respects`: `props_respect`, `auxiliary_respect` and
one for each witness a check adds; `bounds_respect`).
-/

namespace RaftKV

open Lanes

/- Mathlib decides equality of functions on a finite type its own way. The check compared the
map with `Enum.funBEq`, so that is the instance these statements must be about. -/
attribute [local instance high] Enum.funBEq

instance (config : Config) : ∀ i, @LawfulBEq ((cluster N config (store K V)).State i)
    (System.Inspect.beqState (sys := cluster N config (store K V)) i) :=
  fun _ => inferInstanceAs (LawfulBEq (Node N C M))

variable {config : Config} {env : EnvModel (sig N C R)}

/-- `p` gives one verdict on states the checker merges. -/
def Respects (env : EnvModel (sig N C R)) (p : Check.Property (W config)) : Prop :=
  ∀ a b : W config, World.Equiv env a b → p.holds a = p.holds b

/-- Proves `Respects` of a property that reads messages in flight and answers waiting only
through `all` and `any`. -/
local macro "respects" : tactic => `(tactic|
  (intro a b h
   first
    | exact h.congr fun _ _ _ _ _ _ _ => rfl
    | exact h.congr fun _ _ _ _ hnet _ _ => hnet.all_eq
    | exact h.congr fun _ _ _ _ hnet _ _ => hnet.any_eq
    | exact h.congr fun _ _ _ _ _ houtbox _ => houtbox.any_eq))

theorem props_respect : ∀ p ∈ props config, Respects env p := by
  intro p hp
  simp only [props, safety, witnesses, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    rfl | rfl | rfl) | rfl
  · exact fun _ _ h => h.holds_refines _
  all_goals respects

theorem auxiliary_respect : ∀ p ∈ auxiliary config, Respects env p := by
  intro p hp
  simp only [auxiliary, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> respects

theorem candidateWithLog_respect : Respects env (candidateWithLog config) := by respects

theorem partBatch_respect : Respects env (partBatch config) := by respects

theorem pastTheEnd_respect : Respects env (pastTheEnd config) := by respects

theorem bounds_respect (bounds : Bounds) {a b : W config} (h : World.Equiv env a b) :
    bounds.holds a = bounds.holds b :=
  h.congr fun _ _ _ _ hnet _ _ => by simp only [Bounds.holds, hnet.length_eq]

/-- The instance a check explores. -/
abbrev scenario (env : EnvModel (sig N C R)) (requests : List (Request N C)) (bounds : Bounds) :
    Scenario (sig N C R) (List (Request N C) × Check.Monitor (Request N C) (Response R) M) :=
  { env, driver := (spec (store K V)).monitored (Driver.anyOrder requests)
    maxCrashes := bounds.maxCrashes }

section Pass

variable (config) (env) (requests : List (Request N C)) (bounds : Bounds)
  (properties : List (Check.Property (W config))) (hrespect : ∀ p ∈ properties, Respects env p)
  (hfailure : (check config env requests bounds properties).failure = none)
  (hcomplete : (check config env requests bounds properties).complete = true)

include hrespect hfailure hcomplete

/-- After a complete PASS, every `always` property that was checked holds in every state the
instance reaches within its bounds. -/
theorem always_of_pass {name : String} {p : W config → Bool} (hp : .always name p ∈ properties)
    {w : W config}
    (hw : (scenario env requests bounds).Reachable (cluster N config (store K V)) bounds.holds w) :
    p w = true :=
  Check.system_sound_of_respects (scenario env requests bounds)
    ((spec (store K V)).monitored_respects (σ := sig N C R) (.of_lawful _)) properties
    { constraint := bounds.holds } hrespect (fun _ _ => bounds_respect bounds) hfailure hcomplete
    hp hw

/-- After a complete PASS of a check with the monitor, the monitor still has a state of the map
that explains what the cluster has taken and answered, in every state the instance reaches. -/
theorem monitor_of_pass {name : String} (hrefines : Check.refines name ∈ properties)
    {w : W config}
    (hw : (scenario env requests bounds).Reachable (cluster N config (store K V)) bounds.holds w) :
    w.driver.2.ok = true :=
  Check.refines_sound (σ := sig N C R) (spec (store K V)) (.of_lawful _) env bounds.maxCrashes
    properties { constraint := bounds.holds } hrespect (fun _ _ => bounds_respect bounds) hfailure
    hcomplete hrefines hw

/-- After a complete PASS of a check with the monitor, the inputs and outputs of every run of
the instance within its bounds, in the order they happened, are a trace of the map:
`spec (store K V)`. -/
theorem traces_of_pass {name : String} (hrefines : Check.refines name ∈ properties)
    {events : List (Event (sig N C R))} {w : W config}
    (hrun : (scenario env requests bounds).Run (cluster N config (store K V)) bounds.holds
      events w) :
    ∃ a, (spec (store K V)).spec.lts.SMTr ⟨fun _ => none, 0, 0⟩
      ((events.filterMap Event.visible).map some) a :=
  Check.refines_traces (σ := sig N C R) (spec (store K V)) (.of_lawful _) env bounds.maxCrashes
    properties { constraint := bounds.holds } hrespect (fun _ _ => bounds_respect bounds) hfailure
    hcomplete hrefines hrun

end Pass

/-- `raftCheck "batches of one, unordered links and a crash, one term"`: in every state it
reaches there is at most one leader per term, and every run of it is a run of the map. -/
example
    (hfailure : (check single crashing writeThenRead { maxTerm := 1, maxCrashes := 1 }).failure
      = none)
    (hcomplete : (check single crashing writeThenRead { maxTerm := 1, maxCrashes := 1 }).complete
      = true)
    {events : List (Event (sig N C R))} {w : W single}
    (hrun : (scenario crashing writeThenRead { maxTerm := 1, maxCrashes := 1 }).Run
      (cluster N single (store K V)) (Bounds.holds { maxTerm := 1, maxCrashes := 1 }) events w) :
    electionSafety w.state = true ∧
      ∃ a, (spec (store K V)).spec.lts.SMTr ⟨fun _ => none, 0, 0⟩
        ((events.filterMap Event.visible).map some) a :=
  ⟨always_of_pass single crashing writeThenRead _ _ props_respect hfailure hcomplete
      (.tail _ (.head _)) hrun.reachable,
    traces_of_pass single crashing writeThenRead _ _ props_respect hfailure hcomplete (.head _)
      hrun⟩

/-- `raftCheck "batches of one, reliable links, two terms"`, which adds two witnesses. -/
example
    (hfailure : (check single reliable writeThenRead { maxTerm := 2 }
      (props single ++ [partBatch single, pastTheEnd single])).failure = none)
    (hcomplete : (check single reliable writeThenRead { maxTerm := 2 }
      (props single ++ [partBatch single, pastTheEnd single])).complete = true)
    {w : W single}
    (hw : (scenario reliable writeThenRead { maxTerm := 2 }).Reachable
      (cluster N single (store K V)) (Bounds.holds { maxTerm := 2 }) w) :
    committedAgree w.state = true := by
  refine always_of_pass single reliable writeThenRead _ _ ?_ hfailure hcomplete
    (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))) hw
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact props_respect p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact partBatch_respect
    · exact pastTheEnd_respect

end RaftKV
