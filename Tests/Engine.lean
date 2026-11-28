/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Proofs

/-!
Tests of the search engine on transition systems with known state counts.

The bitmask system and the DieHard puzzle are the first rungs of the validation ladder taken
from Veil's regression tests (`VeilTest/Regression/ParallelActionStats.lean`,
`Examples/Puzzles/DieHard.lean`).
-/

namespace Tests.Engine

open Lanes Lanes.Check

/-- Eight bits, one action per bit that sets it: 256 states, and each action is taken from every
state. -/
def bitmask : Model Nat (Fin 8) where
  init := [0]
  next s := (Enum.all (α := Fin 8)).map fun b => (b, s ||| (1 <<< b.val))

/-- The DieHard water jug puzzle: a 3 and a 5 gallon jug, measure 4 gallons. -/
def dieHard : Model (Nat × Nat) String where
  init := [(0, 0)]
  next
    | (small, big) =>
      let toBig := min small (5 - big)
      let toSmall := min big (3 - small)
      [("fillSmall", (3, big)), ("fillBig", (small, 5)), ("emptySmall", (0, big)),
       ("emptyBig", (small, 0)), ("smallToBig", (small - toBig, big + toBig)),
       ("bigToSmall", (small + toSmall, big - toSmall))]

def counter : Model Nat Unit where
  init := [0]
  next s := if s < 3 then [((), s + 1)] else []

/-- Five initial states and no transitions. -/
def wide : Model Nat Unit where
  init := [0, 1, 2, 3, 4]
  next _ := []

/-- What a pass is worth: `search_sound_of_lawful` turns a complete search with no failure into
the invariant in every reachable state. -/
example (hpass : (search counter [.always "at most 3" (· ≤ 3)]).failure = none)
    (hcomplete : (search counter [.always "at most 3" (· ≤ 3)]).complete = true) {s : Nat}
    (hs : counter.Reachable (fun _ => true) s) : s ≤ 3 := by
  simpa using search_sound_of_lawful hpass hcomplete (List.mem_singleton.mpr rfl) hs

/-- A comparison written without spaces. This file imports Lanes and does not open the template
syntax, so `<` here must stay a comparison. -/
def tight (i n : Nat) : Bool := i<n

def tests : List (String × Bool) :=
  let capped := search bitmask [] { maxStates := 10 }
  let cappedInit := search wide [] { maxStates := 3 }
  let r := search bitmask []
  let solved := search dieHard [.always "big jug never holds 4" fun s => s.2 != 4] {} id
  let witness := search dieHard [.sometimes "big jug holds 4" fun s => s.2 == 4] {} id
  let vacuous := search dieHard [.sometimes "big jug holds 6" fun s => s.2 == 6] {} id
  let sameName := search dieHard
    [.sometimes "big jug" fun s => s.2 == 4, .sometimes "big jug" fun s => s.2 == 6] {} id
  let bounded := search bitmask [] { maxDepth := some 1 }
  let constrained := search bitmask [] { constraint := fun s => s < 16 }
  let dead := search counter [] { checkDeadlock := true }
  let live := search counter [] { checkDeadlock := true, terminal := (· == 3) }
  [ ("bitmask: 256 states", r.states == 256 && r.ok),
    ("bitmask: 2048 transitions, depth 8", r.transitions == 2048 && r.depth == 8),
    ("diehard: 16 states", witness.states == 16),
    ("diehard: invariant violated by a shortest trace of 6 steps",
      match solved.failure with
      | some (.violated _ t) => t.steps.length == 6 && t.last.2 == 4
      | _ => false),
    ("diehard: sometimes has a witness", witness.ok && witness.witnesses.length == 1),
    ("diehard: unreachable sometimes fails as vacuous",
      match vacuous.failure with
      | some (.unreached ["big jug holds 6"]) => true
      | _ => false),
    ("diehard: a sometimes is not witnessed by another of the same name",
      match sameName.failure with
      | some (.unreached ["big jug"]) => sameName.witnesses.length == 1
      | _ => false),
    ("depth bound: 9 states, reported incomplete", bounded.states == 9 && !bounded.complete),
    ("constraint: 16 states", constrained.states == 16 && constrained.complete),
    ("deadlock found after 3 steps",
      match dead.failure with
      | some (.deadlock t) => t.steps.length == 3
      | _ => false),
    ("terminal state is not a deadlock", live.ok),
    ("maxStates bounds the states stored, initial states included, and marks the report incomplete",
      capped.states == 10 && !capped.complete && capped.passed
        && cappedInit.states == 3 && !cappedInit.complete && cappedInit.passed),
    ("a comparison without spaces still parses in a file that imports Lanes",
      tight 1 2 && !tight 2 1) ]

end Tests.Engine
