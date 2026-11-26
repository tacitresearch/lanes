/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.System

/-!
Seeded random runs, for instances too large to explore exhaustively. Each run walks the same
`World.next` the model checker explores, so it meets the same faults: loss, duplication,
reordering, crashes within the budget, and every input the driver allows. A failure names its
seed and carries its trace, which replays through `SysState.run`.

A pass here is evidence, never a proof: only `Check.system` with a complete search covers every
state of an instance.
-/

@[expose] public section

namespace Lanes.Check

variable {σ : Signature} {sys : System σ} {D : Type}

structure FuzzFailure (S L : Type) where
  seed : Nat
  property : String
  trace : Trace S L

structure FuzzReport (S L : Type) where
  runs : Nat
  steps : Nat
  failure : Option (FuzzFailure S L)
  /-- The `sometimes` properties no run reached. -/
  unreached : List String

def FuzzReport.ok {S L : Type} (r : FuzzReport S L) : Bool :=
  r.failure.isNone && r.unreached.isEmpty

private def violated (props : List (Property (World sys D))) (w : World sys D) : Option String :=
  props.findSome? fun
    | .always name p => if p w then none else some name
    | .sometimes .. => none

private def reach (props : List (Property (World sys D))) (w : World sys D) (seen : List Bool) :
    List Bool :=
  List.zipWith (fun prop was =>
    was || match prop with
      | .sometimes _ p => p w
      | .always .. => true) props seen

private structure Walk (sys : System σ) (D : Type) where
  steps : Nat := 0
  seen : List Bool
  failure : Option (FuzzFailure (World sys D) (Event σ)) := none

private def run [Enum σ.Id] (sc : Scenario σ D) (props : List (Property (World sys D)))
    (maxSteps seed : Nat) (walk : Walk sys D) : Walk sys D := Id.run do
  let init := World.init sys sc
  let mut gen := mkStdGen seed
  let mut w := init
  let mut path : Array (Event σ × World sys D) := #[]
  let mut seen := reach props w walk.seen
  if let some property := violated props w then
    return { walk with seen, failure := some { seed, property, trace := ⟨init, []⟩ } }
  for _ in [0:maxSteps] do
    let choices := w.next sc
    if choices.isEmpty then break
    let (k, gen') := randNat gen 0 (choices.length - 1)
    gen := gen'
    let some (ev, w') := choices[k]? | break
    w := w'
    path := path.push (ev, w')
    seen := reach props w seen
    if let some property := violated props w then
      return { steps := walk.steps + path.size, seen,
               failure := some { seed, property, trace := ⟨init, path.toList⟩ } }
  return { walk with steps := walk.steps + path.size, seen }

/-- `runs` random runs of at most `maxSteps` events each, with seeds from `firstSeed` on. Stops
at the first run that violates an `always` property. -/
@[no_expose] def fuzz [Enum σ.Id] (sys : System σ) (sc : Scenario σ D) (props : List (Property (World sys D)))
    (runs : Nat := 1000) (maxSteps : Nat := 1000) (firstSeed : Nat := 0) :
    FuzzReport (World sys D) (Event σ) := Id.run do
  let mut walk : Walk sys D := { seen := props.map fun _ => false }
  let mut done := 0
  for k in [0:runs] do
    walk := run sc props maxSteps (firstSeed + k) walk
    done := done + 1
    if walk.failure.isSome then break
  let unreached := (props.zip walk.seen).filterMap fun (prop, seen) =>
    if seen then none else some prop.name
  return { runs := done, steps := walk.steps, failure := walk.failure, unreached }

def FuzzReport.render [σ.Inspect] [sys.Inspect] (r : FuzzReport (World sys D) (Event σ)) :
    String :=
  let verdict := match r.failure with
    | some f =>
      [s!"FAIL: \"{f.property}\" is violated after {f.trace.steps.length} steps (seed {f.seed})",
       f.trace.render (fun w => w.state.render) Event.render]
    | none =>
      if r.unreached.isEmpty then ["PASS (random runs, not a proof)"]
      else [s!"FAIL: never reached: {", ".intercalate (r.unreached.map fun p => s!"\"{p}\"")}"]
  "\n".intercalate (verdict ++ [s!"runs: {r.runs}, steps: {r.steps}"])

end Lanes.Check
