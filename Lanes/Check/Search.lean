/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.HashMap

/-!
# Explicit-state search

The model checker's engine: breadth-first search over a transition system given by an
executable successor function. It knows nothing about actors; `Lanes.Check.System` instantiates
it with `SysState.step`.

The search stores full states and compares them exactly, so a state count is the true number of
distinct states and can be compared with other checkers. Because the search is breadth-first,
every reported trace is a shortest one.

The semantics of counting follow TLC and Veil so that counts line up: a successor that violates
the state constraint is dropped before it is counted or checked, and "distinct states" is the
number of states seen, including those not expanded because of a depth bound.

The search design follows the sequential engine of Veil (verse-lab/veil, Apache-2.0) at commit
`b1128cc`, simplified to store states instead of fingerprints.

## Main definitions

- `Check.Model`: initial states and successors.
- `Check.Property`: `always` (an invariant) and `sometimes` (a state that must be reachable).
- `Check.Options`: bounds, state constraint, deadlock checking.
- `Check.search`: run the search and return a `Check.Report`.
-/

@[expose] public section

namespace Lanes.Check

/-- A transition system given by executable initial states and successors. -/
structure Model (S L : Type) where
  /-- The initial states. -/
  init : List S
  /-- The successors of a state, each with the label of the step taken. -/
  next : S → List (L × S)

/-- A property of the states of a model. -/
inductive Property (S : Type) where
  /-- `p` must hold in every reachable state. -/
  | always (name : String) (p : S → Bool)
  /--
  `p` must hold in some reachable state. Paired with an invariant, this is its vacuity check
  (rule 5.3): it shows the states the invariant talks about are actually reached.
  -/
  | sometimes (name : String) (p : S → Bool)

namespace Property

variable {S : Type}

/-- The name of a property. -/
def name : Property S → String
  | .always n _ | .sometimes n _ => n

end Property

/-- Bounds and switches for a search. -/
structure Options (S : Type) where
  /-- States violating the constraint are dropped: neither counted, checked nor expanded. -/
  constraint : S → Bool := fun _ => true
  /-- States at this depth are not expanded. Initial states have depth 0. -/
  maxDepth : Option Nat := none
  /-- Store at most this many distinct states. States found beyond the limit are left out and
  the report is marked incomplete. -/
  maxStates : Nat := 10000000
  /-- Report a state with no successors as a deadlock, unless `terminal` holds of it. -/
  checkDeadlock : Bool := false
  /-- States that are allowed to have no successors. -/
  terminal : S → Bool := fun _ => false

/-- A path through a model: an initial state and the steps taken from it. -/
structure Trace (S L : Type) where
  /-- The initial state. -/
  init : S
  /-- Each step's label and the state it leads to. -/
  steps : List (L × S)

namespace Trace

variable {S L : Type}

/-- The last state of a trace. -/
def last (t : Trace S L) : S :=
  match t.steps.getLast? with
  | some (_, s) => s
  | none => t.init

/-- The labels along a trace. -/
def labels (t : Trace S L) : List L :=
  t.steps.map (·.1)

end Trace

/-- Why a search failed. -/
inductive Failure (S L : Type) where
  /-- An `always` property is false in the last state of the trace. -/
  | violated (property : String) (trace : Trace S L)
  /-- The last state of the trace has no successors and is not terminal. -/
  | deadlock (trace : Trace S L)
  /-- These `sometimes` properties hold in no state that was explored. -/
  | unreached (properties : List String)

/-- The result of a search. -/
structure Report (S L : Type) where
  /-- The first failure found, if any. -/
  failure : Option (Failure S L)
  /-- A shortest trace to a witness of each `sometimes` property that was reached. -/
  witnesses : List (String × Trace S L)
  /-- Distinct states seen. -/
  states : Nat
  /-- Transitions taken, counting those that lead to an already seen state. -/
  transitions : Nat
  /-- The largest depth of a state seen. -/
  depth : Nat
  /-- Whether every reachable state within the constraint was explored. If `false`, a bound
  cut the search short and a passing result covers only the part explored. -/
  complete : Bool
  /-- How many transitions carried each label name, most frequent first. -/
  coverage : List (String × Nat)

namespace Report

variable {S L : Type}

/-- Whether the search found no failure. -/
def ok (r : Report S L) : Bool :=
  r.failure.isNone

end Report

/-- Search bookkeeping. `states[k]` was reached from `states[parent[k].1]` by `parent[k].2`. -/
private structure Frontier (S L : Type) [BEq S] [Hashable S] where
  states : Array S := #[]
  index : Std.HashMap S Nat := {}
  parent : Array (Option (Nat × L)) := #[]
  depths : Array Nat := #[]

variable {S L : Type} [BEq S] [Hashable S]

/-- The trace from an initial state to `states[k]`, following parent pointers. -/
private def Frontier.trace (f : Frontier S L) (k : Nat) : Option (Trace S L) := do
  let mut steps : List (L × S) := []
  let mut cur := k
  -- A parent always has a smaller index, so `k + 1` iterations suffice.
  for _ in [0:k + 1] do
    match f.parent[cur]? with
    | some (some (p, l)) =>
      steps := (l, ← f.states[cur]?) :: steps
      cur := p
    | _ => break
  return { init := ← f.states[cur]?, steps }

/-- Add a state if it is new. Returns the bookkeeping and the index of the state if it was
added. -/
private def Frontier.add (f : Frontier S L) (s : S) (parent : Option (Nat × L)) (depth : Nat) :
    Frontier S L × Option Nat :=
  if f.index.contains s then (f, none)
  else
    let k := f.states.size
    ({ states := f.states.push s, index := f.index.insert s k, parent := f.parent.push parent,
       depths := f.depths.push depth }, some k)

/--
Explore the model breadth-first and check the properties.

The search stops at the first violated `always` property or deadlock. `labelName` groups labels
for the coverage count; `actions` lists the label names expected to occur, so that names with a
zero count show up in the coverage.
-/
@[no_expose] def search (m : Model S L) (props : List (Property S)) (opts : Options S := {})
    (labelName : L → String := fun _ => "step") (actions : List String := []) : Report S L :=
  Id.run do
  let mut f : Frontier S L := {}
  let mut failure : Option (Failure S L) := none
  let mut witnesses : List (String × Nat) := []
  let mut coverage : Std.HashMap String Nat := actions.foldl (fun c a => c.insert a 0) {}
  let mut transitions := 0
  let mut complete := true
  let mut depth := 0
  -- Check a newly added state against the properties.
  let check := fun (f : Frontier S L) (witnesses : List (String × Nat)) (k : Nat) (s : S) =>
    props.foldl (init := ((none : Option (Failure S L)), witnesses)) fun (fail, ws) p =>
      match p with
      | .always name holds =>
        if fail.isNone && !holds s then
          (f.trace k |>.map (Failure.violated name), ws)
        else (fail, ws)
      | .sometimes name holds =>
        if !ws.any (·.1 == name) && holds s then (fail, ws ++ [(name, k)]) else (fail, ws)
  for s in m.init do
    if failure.isSome then break
    if !opts.constraint s then continue
    let (f', added) := f.add s none 0
    f := f'
    if let some k := added then
      let (fail, ws) := check f witnesses k s
      failure := fail
      witnesses := ws
  let mut head := 0
  for _ in [0:opts.maxStates] do
    if failure.isSome then break
    let some s := f.states[head]? | break
    let d := f.depths[head]?.getD 0
    if opts.maxDepth.any (d ≥ ·) then
      complete := false
      head := head + 1
      continue
    let succs := (m.next s).filter fun (_, s') => opts.constraint s'
    if opts.checkDeadlock && succs.isEmpty && !opts.terminal s then
      failure := f.trace head |>.map Failure.deadlock
      break
    for (l, s') in succs do
      if failure.isSome then break
      transitions := transitions + 1
      coverage := coverage.insert (labelName l) (coverage.getD (labelName l) 0 + 1)
      if f.states.size ≥ opts.maxStates && !f.index.contains s' then
        complete := false
        continue
      let (f', added) := f.add s' (some (head, l)) (d + 1)
      f := f'
      if let some k := added then
        depth := max depth (d + 1)
        let (fail, ws) := check f witnesses k s'
        failure := fail
        witnesses := ws
    head := head + 1
  if failure.isNone && head < f.states.size then
    complete := false
  if failure.isNone then
    let missing := props.filterMap fun p =>
      match p with
      | .sometimes name _ => if witnesses.any (·.1 == name) then none else some name
      | .always .. => none
    if !missing.isEmpty then
      failure := some (.unreached missing)
  return {
    failure
    witnesses := witnesses.filterMap fun (name, k) => (f.trace k).map (name, ·)
    states := f.states.size
    transitions
    depth
    complete
    coverage := coverage.toList.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 ≤ b.1)
  }

end Lanes.Check
