/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.HashMap
public import Std.Data.HashSet

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

The search is written to be proved, not as a loop: a `Check.Search` value is threaded through
`Search.start` (store the initial states), `Search.run` (expand one stored state per unit of
fuel) and `Search.report`. `Lanes.Check.SearchSound` proves what a report claims.
-/

@[expose] public section

namespace Lanes.Check

structure Model (S L : Type) where
  init : List S
  next : S → List (L × S)

inductive Property (S : Type) where
  | always (name : String) (p : S → Bool)
  /--
  `p` must hold in some reachable state. Paired with an invariant, this is its vacuity check
  (rule 5.3): it shows the states the invariant talks about are actually reached.
  -/
  | sometimes (name : String) (p : S → Bool)

namespace Property

variable {S : Type}

def name : Property S → String
  | .always n _ | .sometimes n _ => n

def holds : Property S → S → Bool
  | .always _ p | .sometimes _ p => p

end Property

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
  terminal : S → Bool := fun _ => false

structure Trace (S L : Type) where
  init : S
  steps : List (L × S)

namespace Trace

variable {S L : Type}

def last (t : Trace S L) : S :=
  match t.steps.getLast? with
  | some (_, s) => s
  | none => t.init

def labels (t : Trace S L) : List L :=
  t.steps.map (·.1)

end Trace

inductive Failure (S L : Type) where
  | violated (property : String) (trace : Trace S L)
  | deadlock (trace : Trace S L)
  | unreached (properties : List String)

structure Report (S L : Type) where
  failure : Option (Failure S L)
  /-- A shortest trace to a witness of each `sometimes` property that was reached. -/
  witnesses : List (String × Trace S L)
  states : Nat
  /-- Transitions taken, counting those that lead to an already seen state. -/
  transitions : Nat
  depth : Nat
  /-- Whether every reachable state within the constraint was explored. If `false`, a bound
  cut the search short and a passing result covers only the part explored. -/
  complete : Bool
  /-- How many transitions carried each label name, most frequent first. -/
  coverage : List (String × Nat)

namespace Report

variable {S L : Type}

def ok (r : Report S L) : Bool :=
  r.failure.isNone

end Report

/-- A trace under construction, newest step outermost, so that a successor's path shares its
parent's. -/
inductive Path (S L : Type) where
  | init (s : S)
  | step (parent : Path S L) (l : L) (s : S)

namespace Path

variable {S L : Type}

def last : Path S L → S
  | .init s | .step _ _ s => s

def toTraceAux : Path S L → List (L × S) → Trace S L
  | .init s, steps => { init := s, steps }
  | .step parent l s, steps => parent.toTraceAux ((l, s) :: steps)

def toTrace (p : Path S L) : Trace S L :=
  p.toTraceAux []

end Path

/-- The first `always` property that fails in the last state of `path`. -/
def violation {S L : Type} (props : List (Property S)) (path : Path S L) : Option (Failure S L) :=
  props.findSome? fun
    | .always name holds => if holds path.last then none else some (.violated name path.toTrace)
    | .sometimes .. => none

/-- Record `path` as the witness of each `sometimes` property that holds in its last state and
has no witness yet. -/
def witness {S L : Type} (props : List (Property S)) (path : Path S L)
    (witnesses : List (String × Path S L)) : List (String × Path S L) :=
  props.foldl (init := witnesses) fun ws prop =>
    match prop with
    | .sometimes name holds =>
      if !ws.any (·.1 == name) && holds path.last then ws ++ [(name, path)] else ws
    | .always .. => ws

/-- A stored state: the last state of `path`, first reached at `depth`. -/
structure Visited (S L : Type) where
  path : Path S L
  depth : Nat

/-- The state of a search. `queue` holds every stored state in the order found; those before
`head` have been expanded. -/
structure Search (S L : Type) [BEq S] [Hashable S] where
  queue : Array (Visited S L) := #[]
  seen : Std.HashSet S := {}
  head : Nat := 0
  failure : Option (Failure S L) := none
  witnesses : List (String × Path S L) := []
  complete : Bool := true
  transitions : Nat := 0
  depth : Nat := 0
  coverage : Std.HashMap String Nat := {}

namespace Search

variable {S L : Type} [BEq S] [Hashable S]

/-- Store the last state of `path` if it is new and there is room, and check the properties
in it. Expects a search with no failure. -/
def add (props : List (Property S)) (opts : Options S) (path : Path S L) (depth : Nat)
    (st : Search S L) : Search S L :=
  if st.seen.contains path.last then st
  else if st.queue.size ≥ opts.maxStates then { st with complete := false }
  else
    { st with
      queue := st.queue.push { path, depth }
      seen := st.seen.insert path.last
      depth := max st.depth depth
      failure := violation props path
      witnesses := witness props path st.witnesses }

def addInit (props : List (Property S)) (opts : Options S) (st : Search S L) (s : S) : Search S L :=
  if st.failure.isSome || !opts.constraint s then st else st.add props opts (.init s) 0

def start (m : Model S L) (props : List (Property S)) (opts : Options S)
    (actions : List String) : Search S L :=
  m.init.foldl (addInit props opts) { coverage := actions.foldl (fun c a => c.insert a 0) {} }

/-- Take one transition from the last state of `parent`. -/
def visit (props : List (Property S)) (opts : Options S) (labelName : L → String)
    (parent : Path S L) (depth : Nat) (st : Search S L) (step : L × S) : Search S L :=
  if st.failure.isSome then st
  else
    let name := labelName step.1
    { st with
      transitions := st.transitions + 1
      coverage := st.coverage.insert name (st.coverage.getD name 0 + 1)
    }.add props opts (.step parent step.1 step.2) depth

/-- Expand the stored state `v`, which is the one at `head`. -/
def expand (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) (st : Search S L) (v : Visited S L) : Search S L :=
  if opts.maxDepth.any (v.depth ≥ ·) then { st with complete := false, head := st.head + 1 }
  else
    let succs := (m.next v.path.last).filter fun step => opts.constraint step.2
    if opts.checkDeadlock && succs.isEmpty && !opts.terminal v.path.last then
      { st with failure := some (.deadlock v.path.toTrace) }
    else
      let st := succs.foldl (visit props opts labelName v.path (v.depth + 1)) st
      { st with head := st.head + 1 }

/-- Expand stored states in order until none is left, a failure is found or `fuel` runs out. -/
def run (m : Model S L) (props : List (Property S)) (opts : Options S) (labelName : L → String) :
    (fuel : Nat) → Search S L → Search S L
  | 0, st => st
  | fuel + 1, st =>
    if st.failure.isSome then st
    else
      match st.queue[st.head]? with
      | none => st
      | some v => run m props opts labelName fuel (st.expand m props opts labelName v)

def report (props : List (Property S)) (st : Search S L) : Report S L where
  failure :=
    match st.failure with
    | some failure => some failure
    | none =>
      let missing := props.filterMap fun
        | .sometimes name _ => if st.witnesses.any (·.1 == name) then none else some name
        | .always .. => none
      if missing.isEmpty then none else some (.unreached missing)
  witnesses := st.witnesses.map fun (name, path) => (name, path.toTrace)
  states := st.queue.size
  transitions := st.transitions
  depth := st.depth
  complete := st.complete && (st.failure.isSome || st.head ≥ st.queue.size)
  coverage := st.coverage.toList.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 ≤ b.1)

end Search

variable {S L : Type} [BEq S] [Hashable S]

/--
Explore the model breadth-first and check the properties.

The search stops at the first violated `always` property or deadlock. `labelName` groups labels
for the coverage count; `actions` lists the label names expected to occur, so that names with a
zero count show up in the coverage.

`maxStates` units of fuel are enough: each expands one stored state, and no more are stored.
-/
def search (m : Model S L) (props : List (Property S)) (opts : Options S := {})
    (labelName : L → String := fun _ => "step") (actions : List String := []) : Report S L :=
  ((Search.start m props opts actions).run m props opts labelName opts.maxStates).report props

end Lanes.Check
