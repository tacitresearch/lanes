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

`Search.run` is the definition; `Search.runBatches` is what runs. It takes the stored states a
batch at a time, computes their successors in tasks and stores them in the order `run` would,
so it is the same function (`Search.runBatches_eq`) and the report does not depend on timing.

A state is hashed once, when it is produced: the search keeps it with its hash (`Hashed`), and
two states with different hashes are different without being compared.
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
  /-- Compute successors in tasks, on as many cores as there are. The report is the same
  either way. -/
  tasks : Bool := false

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
  /-- A shortest trace to a witness of each `sometimes` property that was reached, in the order
  of the properties. -/
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

/-- The witness of `prop` once `path` has been seen, given the one `found` before. -/
def witnessFor {S L : Type} (path : Path S L) (prop : Property S) (found : Option (Path S L)) :
    Option (Path S L) :=
  match prop, found with
  | .sometimes _ holds, none => if holds path.last then some path else none
  | _, found => found

/-- Witnesses are kept one per property, in the order of `props`, and not by name: two
`sometimes` properties with the same name each need their own. -/
def witness {S L : Type} (props : List (Property S)) (path : Path S L)
    (witnesses : List (Option (Path S L))) : List (Option (Path S L)) :=
  List.zipWith (witnessFor path) props witnesses

def unwitnessed {S L : Type} (props : List (Property S))
    (witnesses : List (Option (Path S L))) : List (Property S) :=
  (props.zip witnesses).filterMap fun
    | (.sometimes name p, none) => some (.sometimes name p)
    | _ => none

/-- A stored state: the last state of `path`, first reached at `depth`. -/
structure Visited (S L : Type) where
  path : Path S L
  depth : Nat

/-- A state with its hash. -/
structure Hashed (S : Type) where
  state : S
  hash : UInt64

namespace Hashed

variable {S : Type}

def of [Hashable S] (s : S) : Hashed S :=
  ⟨s, Hashable.hash s⟩

instance [BEq S] : BEq (Hashed S) where
  beq a b := a.hash == b.hash && a.state == b.state

instance : Hashable (Hashed S) where
  hash a := a.hash

end Hashed

/-- The state of a search. `queue` holds every stored state in the order found; those before
`head` have been expanded. `witnesses` has one entry per property. -/
structure Search (S L : Type) [BEq S] [Hashable S] where
  queue : Array (Visited S L) := #[]
  seen : Std.HashSet (Hashed S) := {}
  head : Nat := 0
  failure : Option (Failure S L) := none
  witnesses : List (Option (Path S L))
  complete : Bool := true
  transitions : Nat := 0
  depth : Nat := 0
  coverage : Std.HashMap String Nat := {}

namespace Search

variable {S L : Type} [BEq S] [Hashable S]

/-- Store the last state of `path`, whose hash is `hash`, if it is new and there is room, and
check the properties in it. Expects a search with no failure. -/
def add (props : List (Property S)) (opts : Options S) (path : Path S L) (hash : UInt64)
    (depth : Nat) (st : Search S L) : Search S L :=
  if st.seen.contains ⟨path.last, hash⟩ then st
  else if st.queue.size ≥ opts.maxStates then { st with complete := false }
  else
    { st with
      queue := st.queue.push { path, depth }
      seen := st.seen.insert ⟨path.last, hash⟩
      depth := max st.depth depth
      failure := violation props path
      witnesses := witness props path st.witnesses }

/-- Whether a state equal to `s` is stored. -/
def contains (st : Search S L) (s : S) : Bool :=
  st.seen.contains (.of s)

def addInit (props : List (Property S)) (opts : Options S) (st : Search S L) (s : S) : Search S L :=
  if st.failure.isSome || !opts.constraint s then st
  else st.add props opts (.init s) (Hashable.hash s) 0

def start (m : Model S L) (props : List (Property S)) (opts : Options S)
    (actions : List String) : Search S L :=
  m.init.foldl (addInit props opts)
    { witnesses := List.replicate props.length none
      coverage := actions.foldl (fun c a => c.insert a 0) {} }

/-- Take one transition from the last state of `parent`. -/
def visit (props : List (Property S)) (opts : Options S) (labelName : L → String)
    (parent : Path S L) (depth : Nat) (st : Search S L) (step : L × Hashed S) : Search S L :=
  if st.failure.isSome then st
  else
    let name := labelName step.1
    { st with
      transitions := st.transitions + 1
      coverage := st.coverage.insert name (st.coverage.getD name 0 + 1)
    }.add props opts (.step parent step.1 step.2.state) step.2.hash depth

/-- The transitions the search takes from `v`, each with the hash of its target. This is the
part of an expansion that does not depend on what has been stored, so it can be computed ahead
of its turn. -/
def successors (m : Model S L) (opts : Options S) (v : Visited S L) : List (L × Hashed S) :=
  if opts.maxDepth.any (v.depth ≥ ·) then []
  else (m.next v.path.last).filterMap fun step =>
    if opts.constraint step.2 then some (step.1, .of step.2) else none

/-- Expand the stored state `v`, which is the one at `head`, given its `successors`. -/
def expandWith (props : List (Property S)) (opts : Options S) (labelName : L → String)
    (st : Search S L) (v : Visited S L) (succs : List (L × Hashed S)) : Search S L :=
  if opts.maxDepth.any (v.depth ≥ ·) then { st with complete := false, head := st.head + 1 }
  else if opts.checkDeadlock && succs.isEmpty && !opts.terminal v.path.last then
    { st with failure := some (.deadlock v.path.toTrace) }
  else
    let st := succs.foldl (visit props opts labelName v.path (v.depth + 1)) st
    { st with head := st.head + 1 }

/-- Expand the stored state `v`, which is the one at `head`. -/
def expand (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) (st : Search S L) (v : Visited S L) : Search S L :=
  st.expandWith props opts labelName v (successors m opts v)

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

/-- `run`, one unit of fuel for each list, with the successors of each state to expand given
instead of computed. -/
def expandAll (props : List (Property S)) (opts : Options S) (labelName : L → String) :
    List (List (L × Hashed S)) → Search S L → Search S L
  | [], st => st
  | succs :: rest, st =>
    if st.failure.isSome then st
    else
      match st.queue[st.head]? with
      | none => st
      | some v => expandAll props opts labelName rest (st.expandWith props opts labelName v succs)

/-- `xs.map f` in pieces of `size`, each computed in a task of its own. A list of at most one
piece is computed here: a task costs more than a few states do. -/
def mapInTasks {α β : Type} (f : α → β) (size : Nat) : (fuel : Nat) → List α → List (Task (List β))
  | 0, xs => [.pure (xs.map f)]
  | fuel + 1, xs =>
    if xs.length ≤ size then [.pure (xs.map f)]
    else
      let piece := xs.take size
      Task.spawn (fun _ => piece.map f) :: mapInTasks f size fuel (xs.drop size)

/-- States whose successors are computed by one task. -/
def taskSize : Nat := 64

/-- States taken from the queue at a time. Their successors are all in memory until they are
stored, and are wasted if a failure is found among them, so this is bounded. -/
def batchSize : Nat := 4096

/--
`run`, with the successors of the next stored states computed in tasks while those before them
are stored. Each round takes up to `batchSize` states that are waiting to be expanded.
-/
def runBatches (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) (fuel : Nat) (st : Search S L) : Search S L :=
  let count := min fuel (min batchSize (st.queue.size - st.head))
  if _ : count = 0 ∨ st.failure.isSome then st
  else
    let batch := (st.queue.extract st.head (st.head + count)).toList
    let tasks := mapInTasks (successors m opts) taskSize batch.length batch
    runBatches m props opts labelName (fuel - count)
      (tasks.foldl (fun st task => st.expandAll props opts labelName task.get) st)
termination_by fuel
decreasing_by omega

/-- `run`, in tasks if the options ask for them. -/
def explore (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) (fuel : Nat) (st : Search S L) : Search S L :=
  if opts.tasks then st.runBatches m props opts labelName fuel
  else st.run m props opts labelName fuel

def report (props : List (Property S)) (st : Search S L) : Report S L where
  failure :=
    match st.failure with
    | some failure => some failure
    | none =>
      let missing := unwitnessed props st.witnesses
      if missing.isEmpty then none else some (.unreached (missing.map (·.name)))
  witnesses := (props.zip st.witnesses).filterMap fun
    | (.sometimes name _, some path) => some (name, path.toTrace)
    | _ => none
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
  ((Search.start m props opts actions).explore m props opts labelName opts.maxStates).report
    props

end Lanes.Check
