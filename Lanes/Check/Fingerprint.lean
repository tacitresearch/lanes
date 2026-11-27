/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Check.Search

/-!
# Fingerprinted search

`Check.fingerprint` explores like `Check.search`, breadth-first and with the same options, but
keeps of each state it has seen only its 64-bit hash, and of each state it has stored only the
place of its parent and which of the parent's transitions led to it. The states themselves are
kept only while they wait to be expanded, one level of the search at a time. So it holds far
more states than the exact search in the same memory.

Two different states with the same hash are taken as one, and the second is never explored. A
pass is then not a statement about every reachable state, and the report says it was
fingerprinted (`Report.fingerprinted`). What it reports is real: a trace is rebuilt by replaying
the recorded choices from an initial state through `Model.next`, and the property, the deadlock
or the witness is checked again on the state the replay reaches (`Lanes.Check.FingerprintSound`).
-/

@[expose] public section

namespace Lanes.Check

namespace Fingerprint

/-- What a fingerprinted search found, by the record of the state it found it in. -/
inductive Found where
  | violated (record : Nat)
  | deadlock (record : Nat)

/-- The state of a fingerprinted search. Record `r` is the `r`-th state stored: `parents[r]` is
its parent's record plus one, or `0` for an initial state, and `choices[r]` is its place in
`Model.init` or in its parent's `Model.next`. `level` holds the states waiting to be expanded,
with their records, and `later` those found from them. -/
structure Search (S : Type) where
  parents : Array Nat := #[]
  choices : Array Nat := #[]
  seen : Std.HashSet UInt64 := {}
  level : Array (S × Nat) := #[]
  later : Array (S × Nat) := #[]
  depth : Nat := 0
  failure : Option Found := none
  witnesses : List (Option Nat)
  complete : Bool := true
  transitions : Nat := 0
  coverage : Std.HashMap String Nat := {}

namespace Search

variable {S L : Type} [Hashable S]

/-- Store `s`, whose hash is `h`, found from record `parent` (plus one, `0` for none) by its
`choice`, if its hash is new and there is room, and check the properties in it. -/
def add (props : List (Property S)) (opts : Options S) (parent choice : Nat) (st : Search S)
    (s : S) (h : UInt64) : Search S :=
  if st.seen.contains h then st
  else if st.parents.size ≥ opts.maxStates then { st with complete := false }
  else
    let r := st.parents.size
    { st with
      parents := st.parents.push parent
      choices := st.choices.push choice
      seen := st.seen.insert h
      later := st.later.push (s, r)
      failure := if props.any fun | .always _ p => !p s | _ => false then some (.violated r)
        else none
      witnesses := List.zipWith (fun prop found => match prop, found with
        | .sometimes _ p, none => if p s then some r else none
        | _, found => found) props st.witnesses }

def start (m : Model S L) (props : List (Property S)) (opts : Options S)
    (actions : List String) : Search S :=
  let st : Search S := { witnesses := List.replicate props.length none
                         coverage := actions.foldl (fun c a => c.insert a 0) {} }
  let st := m.init.zipIdx.foldl (fun st (s, k) =>
    if st.failure.isSome || !opts.constraint s then st
    else st.add props opts 0 k s (Hashable.hash s)) st
  { st with level := st.later, later := #[] }

/-- A transition the search takes: its label, its target, the target's place in `Model.next`
and its hash. -/
abbrev Succ (S L : Type) := L × S × Nat × UInt64

/-- The transitions the search takes from `s`: those within the constraint. This is the part
of an expansion that does not depend on what has been stored, so it can be computed in a task. -/
def successors (m : Model S L) (opts : Options S) (s : S) : List (Succ S L) :=
  (m.next s).zipIdx.filterMap fun ((l, t), k) =>
    if opts.constraint t then some (l, t, k, Hashable.hash t) else none

/-- Take a transition from the state of record `r`. -/
def visit (props : List (Property S)) (opts : Options S) (labelName : L → String) (r : Nat)
    (st : Search S) (step : Succ S L) : Search S :=
  if st.failure.isSome then st
  else
    let name := labelName step.1
    { st with
      transitions := st.transitions + 1
      coverage := st.coverage.insert name (st.coverage.getD name 0 + 1)
    }.add props opts (r + 1) step.2.2.1 step.2.1 step.2.2.2

/-- Expand a state of the current level, of record `entry.2`, given its successors. -/
def expandWith (props : List (Property S)) (opts : Options S) (labelName : L → String)
    (st : Search S) (entry : S × Nat) (succs : List (Succ S L)) : Search S :=
  if st.failure.isSome then st
  else if opts.maxDepth.any (st.depth ≥ ·) then { st with complete := false }
  else if opts.checkDeadlock && succs.isEmpty && !opts.terminal entry.1 then
    { st with failure := some (.deadlock entry.2) }
  else succs.foldl (visit props opts labelName entry.2) st

def expand (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) (st : Search S) (entry : S × Nat) : Search S :=
  st.expandWith props opts labelName entry (successors m opts entry.1)

/-- The next level: the states found from this one, which are expanded next. -/
def advance (st : Search S) : Search S :=
  { st with level := st.later, later := #[],
            depth := if st.later.isEmpty then st.depth else st.depth + 1 }

/-- Expand a level at a time until none is left, a failure is found or `fuel` runs out. -/
def run (m : Model S L) (props : List (Property S)) (opts : Options S) (labelName : L → String) :
    (fuel : Nat) → Search S → Search S
  | 0, st => st
  | fuel + 1, st =>
    if st.failure.isSome || st.level.isEmpty then st
    else run m props opts labelName fuel (st.level.foldl (expand m props opts labelName) st).advance

/-- States of a level whose successors are computed at a time: they are all in memory until
they are stored. -/
def batchSize : Nat := 4096

/-- Expand `entries`, the successors of `batchSize` of them at a time computed in tasks of
`Check.Search.taskSize` states, while those before them are stored. -/
def expandInTasks (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) : (fuel : Nat) → List (S × Nat) → Search S → Search S
  | 0, entries, st => entries.foldl (expand m props opts labelName) st
  | fuel + 1, entries, st =>
    if entries.isEmpty then st
    else
      let batch := entries.take batchSize
      let tasks := Check.Search.mapInTasks (fun e => (e, successors m opts e.1))
        Check.Search.taskSize batch.length batch
      let st := tasks.foldl (fun st task =>
        task.get.foldl (fun st (e, succs) => st.expandWith props opts labelName e succs) st) st
      expandInTasks m props opts labelName fuel (entries.drop batchSize) st

/-- `run`, with each level's successors computed in tasks (`Options.tasks`). It is the same
function (`Fingerprint.Search.runParallel_eq`): the same states stored in the same order, the
same report. -/
def runParallel (m : Model S L) (props : List (Property S)) (opts : Options S)
    (labelName : L → String) : (fuel : Nat) → Search S → Search S
  | 0, st => st
  | fuel + 1, st =>
    if st.failure.isSome || st.level.isEmpty then st
    else runParallel m props opts labelName fuel
      (expandInTasks m props opts labelName st.level.size st.level.toList st).advance

/-- The choices that lead to record `r`, from its initial state. Each parent is stored before
its children, so `fuel` the number of records is enough. -/
def choicesTo (st : Search S) : (fuel : Nat) → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, r, acc =>
    match st.parents[r]?, st.choices[r]? with
    | some 0, some k => k :: acc
    | some (p + 1), some k => choicesTo st fuel p (k :: acc)
    | _, _ => acc

end Search

variable {S L : Type}

/-- The steps the choices `ks` take from `s`, each within the constraint. -/
def replaySteps (m : Model S L) (constraint : S → Bool) : S → List Nat → Option (List (L × S))
  | _, [] => some []
  | s, k :: ks =>
    match (m.next s)[k]? with
    | some (l, t) =>
      if constraint t then (replaySteps m constraint t ks).map ((l, t) :: ·) else none
    | none => none

/-- The trace the choices `ks` take: an initial state, then a transition each. -/
def replay (m : Model S L) (constraint : S → Bool) : List Nat → Option (Trace S L)
  | [] => none
  | k :: ks =>
    match m.init[k]? with
    | some s => if constraint s then (replaySteps m constraint s ks).map ({ init := s, steps := · })
      else none
    | none => none

/-- The failure `t` shows, checked again in its last state. -/
def recheck (props : List (Property S)) (opts : Options S) (m : Model S L) :
    Found → Trace S L → Option (Failure S L)
  | .violated _, t => props.findSome? fun
    | .always name p => if p t.last then none else some (.violated name t)
    | .sometimes .. => none
  | .deadlock _, t =>
    if (m.next t.last).all (fun step => !opts.constraint step.2) && !opts.terminal t.last then
      some (.deadlock t)
    else none

def Found.record : Found → Nat
  | .violated r | .deadlock r => r

end Fingerprint

variable {S L : Type} [Hashable S]

/-- The report of a fingerprinted search. Every trace in it is replayed from the recorded
choices and what it shows is checked again; a failure that did not replay would leave the
report incomplete instead (it cannot happen: `Model.next` is a function). -/
def Fingerprint.Search.report (m : Model S L) (props : List (Property S)) (opts : Options S)
    (st : Fingerprint.Search S) : Report S L :=
  let trace (r : Nat) := Fingerprint.replay m opts.constraint (st.choicesTo st.parents.size r [])
  let failure := st.failure.bind fun f =>
    (trace f.record).bind (Fingerprint.recheck props opts m f)
  let witnesses := (props.zip st.witnesses).filterMap fun
    | (.sometimes name p, some r) => (trace r).bind fun t => if p t.last then some (name, t) else none
    | _ => none
  let missing := (props.zip st.witnesses).filterMap fun
    | (.sometimes name _, none) => some name
    | _ => none
  { failure := match failure with
      | some f => some f
      | none => if st.failure.isSome || missing.isEmpty then none else some (.unreached missing)
    witnesses
    states := st.parents.size
    transitions := st.transitions
    depth := st.depth
    complete := st.complete && (st.failure.isSome == failure.isSome)
      && (st.failure.isSome || st.level.isEmpty)
    coverage := st.coverage.toList.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 ≤ b.1)
    fingerprinted := true }

/--
`search`, keeping a hash of each state seen instead of the state. It holds many more states in
the same memory, but a pass is not exhaustive: a state whose hash collides with one seen before
is never explored. The report says it was fingerprinted. A counterexample or a witness it
reports replays exactly (`Check.fingerprint_violated`).

`maxStates + 1` levels are enough: each level but the last stores a state. With
`Options.tasks` each level's successors are computed in tasks; the report is the same.
-/
def fingerprint (m : Model S L) (props : List (Property S)) (opts : Options S := {})
    (labelName : L → String := fun _ => "step") (actions : List String := []) : Report S L :=
  let st := Fingerprint.Search.start m props opts actions
  let st := if opts.tasks then st.runParallel m props opts labelName (opts.maxStates + 1)
    else st.run m props opts labelName (opts.maxStates + 1)
  st.report m props opts

end Lanes.Check
