/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Scheduler
public import Lanes.Check.Search

/-!
# Model checking actor systems

`Check.system` explores every interleaving of a small instance of a system: every order of
deliveries and timeouts, every input the driver may send, and every loss, duplication and crash
the environment model allows. It runs the actors' own `step` functions through `SysState.step`,
so what is checked is the code that runs.

A counterexample is a list of events. It replays through `SysState.run` and in the deterministic
scheduler.

`Lanes.Check.SystemSound` proves what a complete PASS means.
-/

@[expose] public section

namespace Lanes.Check

variable {σ : Signature}

/--
A world tagged with the environment model its equality is taken under.

`slots` is the part of the world held in functions, as a list: the actors' states, whether they
are up and their timers. Hashing and comparing walk it instead of looking each actor up in
three functions on either side. `Node.of` computes it once and reads the world's functions
from it, so a stored world is compact.
-/
structure Node (sys : System σ) (env : EnvModel σ) (D : Type) [Enum σ.Id] where
  world : World sys D
  slots : List (Slot sys)
  slots_eq : slots = (Enum.all (α := σ.Id)).map (Slot.of world.state)

variable {sys : System σ} {D : Type}

def Node.of [Enum σ.Id] {env : EnvModel σ} (world : World sys D) : Node sys env D :=
  let slots := Slots.of world.state
  { world := { world with state := world.state.compactWith slots }
    slots := slots.list
    slots_eq := by
      change (Slots.of world.state).list = List.map
        (Slot.of (world.state.compactWith (Slots.of world.state))) Enum.all
      rw [SysState.compactWith_of]
      rfl }

instance [σ.Inspect] [sys.Inspect] [BEq D] {env : EnvModel σ} : BEq (Node sys env D) where
  beq a b := a.world.crashes == b.world.crashes && a.world.driver == b.world.driver
    && Slot.allSame a.slots b.slots
    && SysState.netEquiv env a.world.state.net b.world.state.net
    && a.world.state.outbox.isPerm b.world.state.outbox

instance [σ.Inspect] [sys.Inspect] [Hashable D] {env : EnvModel σ} :
    Hashable (Node sys env D) where
  hash a := mixHash (mixHash (a.slots.foldl Slot.hash 7) a.world.state.trafficHash)
    (mixHash (hash a.world.driver) (hash a.world.crashes))

def Trace.map {S S' L : Type} (f : S → S') (t : Trace S L) : Trace S' L where
  init := f t.init
  steps := t.steps.map fun (l, s) => (l, f s)

def Report.map {S S' L : Type} (f : S → S') (r : Report S L) : Report S' L :=
  { r with
    failure := r.failure.map fun
      | .violated p t => .violated p (t.map f)
      | .deadlock t => .deadlock (t.map f)
      | .unreached ps => .unreached ps
    witnesses := r.witnesses.map fun (n, t) => (n, t.map f) }

/-- The transition system that `system` searches. -/
def model [Enum σ.Id] (sys : System σ) {D : Type} (sc : Scenario σ D) :
    Model (Node sys sc.env D) (Event σ) where
  init := [.of (World.init sys sc)]
  next n := (n.world.next sc).map fun (ev, w) => (ev, .of w)

/--
Properties are stated over the `World`: the system state and the driver's state. The result
covers exactly the instance given: this driver, this crash budget, these bounds.
-/
def system [σ.Inspect] (sys : System σ) [sys.Inspect] {D : Type} [BEq D] [Hashable D]
    (sc : Scenario σ D) (props : List (Property (World sys D)))
    (opts : Options (World sys D) := {}) : Report (World sys D) (Event σ) :=
  let props' : List (Property (Node sys sc.env D)) := props.map fun
    | .always name p => .always name fun n => p n.world
    | .sometimes name p => .sometimes name fun n => p n.world
  let opts' : Options (Node sys sc.env D) :=
    { constraint := fun n => opts.constraint n.world
      maxDepth := opts.maxDepth
      maxStates := opts.maxStates
      checkDeadlock := opts.checkDeadlock
      terminal := fun n => opts.terminal n.world
      tasks := opts.tasks }
  (search (model sys sc) props' opts' Event.kind Event.kinds).map (·.world)

def Trace.render {S L : Type} (showState : S → String) (showLabel : L → String)
    (t : Trace S L) : String :=
  let steps := t.steps.zipIdx.map fun ((l, _), k) => s!"  {k + 1}. {showLabel l}"
  "\n".intercalate (steps ++ ["  state reached:", showState t.last])

/-- The report as the checker prints it: the verdict, the trace to a failure and the state it
reaches, the witnesses, the counts, and how often each kind of transition was taken. -/
def Report.render {S L : Type} (showState : S → String) (showLabel : L → String)
    (r : Report S L) : String :=
  let verdict := match r.failure with
    | none =>
      if r.complete then ["PASS: every reachable state explored"]
      else ["PASS (bounded): the search hit a bound, so only part of the state space is covered"]
    | some (.violated p t) =>
      [s!"FAIL: \"{p}\" is violated after {t.steps.length} steps",
       t.render showState showLabel]
    | some (.deadlock t) =>
      [s!"FAIL: deadlock after {t.steps.length} steps", t.render showState showLabel]
    | some (.unreached ps) =>
      [s!"FAIL: never reached: {", ".intercalate (ps.map fun p => s!"\"{p}\"")}",
       "  A `sometimes` property with no witness means the check is vacuous or the instance is "
         ++ "too small."]
  let witnesses := r.witnesses.map fun (n, t) => s!"reached \"{n}\" in {t.steps.length} steps"
  let coverage := r.coverage.map fun (name, count) =>
    if count == 0 then s!"{name} 0 (never fired)" else s!"{name} {count}"
  "\n".intercalate (verdict ++ witnesses ++
    [s!"states: {r.states}, transitions: {r.transitions}, depth: {r.depth}",
     s!"coverage: {", ".intercalate coverage}"])

/-- `render` for a report of `Check.system`, which prints states and events through
`Inspect`. -/
def Report.renderSystem [σ.Inspect] [sys.Inspect]
    (r : Report (World sys D) (Event σ)) : String :=
  r.render (fun w => w.state.render) Event.render

end Lanes.Check
