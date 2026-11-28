/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Inspect

/-!
# The deterministic scheduler

A single-threaded scheduler that runs a system by applying `SysState.step` to one enabled event
at a time, chosen by a seeded generator. The same seed gives the same run. Every run yields its
list of events, which replays through `SysState.run`.

It serves as the test and replay harness, and as random simulation for instances too large to
check exhaustively.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

/--
A model of the outside world: which inputs may arrive next and what it remembers of the
outputs it sees and of the timers it sees fire, since the clock is outside too. It also sees
each message an actor is handed (`deliver`), which a monitor needs when handling one passes a
deadline. Drivers may choose among several inputs; that choice exists only in the simulator
and the model checker, never in an actor.
-/
structure Driver (σ : Signature) (D : Type) where
  init : D
  inputs : D → List (σ.In × D)
  observe : D → σ.Out → D := fun d _ => d
  timeout : D → (i : σ.Id) → σ.Msg i → D := fun d _ _ => d
  deliver : D → (i : σ.Id) → σ.Msg i → D := fun d _ _ => d

namespace Driver

/-- A world that sends nothing: the system runs from its boot actors alone. -/
def silent : Driver σ Unit where
  init := ()
  inputs _ := []

/-- Sends `xs` in order. -/
def script (xs : List σ.In) : Driver σ (List σ.In) where
  init := xs
  inputs
    | [] => []
    | x :: xs => [(x, xs)]

/-- May send the inputs of `xs` that are left in any order; the checker tries every order. -/
def anyOrder (xs : List σ.In) : Driver σ (List σ.In) where
  init := xs
  inputs remaining :=
    (List.range remaining.length).filterMap fun k =>
      remaining[k]?.map fun x => (x, remaining.eraseIdx k)

end Driver

/-- What the scheduler and the checker step: the system, the driver's state, and the crashes
and restarts so far, which `Scenario.maxCrashes` and `Scenario.maxRestarts` bound. Properties
are stated over it. A restart does not touch the driver: the outside keeps what it sent and
saw. -/
structure World (sys : System σ) (D : Type) where
  state : SysState sys
  driver : D
  crashes : Nat := 0
  restarts : Nat := 0

/-- One instance to run or check: the environment model, the driver of the inputs, how many
crashes and process restarts a run may take, and the moments the environment may give the
steps. A restart is explored only where `env` allows it (`EnvModel.mayRestart`), as a crash is
only where `env.mayCrash` does. With no moments, nothing ticks and every step is told the time
0 and the seed 0; with some, the clock ticks to each later one (`Moment.later`), so a run is
finite. -/
structure Scenario (σ : Signature) (D : Type) where
  env : EnvModel σ := {}
  driver : Driver σ D
  maxCrashes : Nat := 0
  maxRestarts : Nat := 0
  moments : List Moment := []

/-- Whether `b` comes after `a`, by time and then by seed: the order the checker ticks in. -/
def Moment.later (a b : Moment) : Bool :=
  a.now_ms < b.now_ms || (a.now_ms == b.now_ms && a.seed < b.seed)

namespace World

variable {sys : System σ} {D : Type}

/-- `SysState.init` with the driver's initial state. -/
def init (sys : System σ) (sc : Scenario σ D) : World sys D where
  state := SysState.init sys sc.env
  driver := sc.driver.init

/-- Every event enabled in `w`, with the world it leads to: each event the environment model
allows, a crash or a restart only within its budget, and each input the driver may send. The checker
explores all of them; `simulate` and `fuzz` pick one. -/
def next [Enum σ.Id] (sc : Scenario σ D) (w : World sys D) : List (Event σ × World sys D) :=
  let internal := (w.state.successors sc.env).filterMap fun (ev, c) =>
    match ev with
    | .output out => some (ev, { w with state := c, driver := sc.driver.observe w.driver out })
    | .timeout i msg => some (ev, { w with state := c, driver := sc.driver.timeout w.driver i msg })
    | .deliver e | .duplicate e =>
      some (ev, { w with state := c, driver := sc.driver.deliver w.driver e.dst e.msg })
    | .crash _ =>
      if w.crashes < sc.maxCrashes then
        some (ev, { w with state := c, crashes := w.crashes + 1 })
      else none
    | .restart =>
      if w.restarts < sc.maxRestarts then
        some (ev, { w with state := c, restarts := w.restarts + 1 })
      else none
    | _ => some (ev, { w with state := c })
  let inputs := (sc.driver.inputs w.driver).filterMap fun (x, d) =>
    (w.state.step sc.env (.input x)).map fun c =>
      (Event.input x, { w with state := c, driver := d })
  let ticks := (sc.moments.filter (Moment.later w.state.clock)).map fun m =>
    (Event.tick m, { w with state := { w.state with clock := m } })
  internal ++ inputs ++ ticks

end World

/-- A run of `simulate`: its events, which replay through `SysState.run`, and where it ended. -/
structure Run (sys : System σ) (D : Type) where
  events : Array (Event σ)
  final : World sys D
  /-- Whether the run ended because no event was enabled, as opposed to hitting the step
  bound. -/
  quiescent : Bool

/-- A run of at most `maxSteps` events, each picked from `World.next` by a generator seeded
with `seed`: the same seed gives the same run. -/
def simulate [Enum σ.Id] (sys : System σ) {D : Type} (sc : Scenario σ D) (seed : Nat)
    (maxSteps : Nat := 10000) : Run sys D := Id.run do
  let mut gen := mkStdGen seed
  let mut w := World.init sys sc
  let mut events : Array (Event σ) := #[]
  let mut quiescent := false
  for _ in [0:maxSteps] do
    let choices := w.next sc
    if choices.isEmpty then
      quiescent := true
      break
    let (k, gen') := randNat gen 0 (choices.length - 1)
    gen := gen'
    match choices[k]? with
    | some (ev, w') =>
      events := events.push ev
      w := { w' with state := w'.state.compact }
    | none => break
  return { events, final := w, quiescent }

end Lanes
