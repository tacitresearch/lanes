/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Inspect

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
outputs it sees. Drivers may choose among several inputs; that choice exists only in the
simulator and the model checker, never in an actor.
-/
structure Driver (σ : Signature) (D : Type) where
  init : D
  inputs : D → List (σ.In × D)
  observe : D → σ.Out → D := fun d _ => d

namespace Driver

def silent : Driver σ Unit where
  init := ()
  inputs _ := []

def script (xs : List σ.In) : Driver σ (List σ.In) where
  init := xs
  inputs
    | [] => []
    | x :: xs => [(x, xs)]

def anyOrder (xs : List σ.In) : Driver σ (List σ.In) where
  init := xs
  inputs remaining :=
    (List.range remaining.length).filterMap fun k =>
      remaining[k]?.map fun x => (x, remaining.eraseIdx k)

end Driver

structure World (sys : System σ) (D : Type) where
  state : SysState sys
  driver : D
  crashes : Nat := 0

structure Scenario (σ : Signature) (D : Type) where
  env : EnvModel σ := {}
  driver : Driver σ D
  maxCrashes : Nat := 0

namespace World

variable {sys : System σ} {D : Type}

def init (sys : System σ) (sc : Scenario σ D) : World sys D where
  state := SysState.init sys sc.env
  driver := sc.driver.init

def next [Enum σ.Id] (sc : Scenario σ D) (w : World sys D) : List (Event σ × World sys D) :=
  let internal := (w.state.successors sc.env).filterMap fun (ev, c) =>
    match ev with
    | .output out => some (ev, { w with state := c, driver := sc.driver.observe w.driver out })
    | .crash _ =>
      if w.crashes < sc.maxCrashes then
        some (ev, { w with state := c, crashes := w.crashes + 1 })
      else none
    | _ => some (ev, { w with state := c })
  let inputs := (sc.driver.inputs w.driver).filterMap fun (x, d) =>
    (w.state.step sc.env (.input x)).map fun c =>
      (Event.input x, { w with state := c, driver := d })
  internal ++ inputs

end World

structure Run (sys : System σ) (D : Type) where
  events : Array (Event σ)
  final : World sys D
  /-- Whether the run ended because no event was enabled, as opposed to hitting the step
  bound. -/
  quiescent : Bool

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
