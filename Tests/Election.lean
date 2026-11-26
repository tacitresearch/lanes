/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Election

/-!
Model checks of leader election on three nodes with terms bounded at 2, over unordered links
with a crash budget. Timers, crashes and restarts are all explored here.
-/

namespace Tests.Election

open Lanes Examples.Election

abbrev N := Fin 3

instance : (sig N).Inspect := {}
instance (config : Config) : (cluster N config).Inspect := {}

def env : EnvModel (sig N) where
  link _ _ := Link.unordered
  mayCrash _ := true
  restarts _ := true

def check (config : Config) (maxCrashes : Nat) :=
  Check.system (cluster N config) { env, driver := Driver.silent, maxCrashes }
    [ .always "at most one leader per term" fun w => atMostOneLeaderPerTerm w.state,
      .sometimes "a leader is elected" fun w => hasLeader w.state,
      .sometimes "a second term is reached" fun w =>
        (Enum.all (α := N)).any fun a => (w.state.state a).term == 2 ]
    { constraint := fun w => (Enum.all (α := N)).all fun a => (w.state.state a).term ≤ 2 }

/-! Five nodes over a lossy, duplicating network with three crashes are too many states to
explore, so they get seeded random runs. -/

def env5 : EnvModel (sig (Fin 5)) where
  link _ _ := Link.network
  mayCrash _ := true
  restarts _ := true

def fuzz5 (config : Config) :=
  Check.fuzz (cluster (Fin 5) config) { env := env5, driver := Driver.silent, maxCrashes := 3 }
    [ .always "at most one leader per term" fun w => atMostOneLeaderPerTerm w.state,
      .sometimes "a leader is elected" fun w => hasLeader w.state ]
    (runs := 60) (maxSteps := 250)

def fuzzTests : List (String × Bool) :=
  let safe := fuzz5 {}
  let buggy := fuzz5 { votesOncePerTerm := false }
  [ ("election: random runs on five nodes with loss, duplication and crashes keep one leader",
      safe.ok && safe.runs == 60),
    ("election: random runs find the split brain, and the trace they report replays",
      match buggy.failure with
      | some f =>
        match (SysState.init (cluster (Fin 5) { votesOncePerTerm := false }) env5).run env5
            f.trace.labels with
        | some c => !atMostOneLeaderPerTerm c
        | none => false
      | none => false) ]

def tests : List (String × Bool) :=
  let safe := check {} 1
  let buggy := check { votesOncePerTerm := false } 0
  [ ("election: at most one leader per term, with reordering and a crash",
      safe.ok && safe.complete),
    ("election: the check is not vacuous: a leader is elected and terms advance",
      safe.witnesses.length == 2),
    ("election: timeouts, crashes and restarts were all explored",
      ["timeout", "crash", "start"].all fun kind =>
        safe.coverage.any fun (name, count) => name == kind && count > 0),
    ("election: voting twice in a term gives two leaders in one term",
      match buggy.failure with
      | some (.violated "at most one leader per term" _) => true
      | _ => false) ]

end Tests.Election
