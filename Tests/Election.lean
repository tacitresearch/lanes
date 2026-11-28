/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Fixtures.Election

/-!
Model checks of leader election on three nodes with terms bounded at 2, over unordered links
with a crash budget. Timers, crashes and restarts are all explored here.
-/

namespace Tests.Election

open Lanes Tests.Fixtures.Election

abbrev N := Fin 3

instance : (sig N).Inspect := {}
instance (config : Config) : (cluster N config).Inspect := {}

def env : EnvModel (sig N) where
  link _ _ := Link.unordered
  mayCrash _ := true
  restarts _ := true

def check (config : Config) (maxCrashes : Nat) (tasks : Bool := false)
    (fingerprinted : Bool := false) :=
  let sc : Scenario (sig N) Unit := { env, driver := Driver.silent, maxCrashes }
  let props : List (Check.Property (World (cluster N config) Unit)) :=
    [ .always "at most one leader per term" fun w => atMostOneLeaderPerTerm w.state,
      .sometimes "a leader is elected" fun w => hasLeader w.state,
      .sometimes "a second term is reached" fun w =>
        (Enum.all (α := N)).any fun a => (w.state.state a).term == 2 ]
  let opts : Check.Options (World (cluster N config) Unit) :=
    { constraint := fun w => (Enum.all (α := N)).all fun a => (w.state.state a).term ≤ 2
      tasks }
  if fingerprinted then Check.systemFingerprinted (cluster N config) sc props opts
  else Check.system (cluster N config) sc props opts

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
      safe.ok),
    ("election: the check is not vacuous: a leader is elected and terms advance",
      safe.witnesses.length == 2),
    ("election: timeouts, crashes and restarts were all explored",
      ["timeout", "crash", "start"].all fun kind =>
        safe.coverage.any fun (name, count) => name == kind && count > 0),
    ("election: voting twice in a term gives two leaders in one term",
      match buggy.failure with
      | some (.violated "at most one leader per term" _) => true
      | _ => false) ]

/-- The checker's speed, on the check above with one crash: 164,847 states. The crash budget
is read from a reference so that the check runs here and not when the program starts. -/
def speed : IO (List (String × Bool)) := do
  let crashes ← (← IO.mkRef 1).get
  let t0 ← IO.monoMsNow
  let report := check {} crashes
  let states := report.states
  let elapsed := (← IO.monoMsNow) - t0
  IO.eprintln s!"check: {states} states and {report.transitions} transitions in {elapsed} ms, \
    {states * 1000 / max elapsed 1} states per second"
  let t1 ← IO.monoMsNow
  let printed := check {} crashes (fingerprinted := true)
  let fstates := printed.states
  let felapsed := (← IO.monoMsNow) - t1
  IO.eprintln s!"check, fingerprinted: {fstates} states in {felapsed} ms, \
    {fstates * 1000 / max felapsed 1} states per second"
  return [("election: the check with one crash explores 164,847 states", states == 164847),
    ("election: the fingerprinted check with one crash explores 164,847 states", fstates == 164847)]

/-- The fingerprinted search keeps hashes instead of states. With no collision it explores the
same states, and a violation it reports replays through the semantics
(`Check.systemFingerprinted_violated`). With tasks its report is the one without them
(`Check.fingerprint_tasks`). -/
def fingerprintTests : IO (List (String × Bool)) := do
  let crashes ← (← IO.mkRef 0).get
  let plain := check {} crashes
  let printed := check {} crashes (fingerprinted := true)
  let inTasks := check {} crashes (tasks := true) (fingerprinted := true)
  let buggy := check { votesOncePerTerm := false } crashes (fingerprinted := true)
  let config : Config := { votesOncePerTerm := false }
  return [("election: the fingerprinted check explores the same states and says it is fingerprinted",
      printed.passed && printed.complete && printed.fingerprinted && printed.states == plain.states
        && printed.transitions == plain.transitions && printed.depth == plain.depth
        && printed.witnesses.length == 2
        && (printed.renderSystem.splitOn "PASS (bounded, fingerprinted)").length == 2),
    ("election: computing a fingerprinted check's successors in tasks gives the same report",
      inTasks.renderSystem == printed.renderSystem),
    ("election: a fingerprinted check finds two leaders in one term, and the trace replays",
      match buggy.failure with
      | some (.violated "at most one leader per term" t) =>
        match (SysState.init (cluster N config) env).run env t.labels with
        | some c => !atMostOneLeaderPerTerm c && c.equiv env t.last.state
        | none => false
      | _ => false)]

/-- With tasks the report is the one without them: `Check.Search.explore_eq` proves it, and
this runs it, on a check large enough to use tasks. -/
def tasksTests : IO (List (String × Bool)) := do
  let crashes ← (← IO.mkRef 0).get
  let plain := check {} crashes
  let inTasks := check {} crashes (tasks := true)
  return [("election: computing successors in tasks gives the same report",
    plain.states == 24345 && inTasks.renderSystem == plain.renderSystem
      && inTasks.witnesses.map (·.2.labels.length) == plain.witnesses.map (·.2.labels.length))]

end Tests.Election
