import Lanes
import Election
import Lanes.Testing

/-!
Model checks of leader election, run by `lake test` (Lanes rule 5.1). Three nodes with terms
bounded at 2, over links that reorder, with a crash: there is at most one leader per term, a
leader is elected and a second term is reached (rule 5.3), and timeouts, crashes and restarts
are all explored. A node that votes twice in a term gives two leaders in one term. Five nodes
with loss, duplication and three crashes are too many states to explore, so they get seeded
random runs, which find the same bug.
-/

open Lanes Election

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

def env5 : EnvModel (sig (Fin 5)) where
  link _ _ := Link.network
  mayCrash _ := true
  restarts _ := true

def fuzz5 (config : Config) :=
  Check.fuzz (cluster (Fin 5) config) { env := env5, driver := Driver.silent, maxCrashes := 3 }
    [ .always "at most one leader per term" fun w => atMostOneLeaderPerTerm w.state,
      .sometimes "a leader is elected" fun w => hasLeader w.state ]
    (runs := 60) (maxSteps := 250)

def tests : List (String × Bool) :=
  let safe := check {} 0
  let buggy := check { votesOncePerTerm := false } 0
  let fuzzed := fuzz5 {}
  let fuzzedBuggy := fuzz5 { votesOncePerTerm := false }
  [ ("three nodes: at most one leader per term, with reordering",
      safe.ok),
    ("three nodes: a leader is elected and terms advance", safe.witnesses.length == 2),
    ("three nodes: timeouts were explored",
      safe.coverage.any fun (name, count) => name == "timeout" && count > 0),
    ("three nodes: voting twice in a term gives two leaders in one term",
      match buggy.failure with
      | some (.violated "at most one leader per term" _) => true
      | _ => false),
    ("five nodes, random runs with loss, duplication and crashes: one leader per term",
      fuzzed.ok && fuzzed.runs == 60),
    ("five nodes, random runs: voting twice is found, and the trace replays",
      match fuzzedBuggy.failure with
      | some f =>
        match (SysState.init (cluster (Fin 5) { votesOncePerTerm := false }) env5).run env5
            f.trace.labels with
        | some c => !atMostOneLeaderPerTerm c
        | none => false
      | none => false) ]

def main (args : List String) : IO UInt32 :=
  Lanes.Testing.report args (Lanes.Testing.Result.tests tests .check)
