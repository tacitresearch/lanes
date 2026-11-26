/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV

/-!
Model checks of Raft on three nodes, one key and two values, run by `lake test`. Every check
monitors the cluster against the map it replicates, and evaluates the invariants in every
state. The instances are small because the state space is not: terms, log lengths and the
number of messages in flight are bounded.
-/

open Lanes RaftKV

abbrev N := Fin 3
abbrev K := Fin 1
abbrev V := Fin 2
abbrev C := Op K V
abbrev R := Res V
abbrev M := K → Option V

instance : (sig N C R).Inspect := {}
instance (config : Config) : (cluster N config (store K V)).Inspect := {}

structure Bounds where
  maxTerm : Nat := 2
  maxLog : Nat := 2
  maxNet : Nat := 4
  maxCrashes : Nat := 0

abbrev W (config : Config) :=
  World (cluster N config (store K V)) (List (Request N C) × Check.Monitor (sig N C R) M)

def props (config : Config) : List (Check.Property (W config)) :=
  [ Check.refines "the cluster is the map it replicates",
    .always "at most one leader per term" fun w => electionSafety w.state,
    .always "logs that agree on a term agree before it" fun w => logMatching w.state,
    .always "committed entries agree" fun w => committedAgree w.state,
    .always "a leader has every committed entry" fun w => leaderComplete w.state,
    .always "applied ≤ committed ≤ logged" fun w => wellFormed w.state,
    .sometimes "a leader is elected" fun w =>
      (Enum.all (α := N)).any fun a => isLeader (w.state.state a),
    .sometimes "a write is answered" fun w => w.state.outbox.any fun r => r.res == .ok,
    .sometimes "a read sees the written value" fun w =>
      w.state.outbox.any fun r => r.res == .value (some 1),
    .sometimes "a follower commits" fun w =>
      (Enum.all (α := N)).any fun a =>
        !isLeader (w.state.state a) && (w.state.state a).commit > 0 ]

def check (config : Config) (env : EnvModel (sig N C R)) (requests : List (Request N C))
    (bounds : Bounds := {}) :=
  Check.system (cluster N config (store K V))
    { env, driver := (spec (store K V)).monitored (Driver.anyOrder requests)
      maxCrashes := bounds.maxCrashes } (props config)
    { constraint := fun w =>
        w.state.net.length ≤ bounds.maxNet
          && (Enum.all (α := N)).all fun a =>
            (w.state.state a).term ≤ bounds.maxTerm && (w.state.state a).log.length ≤ bounds.maxLog }

def reliable : EnvModel (sig N C R) := {}

def writeThenRead : List (Request N C) :=
  [⟨1, 0, .put 0 1⟩, ⟨2, 0, .get 0⟩]

def unordered : EnvModel (sig N C R) where
  link _ _ := Link.unordered

def crashing : EnvModel (sig N C R) where
  link _ _ := Link.unordered
  mayCrash _ := true
  restarts _ := true

/-- Two writes through two nodes: enough for a leader of a later term to hold an entry of an
earlier one that another leader has replaced. -/
def twoWrites : List (Request N C) :=
  [⟨1, 0, .put 0 0⟩, ⟨2, 1, .put 0 1⟩]

def run {config : Config} (name : String)
    (check : Unit → Check.Report (W config) (Event (sig N C R))) (expect : Option String := none) :
    IO Bool := do
  let t0 ← IO.monoMsNow
  let report := check ()
  let found := match report.failure with
    | none => none
    | some (.violated property _) => some property
    | some (.deadlock _) => some "deadlock"
    | some (.unreached names) => some s!"never reached: {names}"
  let ok := found == expect && (expect.isSome || report.complete)
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}: {report.states} states, depth {report.depth}, {(← IO.monoMsNow) - t0} ms{match found with | some f => s!", found: {f}" | none => ""}"
  if !ok then IO.println report.renderSystem
  return ok

/-- Checks that finish in seconds: run by `lake test`. -/
def quick : List (String × IO Bool) :=
  [ ("reliable links, one term", run "reliable links, one term" fun _ =>
      check {} reliable writeThenRead { maxTerm := 1, maxNet := 3 }),
    ("seeded: a node votes for a candidate whose log is behind",
      run "seeded: a node votes for a candidate whose log is behind"
        (expect := some "a leader has every committed entry") fun _ =>
        check { votesForUpToDateOnly := false } reliable writeThenRead { maxTerm := 2 }) ]

/-- Checks that take minutes: `lake exe raftCheck deep`. -/
def deep : List (String × IO Bool) :=
  [ ("reliable links, two terms", run "reliable links, two terms" fun _ =>
      check {} reliable writeThenRead { maxTerm := 2 }),
    ("unordered links, one term", run "unordered links, one term" fun _ =>
      check {} unordered writeThenRead { maxTerm := 1 }),
    ("unordered links and a crash, one term", run "unordered links and a crash, one term" fun _ =>
      check {} crashing writeThenRead { maxTerm := 1, maxCrashes := 1 }),
    ("seeded: a leader commits an entry of an earlier term by counting",
      run "seeded: a leader commits an entry of an earlier term by counting"
        (expect := some "a leader has every committed entry") fun _ =>
        check { commitsOwnTermOnly := false } reliable twoWrites
          { maxTerm := 4, maxLog := 1, maxNet := 5 }) ]

def main (args : List String) : IO UInt32 := do
  let chosen := match args with
    | ["deep"] => deep
    | [name] => (quick ++ deep).filter (·.1 == name)
    | _ => quick
  let mut failed := 0
  for (_, check) in chosen do
    unless ← check do failed := failed + 1
  IO.println s!"{chosen.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
