/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Fixtures.Election
import Tests.Fixtures.Watchdog
import Tests.Gate

/-!
The fair scheduler, checked on runs before `Lanes.Semantics.FairRuns` proves it: from states
reached by random runs with faults, its queue holds exactly the owed events, and no event stays
owed for more steps than there were other events owed when it became owed. A timer that a step
arms again counts as owed from that step, which is what lets a keep-alive stay quiet.
-/

namespace Tests.Fair

open Lanes

variable {σ : Signature} {sys : System σ} [Enum σ.Id]

/-- Found by walking every actor, not from the scheduler's queue. -/
def owedEvents (env : EnvModel σ) (c : SysState sys) : List (Event σ) :=
  c.candidates.filter (c.owed env)

def queueExact (env : EnvModel σ) (s : FairScheduler sys) : Bool :=
  s.queue.isPerm (owedEvents env s.state)

structure Watch (sys : System σ) where
  scheduler : FairScheduler sys
  /-- For each owed event, how many more steps it may wait. -/
  patience : List (Event σ × Nat)
  ok : Bool := true
  /-- Newest first. -/
  taken : List (Event σ) := []
  /-- The most events owed at once. -/
  busiest : Nat := 0

def Watch.start (env : EnvModel σ) (s : FairScheduler sys) : Watch sys :=
  let owed := owedEvents env s.state
  { scheduler := s, patience := owed.map (·, owed.length - 1), ok := queueExact env s }

def Watch.step (env : EnvModel σ) (w : Watch sys) : Watch sys :=
  let taken := w.scheduler.next env
  let s := w.scheduler.advance env
  let owed := owedEvents env s.state
  let armed := (taken.map w.scheduler.state.arms).getD []
  let waited := owed.map fun ev =>
    match if taken == some ev || armed.contains ev then none else w.patience.lookup ev with
    | some 0 => none
    | some (left + 1) => some (ev, left)
    | none => some (ev, owed.length - 1)
  { scheduler := s
    patience := waited.filterMap id
    ok := w.ok && queueExact env s && waited.all (·.isSome)
      && (taken.isSome || w.patience.isEmpty)
    taken := taken.toList ++ w.taken
    busiest := max w.busiest owed.length }

/-- Follows `events`, then lets the fair scheduler run for `steps` steps. -/
def watch (sys : System σ) (env : EnvModel σ) (events : Array (Event σ)) (steps : Nat) :
    Watch sys :=
  let (s, exact) := events.foldl (init := (FairScheduler.init sys env, true)) fun (s, exact) ev =>
    (s.take env ev, exact && queueExact env s)
  let w := (List.range steps).foldl (fun w _ => w.step env) (Watch.start env s)
  { w with ok := w.ok && exact }

abbrev N := Fin 3

instance : (Tests.Fixtures.Election.sig N).Inspect := {}

def electionEnv : EnvModel (Tests.Fixtures.Election.sig N) where
  link _ _ := Link.network
  mayCrash _ := true
  restarts _ := true

/-- Election timers are armed again and again, so the fair scheduler never runs out of work. -/
def election (seed : Nat) : Watch (Tests.Fixtures.Election.cluster N {}) :=
  let run := simulate (Tests.Fixtures.Election.cluster N {})
    { env := electionEnv, driver := Driver.silent, maxCrashes := 2 } seed (maxSteps := 5 * seed)
  watch _ electionEnv run.events 200

open Lanes.Http Tests.Gate in
def gate (seed : Nat) : Watch (served (Server.system echo) bridge {}) :=
  let env := hostile fun _ _ => true
  let run := simulate (served (Server.system echo) bridge {})
    { env, driver := client [(1, get []), (2, get ["bad"]), (3, get [])], maxCrashes := 1 } seed
    (maxSteps := 3 * seed)
  watch _ env run.events 60

open Tests.Fixtures.Watchdog in
/-- The keeper is a ping ahead: one is in flight whenever the dog's timer comes up. Then the
keeper is left to ping, or told to rest. -/
def watchdog (rest : Bool) : Watch (system {}) :=
  let ahead : Array (Event sig) := #[.timeout .keeper .tick, .timeout .keeper .tick, .deliver ping]
  watch _ {} (if rest then ahead.push (.input ()) else ahead) 200

def tests : List (String × Bool) :=
  let elections := (List.range 8).map election
  let gates := (List.range 8).map gate
  let pinged := watchdog (rest := false)
  let rested := watchdog (rest := true)
  [ ("fair scheduler: on election runs the queue is exactly what is owed, and nothing owed "
        ++ "waits longer than the events that were owed before it",
      elections.all (·.ok)),
    ("fair scheduler: the election runs keep it busy, with several events owed at once",
      elections.all fun w => w.taken.length == 200 && w.busiest ≥ 3),
    ("fair scheduler: the same on the gate, from states with crashes, loss and duplicates",
      gates.all (·.ok) && gates.any (·.busiest ≥ 2)),
    ("fair scheduler: the gate runs out of work, and then nothing is owed",
      gates.all fun w => w.taken.length < 60 && w.patience.isEmpty),
    ("fair scheduler: a timer that is armed again waits anew, so a watchdog whose keeper keeps "
        ++ "pinging never barks",
      pinged.ok && !pinged.taken.contains Tests.Fixtures.Watchdog.bark
        && pinged.taken.count (.deliver Tests.Fixtures.Watchdog.ping) == 100),
    ("fair scheduler: once the keeper rests, the watchdog barks and nothing is owed",
      rested.ok && rested.taken.count Tests.Fixtures.Watchdog.bark == 1 && rested.taken.length < 200
        && rested.patience.isEmpty) ]

end Tests.Fair
