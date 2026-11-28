import Lanes
import Watchdog
import Lanes.Testing

/-!
The watchdog under the fair scheduler, run by `lake test`. The fair scheduler takes the event
owed longest, and a timer that a step arms again is owed anew from that step. So with the keeper
a ping ahead, pinging on its timer, the dog's `silence` timer is armed again before it is owed
long enough to fire: in two hundred steps the dog never barks. Once the keeper is told to rest
the dog barks, once, and then nothing is owed. `Watchdog/Proofs.lean` proves the first for the
infinite run (`exists_fair_run_never_barks`).

The checker, which fires timers in any order, finds a bark even while the keeper pings: timers
in Lanes have no real time, and what keeps the dog quiet is fairness, not timing.
-/

open Lanes Watchdog

instance : sig.Inspect := by instance_by_cases
instance : (system {}).Inspect := by instance_by_cases

/-- The events the fair scheduler takes in `steps` steps after `first`, newest last. -/
def fairRun (first : List (Event sig)) (steps : Nat) :
    List (Event sig) × FairScheduler (system {}) :=
  let s := first.foldl (fun s ev => s.take {} ev) (FairScheduler.init (system {}) {})
  (List.range steps).foldl (init := ([], s)) fun (taken, s) _ =>
    match s.next {} with
    | some ev => (taken ++ [ev], s.advance {})
    | none => (taken, s)

/-- The keeper is a ping ahead: one is in flight whenever the dog's timer comes up. -/
def ahead : List (Event sig) := [.timeout .keeper .tick, .timeout .keeper .tick, .deliver ping]

def tests : List (String × Bool) :=
  let (pinged, _) := fairRun ahead 200
  let (rested, s) := fairRun (ahead ++ [.input ()]) 200
  let checked := Check.system (system {}) { driver := Driver.silent }
    [ .sometimes "the dog barks" fun w => !w.state.outbox.isEmpty ] { maxDepth := some 6 }
  [ ("fair scheduler: while the keeper pings the dog never barks",
      !pinged.contains bark && pinged.count (.deliver ping) == 100),
    ("fair scheduler: once the keeper rests the dog barks once, and then nothing is owed",
      rested.count bark == 1 && rested.length < 200 && (s.next {}).isNone),
    ("checker: with timers in any order the dog may bark while the keeper pings",
      checked.witnesses.length == 1) ]

def main (args : List String) : IO UInt32 :=
  Lanes.Testing.report args (Lanes.Testing.Result.tests tests .check)
