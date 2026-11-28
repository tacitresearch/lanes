/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
An adapter end to end: a stamper that asks the clock adapter for the time. Its property is
model-checked against what a clock may do, and a real run with the real clock is checked to be
one of the runs that model allows.
-/

namespace Tests.Clock

open Lanes Std.Async

inductive In where
  | stamp (id : Nat)
  | time (id time_ms : Nat)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | ask (id : Nat)
  | stamped (id time_ms : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev stampSig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- The state is the latest stamp given. `ahead` seeds a bug: a stamp the clock never gave. -/
abbrev stamper (ahead : Bool := false) : System stampSig where
  State _ := Nat
  actor _ :=
    { init := 0
      step := fun latest msg =>
        match msg with
        | .stamp id => (latest, [.emit (.ask id)])
        | .time id time_ms =>
          let stamp := if ahead then max latest time_ms + 1 else max latest time_ms
          (stamp, [.emit (.stamped id stamp)])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

def port : Lanes.Clock.Port stampSig where
  asked
    | .ask id => some id
    | .stamped .. => none
  tell id time_ms := .time id time_ms
  told
    | .time id time_ms => some (id, time_ms)
    | .stamp _ => none

/-- Clients ask for each stamp once, and remember the stamps they were given, newest first. -/
def clients : Outside stampSig (List Nat × List Nat) where
  init := ([], [])
  allow d x :=
    match x with
    | .stamp id => if id ∈ d.1 then none else some (id :: d.1, d.2)
    | .time .. => none
  observe d out :=
    match out with
    | .stamped _ time_ms => (d.1, time_ms :: d.2)
    | .ask _ => d

def world := clients.both (Lanes.Clock.outside port) fun x => x matches .stamp ..

instance : stampSig.Inspect := {}
instance (ahead : Bool) : (stamper ahead).Inspect := {}

/-- Two stamps, and a clock that answers each open question with the last time or the next.
The property is not "stamps arrive in order": outputs may be handed over in any order, and the
checker says so if that is claimed. -/
def check (ahead : Bool) :=
  Check.system (stamper ahead)
    { driver := world.driver fun d =>
        [.stamp 0, .stamp 1] ++ d.2.1.flatMap fun id => [.time id d.2.2, .time id (d.2.2 + 1)] }
    [ .always "no stamp is ahead of the clock" fun w => w.driver.1.2.all (· ≤ w.driver.2.2),
      .sometimes "both stamps are given" fun w => w.driver.1.2.length == 2,
      .sometimes "time passes between two stamps" fun w => w.driver.1.2.contains 2 ]

def tests : List (String × Bool) :=
  [ ("clock: no stamp is ahead of the clock, against everything a clock may do",
      (check false).ok),
    ("clock: a stamper that runs ahead of the clock is caught",
      match (check true).failure with
      | some (.violated "no stamp is ahead of the clock" _) => true
      | _ => false) ]

/-- Later than any wall clock will say while this test is of use. -/
def future : Nat := 99999999999999

def live : Async (List (String × Bool)) := do
  let given ← IO.mkRef 0
  let all ← IO.Promise.new
  let past : List (Journal.Entry stampSig) := [.input (.time 0 5), .input (.time 1 future), .handed]
  let clock ← Lanes.Clock.Wall.start (Lanes.Clock.latest port past)
  let rt ← Runtime.startWith stamper { record := true } fun rt _ out => do
    Lanes.Clock.handler clock port rt out
    if out matches .stamped .. then
      if (← given.modifyGet fun n => (n + 1, n + 1)) == 20 then all.resolve ()
  for id in [0:20] do rt.input (.stamp id)
  await all
  rt.idle
  let events := (← rt.trace).toList
  rt.stop
  let stamps := events.filterMap fun
    | .output (.stamped _ time_ms) => some time_ms
    | _ => none
  return [
    ("clock: the real clock does only what its model allows", world.allows events),
    ("clock: every stamp was given, in the order the kernel made them",
      stamps.length == 20 && stamps.Pairwise (· ≤ ·) && stamps.all (· > 0)),
    ("clock: a clock started on a journal gives no time before the last one in it",
      stamps.all (future ≤ ·)) ]

end Tests.Clock
