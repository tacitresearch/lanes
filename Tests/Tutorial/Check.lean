/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Tutorial.Counter

/-!
Step 3 of `docs/TUTORIAL.md`: the model check of the app's `Check.lean`, run on the counter and
on the counter with the step's bug.
-/

namespace Tests.Tutorial

open Lanes Tut

instance : sig.Inspect := {}
instance (svc : Service sig.In sig.Out Nat) : (Server.system svc).Inspect := {}

def requests : List Request :=
  [.increment 1, .increment 2, .increment 3, .decrement 4]

/-- The bug the tutorial seeds: a decrement at one is refused. -/
def buggy (config : Config) : Service sig.In sig.Out Nat where
  init := 0
  step count
    | .decrement req =>
      if 1 < count then (count - 1, [⟨req, count - 1, true⟩])
      else (count, [⟨req, count, false⟩])
    | r => (service config).step count r

def report (service : Config → Service sig.In sig.Out Nat) :=
  Check.system (Server.system (service { limit := 2 }))
    { driver := (service { limit := 2 }).monitored (Driver.anyOrder requests)
      env := { mayCrash := fun _ => true }
      maxCrashes := 1 }
    [ Check.refines "every response is allowed by the spec",
      .always "the counter never exceeds its limit" fun w => w.state.state () ≤ 2,
      .sometimes "the counter reaches its limit" fun w => w.state.state () == 2,
      .sometimes "an increment is refused" fun w =>
        w.state.outbox.any fun r => !r.applied && r.value == 2,
      .always "a request is refused only at zero or at the limit" fun w =>
        w.state.outbox.all fun r => r.applied || r.value == 0 || r.value == 2,
      .sometimes "a decrement is refused" fun w =>
        w.state.outbox.any fun r => !r.applied && r.value == 0 ]

end Tests.Tutorial
