/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.Tutorial.Counter

/-!
The theorems. Nothing executable imports this file, so the application binary stays small, and
`Check.lean` does not, so a broken proof does not stop the checks: `lake test` runs the checks,
then builds this file with warnings as errors, and a `sorry` fails it.
-/

namespace Tut

open Lanes

/-- The counter never exceeds its limit. -/
theorem counter_le_limit (config : Config) :
    (Server.actor (service config)).Invariant fun count => count ≤ config.limit := by
  actor_invariant [Server.actor, service]

/-- In every reachable state of the system, under any environment model. -/
theorem system_le_limit (config : Config) (env : EnvModel sig) :
    (system config).Invariant env fun c => c.state () ≤ config.limit :=
  System.invariant_of_actor (system config) () (counter_le_limit config) env

/--
The running system implements the spec: whatever concurrent clients observe is a behaviour of
`service` with each request taking effect at one instant. It holds in any environment that
loses, duplicates and crashes nothing, which is what the runtime provides inside one process.
-/
theorem implements (config : Config) (env : EnvModel sig) (henv : env.Faultless) :
    (system config).Implements env (service config) :=
  Server.implements (service config) env henv

end Tut

/-- info: 'Tut.system_le_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.system_le_limit

/-- info: 'Tut.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tut.implements
