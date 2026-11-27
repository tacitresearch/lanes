/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.Tutorial.Counter

/-!
Proofs that need the proof layer (CSLib, Mathlib). Nothing executable imports this file, so the
application binary stays small.
-/

namespace Tut

open Lanes

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
