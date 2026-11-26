/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Inspect

/-!
`instance_by_cases` gives an instance for a family defined by cases on an identity, such as the
messages of a system whose actors differ: `∀ i, DecidableEq (Msg i)`, and the `Inspect` of a
signature or a system whose messages or states depend on the identity. It takes the identity
apart and finds the instance in each case, which instance search alone does not do.
-/

@[expose] public section

namespace Lanes

/-- `instance : ∀ i, C (F i) := by instance_by_cases`, and
`instance : sys.Inspect := by instance_by_cases`. -/
syntax (name := instanceByCases) "instance_by_cases" : tactic

macro_rules
  | `(tactic| instance_by_cases) => `(tactic| first
    | (intro i; first | infer_instance | (cases i <;> infer_instance))
    | exact {}
    | exact { reprMsg := by instance_by_cases, hashMsg := by instance_by_cases }
    | exact { beqState := by instance_by_cases, reprState := by instance_by_cases,
              hashState := by instance_by_cases })

end Lanes
