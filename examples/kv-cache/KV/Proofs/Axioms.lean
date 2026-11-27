/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KV.Proofs

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'KV.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KV.implements

/-- info: 'KV.caching_not_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KV.caching_not_implements

/-- info: 'KV.implements_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KV.implements_once
