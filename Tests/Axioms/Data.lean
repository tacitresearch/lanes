/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Data/`. -/

-- Lanes.Data.Fifo
/-- info: 'Lanes.Fifo.length_toList' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Fifo.length_toList
