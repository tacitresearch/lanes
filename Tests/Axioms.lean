/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Examples.BankProofs

/-!
The axiom gate (rule 5.5). Each headline theorem may depend only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one of them, this file stops compiling. It is built
by `lake build`, not linked into the test executable.
-/

/-- info: 'Lanes.System.Reachable.actor' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.Reachable.actor

/-- info: 'Lanes.Refines.of_map' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Refines.of_map

/-- info: 'Lanes.Refines.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Refines.trans

/-- info: 'Lanes.Refines.traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Refines.traces

/-- info: 'Lanes.System.reachable_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.System.reachable_iff

/-- info: 'Lanes.Html.escape_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.escape_safe

/-- info: 'Lanes.SysState.step_of_mem_successors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.step_of_mem_successors

/-- info: 'Examples.Bank.balance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.balance_nonneg

/-- info: 'Examples.Bank.money_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.money_conserved
