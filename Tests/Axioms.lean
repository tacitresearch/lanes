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

/-- info: 'Lanes.SysState.mem_successors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.mem_successors_iff

/-- info: 'Lanes.Kernel.abs_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.abs_boot

/-- info: 'Lanes.Kernel.accept_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.accept_sound

/-- info: 'Lanes.Kernel.run1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.run1_sound

/-- info: 'Lanes.Kernel.fire_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.fire_sound

/-- info: 'Lanes.Http.gate_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.gate_bounded

/-- info: 'Lanes.Http.Route.match?_link' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Http.Route.match?_link

/-- info: 'Lanes.Http.percentDecode_percentEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.percentDecode_percentEncode

/-- info: 'Lanes.Kernel.exec_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Kernel.exec_reachable

/-- info: 'Lanes.System.Inductive.of_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Inductive.of_monotone

/-- info: 'Lanes.SysState.erase_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.erase_step

/-- info: 'Lanes.System.Invariant.of_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.of_ghost

/-- info: 'Lanes.Quorum.majority_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Quorum.majority_inter

/-- info: 'Lanes.SysState.Equiv.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.Equiv.step

/-- info: 'Lanes.SysState.equiv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.equiv_iff

/-- info: 'Lanes.World.Equiv.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.World.Equiv.next

/-- info: 'Lanes.Server.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Server.implements

/-- info: 'Lanes.Check.Monitor.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.sound

/-- info: 'Lanes.Check.Monitor.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.complete

/-- info: 'Lanes.Check.Monitor.ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.Monitor.ok_iff

/-- info: 'Examples.Bank.balance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.balance_nonneg

/-- info: 'Examples.Bank.money_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.money_conserved

/-- info: 'Lanes.Check.search_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_violated

/-- info: 'Lanes.Check.search_deadlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_deadlock

/-- info: 'Lanes.Check.search_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_witness

/-- info: 'Lanes.Check.search_states_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_states_le

/-- info: 'Lanes.Check.search_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_sound

/-- info: 'Lanes.Check.search_sound_of_lawful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_sound_of_lawful

/-- info: 'Lanes.Check.search_unreached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_unreached

/-- info: 'Lanes.Check.search_deadlock_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_deadlock_free

/-- info: 'Lanes.Check.search_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Check.search_reached
