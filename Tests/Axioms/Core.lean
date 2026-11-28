/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Core/`. -/

-- Lanes.Core.Inspect
/-- info: 'Lanes.SysState.step_of_mem_successors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.step_of_mem_successors

-- Lanes.Core.Run
/-- info: 'Lanes.SysState.step_ahead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.step_ahead

/-- info: 'Lanes.SysState.nextOnLink_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.nextOnLink_spec

/-- info: 'Lanes.SysState.mem_net_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SysState.mem_net_of_step

-- Lanes.Core.Step
/-- info: 'Lanes.SysState.step_restart' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.SysState.step_restart

/-- info: 'Lanes.System.reachable_withoutRestarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.reachable_withoutRestarts

/-- info: 'Lanes.System.Invariant.of_withoutRestarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.of_withoutRestarts

/-- info: 'Lanes.System.Invariant.restarts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.System.Invariant.restarts
