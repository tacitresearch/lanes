/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Examples.BankProofs
import Examples.ElectionProofs
import Examples.KVProofs
import Examples.WatchdogProofs
import Tests.BatchProofs
import Tests.Oracle.Url

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Examples/` and `Tests/`. -/

-- Examples.Bank
/-- info: 'Examples.Bank.balance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.balance_nonneg

-- Examples.BankProofs
/-- info: 'Examples.Bank.money_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Bank.money_conserved

-- Examples.ElectionProofs
/-- info: 'Examples.Election.election_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Election.election_safety

/-- info: 'Examples.Election.atMostOneLeaderPerTerm_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Election.atMostOneLeaderPerTerm_invariant

-- Examples.KVProofs
/-- info: 'Examples.KV.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.KV.implements

/-- info: 'Examples.KV.caching_not_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.KV.caching_not_implements

/-- info: 'Examples.KV.implements_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.KV.implements_once

-- Examples.WatchdogProofs
/-- info: 'Examples.Watchdog.exists_fair_run_never_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Watchdog.exists_fair_run_never_barks

/-- info: 'Examples.Watchdog.impatient_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Examples.Watchdog.impatient_barks

-- Tests.BatchProofs
/-- info: 'Tests.Batch.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements

/-- info: 'Tests.Batch.implements_withPast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements_withPast

-- Tests.Oracle.Url
/-- info: 'Tests.Oracle.Url.resolve_examples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Oracle.Url.resolve_examples
