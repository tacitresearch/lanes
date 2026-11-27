/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.BatchProofs
import Tests.Fixtures.BankProofs
import Tests.Fixtures.ElectionProofs
import Tests.Fixtures.KVProofs
import Tests.Fixtures.WatchdogProofs
import Tests.Oracle.Url

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Tests/`, the fixtures included. -/

-- Tests.Fixtures.Bank
/-- info: 'Tests.Fixtures.Bank.balance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Bank.balance_nonneg

-- Tests.Fixtures.BankProofs
/-- info: 'Tests.Fixtures.Bank.money_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Bank.money_conserved

-- Tests.Fixtures.ElectionProofs
/-- info: 'Tests.Fixtures.Election.election_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Election.election_safety

/-- info: 'Tests.Fixtures.Election.atMostOneLeaderPerTerm_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Election.atMostOneLeaderPerTerm_invariant

-- Tests.Fixtures.KVProofs
/-- info: 'Tests.Fixtures.KV.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.KV.implements

/-- info: 'Tests.Fixtures.KV.caching_not_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.KV.caching_not_implements

/-- info: 'Tests.Fixtures.KV.implements_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.KV.implements_once

-- Tests.Fixtures.WatchdogProofs
/-- info: 'Tests.Fixtures.Watchdog.exists_fair_run_never_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Watchdog.exists_fair_run_never_barks

/-- info: 'Tests.Fixtures.Watchdog.impatient_barks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Watchdog.impatient_barks

-- Tests.BatchProofs
/-- info: 'Tests.Batch.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements

/-- info: 'Tests.Batch.implements_withPast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements_withPast

-- Tests.Oracle.Url
/-- info: 'Tests.Oracle.Url.resolve_examples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Oracle.Url.resolve_examples
