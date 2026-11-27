/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.BatchProofs
import Tests.Fixtures.BankProofs
import Tests.Oracle.Url

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Tests/`, the fixtures included. -/

-- Tests.Fixtures.Bank
/-- info: 'Tests.Fixtures.Bank.balance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Bank.balance_nonneg

-- Tests.Fixtures.BankProofs
/-- info: 'Tests.Fixtures.Bank.money_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Fixtures.Bank.money_conserved

-- Tests.BatchProofs
/-- info: 'Tests.Batch.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements

/-- info: 'Tests.Batch.implements_withPast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Batch.implements_withPast

-- Tests.Oracle.Url
/-- info: 'Tests.Oracle.Url.resolve_examples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.Oracle.Url.resolve_examples
