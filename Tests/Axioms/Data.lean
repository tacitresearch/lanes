/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Data/`. -/

-- Lanes.Data.BodySound
/-- info: 'Lanes.Body.read_eq_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Body.read_eq_ok_iff
/-- info: 'Lanes.Body.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Body.decode_encode
/-- info: 'Lanes.Body.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Body.encode_decode
/-- info: 'Lanes.Body.readAny_writeAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Body.readAny_writeAny

-- Lanes.Data.MatchSound
/-- info: 'Lanes.Body.decodeWith_encode_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Body.decodeWith_encode_self
/-- info: 'Lanes.Schema.Plan.of_insertIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schema.Plan.of_insertIdx
/-- info: 'Lanes.Schema.Plan.of_rename' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schema.Plan.of_rename
/-- info: 'Lanes.Body.decodeWith_migrate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Body.decodeWith_migrate

-- Lanes.Data.Codec
/-- info: 'Lanes.Codec.extTreeMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Codec.extTreeMap

-- Lanes.Data.Declare
/-- info: 'Lanes.Migrate.migrate_same' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Migrate.migrate_same

-- Lanes.Data.Schema
/-- info: 'Lanes.Schema.ofValue?_toValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Schema.ofValue?_toValue

-- Lanes.Data.Quorum
/-- info: 'Lanes.Quorum.majority_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Quorum.majority_inter
