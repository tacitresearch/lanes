/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Data/`. -/

-- Lanes.Data.Codec
/-- info: 'Lanes.Codec.extTreeMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Codec.extTreeMap

-- Lanes.Data.Frame
/-- info: 'Lanes.Frame.encode_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.encode_append

/-- info: 'Lanes.Frame.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_encode

/-- info: 'Lanes.Frame.decode_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_take

/-- info: 'Lanes.Frame.decode_take_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_take_eq

/-- info: 'Lanes.Frame.prefix_decode_encode_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.prefix_decode_encode_append

/-- info: 'Lanes.Frame.decode_extract_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_extract_prefix

/-- info: 'Lanes.Frame.decode_checksum_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Frame.decode_checksum_ne

-- Lanes.Data.Quorum
/-- info: 'Lanes.Quorum.majority_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Quorum.majority_inter
