/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Durable/`. -/

-- Lanes.Durable.Disk
/-- info: 'Lanes.Journal.Disk.load_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.load_cut

/-- info: 'Lanes.Journal.Disk.read_of_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.read_of_start

/-- info: 'Lanes.Journal.Disk.torn_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.torn_nil

/-- info: 'Lanes.Journal.Disk.Torn.load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.load

/-- info: 'Lanes.Journal.Disk.Torn.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.read

/-- info: 'Lanes.Journal.Disk.Torn.mend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.mend

/-- info: 'Lanes.Journal.Disk.Torn.mend_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.mend_crash

/-- info: 'Lanes.Journal.Disk.Holds.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.append

/-- info: 'Lanes.Journal.Disk.Holds.append_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.append_crash

/-- info: 'Lanes.Journal.Disk.Holds.save' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.save

/-- info: 'Lanes.Journal.Disk.Holds.save_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.save_crash

/-- info: 'Lanes.Journal.Disk.Holds.load_append_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.load_append_crash

/-- info: 'Lanes.Journal.Disk.Holds.load_save_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Holds.load_save_crash

-- Lanes.Durable.Frame
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

-- Lanes.Durable.Journal
/-- info: 'Lanes.Journal.open?_file' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.open?_file

/-- info: 'Lanes.Journal.open?_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.open?_cut

/-- info: 'Lanes.Journal.recover_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_handed

/-- info: 'Lanes.Journal.resume_eq_recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.resume_eq_recover

/-- info: 'Lanes.Journal.turns_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turns_kernel

/-- info: 'Lanes.Journal.turnAll_eq_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turnAll_eq_exec

/-- info: 'Lanes.Journal.recover_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_kernel

/-- info: 'Lanes.Journal.recover_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_outputs

-- Lanes.Durable.Snapshot
/-- info: 'Lanes.Journal.saved?_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.saved?_saved
