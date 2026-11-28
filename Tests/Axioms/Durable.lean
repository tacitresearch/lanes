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

-- Lanes.Durable.Format
/-- info: 'Lanes.Journal.Prelude.check_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Prelude.check_frames

/-- info: 'Lanes.Journal.Prelude.check_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Prelude.check_other

/-- info: 'Lanes.Journal.Kind.formerly_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Kind.formerly_cut

/-- info: 'Lanes.Journal.Prelude.named?_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Prelude.named?_frames

-- Lanes.Durable.Inspect
/-- info: 'Lanes.Journal.inspect_file' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.inspect_file

/-- info: 'Lanes.Journal.inspect_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.inspect_cut

/-- info: 'Lanes.Journal.inspect_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.inspect_saved

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
/-- info: 'Lanes.Journal.replay_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.replay_kernel

/-- info: 'Lanes.Journal.resume_eq_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.resume_eq_replay

/-- info: 'Lanes.Journal.label_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Journal.label_zero

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

/-- info: 'Lanes.Journal.turnAll_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turnAll_spread

/-- info: 'Lanes.Journal.recover_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_kernel

/-- info: 'Lanes.Journal.recover_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recover_outputs

-- Lanes.Durable.Migration
/-- info: 'Lanes.Migration.cell_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Migration.cell_kernel

/-- info: 'Lanes.Migration.inv_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Migration.inv_kernel

/-- info: 'Lanes.Migration.inv_migrated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Migration.inv_migrated

/-- info: 'Lanes.Migration.inv_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Migration.inv_exec

-- Lanes.Durable.OutputId
/-- info: 'Lanes.Journal.placed_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.placed_append

/-- info: 'Lanes.Journal.placed_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.placed_snd

/-- info: 'Lanes.Journal.turn_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turn_placed

/-- info: 'Lanes.Journal.turnAll_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.turnAll_placed

/-- info: 'Lanes.Journal.recoverIds_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recoverIds_erase

/-- info: 'Lanes.Journal.resumeIds_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.resumeIds_erase

/-- info: 'Lanes.Journal.recoverIds_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recoverIds_suffix

/-- info: 'Lanes.Journal.ids_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.ids_append

/-- info: 'Lanes.Journal.recoverIds_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.recoverIds_handed

/-- info: 'Lanes.Journal.resumeIds_eq_recoverIds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.resumeIds_eq_recoverIds

-- Lanes.Durable.Snapshot
/-- info: 'Lanes.Journal.savedOpen?_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.savedOpen?_saved

/-- info: 'Lanes.Journal.saved?_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.saved?_other

/-- info: 'Lanes.Journal.saved?_saved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.saved?_saved

-- Lanes.Durable.Upgrade
/-- info: 'Lanes.Journal.Entry.fits_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Entry.fits_handed

/-- info: 'Lanes.Journal.Disk.open?_of_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.open?_of_read

/-- info: 'Lanes.Journal.Disk.start_foreign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.start_foreign

/-- info: 'Lanes.Journal.Begun.resume_upgraded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Begun.resume_upgraded

/-- info: 'Lanes.Journal.Upgrade.start_torn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.start_torn

/-- info: 'Lanes.Journal.Upgrade.decode_torn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.decode_torn

/-- info: 'Lanes.Journal.Upgrade.begin_torn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.begin_torn

/-- info: 'Lanes.Journal.Upgrade.begin_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.begin_crash

/-- info: 'Lanes.Journal.Upgrade.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.holds

/-- info: 'Lanes.Journal.Upgrade.inv_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.inv_load

/-- info: 'Lanes.Journal.Upgrade.label_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Upgrade.label_snd

-- Lanes.Durable.Reading
/-- info: 'Lanes.Journal.Disk.ofReadings_eq' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.ofReadings_eq

/-- info: 'Lanes.Journal.Disk.Torn.load_readings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Disk.Torn.load_readings

-- Lanes.Durable.Ship
/-- info: 'Lanes.Journal.Ship.Holds.start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Ship.Holds.start

/-- info: 'Lanes.Journal.Ship.Holds.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Ship.Holds.step

/-- info: 'Lanes.Journal.Ship.Holds.take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Ship.Holds.take

/-- info: 'Lanes.Journal.Ship.Holds.put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Ship.Holds.put

/-- info: 'Lanes.Journal.Ship.snapshotOf?_saveWrites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Ship.snapshotOf?_saveWrites

-- Lanes.Durable.Restore
/-- info: 'Lanes.Journal.Restore.piece?_file' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Restore.piece?_file

/-- info: 'Lanes.Journal.Restore.stitch_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Restore.stitch_slice

/-- info: 'Lanes.Journal.Restore.journal_resumeIds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Restore.journal_resumeIds

/-- info: 'Lanes.Journal.Restore.journal_restores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Journal.Restore.journal_restores
