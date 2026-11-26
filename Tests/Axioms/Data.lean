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

-- Lanes.Data.Json.BasicSound
/-- info: 'Lanes.Json.isNull_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.isNull_iff

/-- info: 'Lanes.Json.getBool?_eq_ok' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.getBool?_eq_ok

/-- info: 'Lanes.Json.getStr?_eq_ok' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.getStr?_eq_ok

/-- info: 'Lanes.Json.getNum?_eq_ok' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.getNum?_eq_ok

/-- info: 'Lanes.Json.getArr?_eq_ok' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.getArr?_eq_ok

/-- info: 'Lanes.Json.getObj?_eq_ok' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.getObj?_eq_ok

/-- info: 'Lanes.Json.getInt?_eq_ok' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Json.getInt?_eq_ok

/-- info: 'Lanes.Json.getNat?_eq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.getNat?_eq_ok

/-- info: 'Lanes.Json.getArrVal?_eq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.getArrVal?_eq_ok

/-- info: 'Lanes.Json.getObjVal?_eq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.getObjVal?_eq_ok

-- Lanes.Data.Json.Classes
/-- info: 'Lanes.fromJson?_toJson_json' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_json

/-- info: 'Lanes.fromJson?_toJson_jsonNumber' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_jsonNumber

/-- info: 'Lanes.fromJson?_toJson_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_unit

/-- info: 'Lanes.fromJson?_toJson_bool' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_bool

/-- info: 'Lanes.fromJson?_toJson_nat' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_nat

/-- info: 'Lanes.fromJson?_toJson_int' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_int

/-- info: 'Lanes.fromJson?_toJson_string' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_string

/-- info: 'Lanes.fromJson?_toJson_fin' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_fin

/-- info: 'Lanes.fromJson?_toJson_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_array

/-- info: 'Lanes.fromJson?_toJson_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_list

/-- info: 'Lanes.fromJson?_toJson_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_prod

/-- info: 'Lanes.fromJson?_toJson_none' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_none

/-- info: 'Lanes.fromJson?_toJson_some' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.fromJson?_toJson_some

-- Lanes.Data.Json.ParserSound
/-- info: 'Lanes.Json.Parser.rest_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.Parser.rest_next

/-- info: 'Lanes.Json.Parser.rest_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.Parser.rest_eq_nil

/-- info: 'Lanes.Json.parse_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.parse_complete

/-- info: 'Lanes.Json.parse_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.parse_sound

/-- info: 'Lanes.Json.parse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.parse_iff

/-- info: 'Lanes.Json.parse_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.parse_compress

/-- info: 'Lanes.Json.parse_pretty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.parse_pretty

-- Lanes.Data.Json.PrinterSound
/-- info: 'Lanes.Json.text_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.text_compress

/-- info: 'Lanes.Json.text_pretty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.text_pretty

/-- info: 'Lanes.Json.fromUTF8?_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.fromUTF8?_compress

/-- info: 'Lanes.Json.fromUTF8?_pretty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.fromUTF8?_pretty

/-- info: 'Lanes.Json.number_toString' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.number_toString

/-- info: 'Lanes.Json.ofScientific_mantissa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.ofScientific_mantissa

-- Lanes.Data.Quorum
/-- info: 'Lanes.Quorum.majority_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Quorum.majority_inter
