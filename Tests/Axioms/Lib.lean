/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Lib/`. -/

-- Lanes.Lib.Crypto.Hmac
/-- info: 'Lanes.Bytes.unhex?_hex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Bytes.unhex?_hex

-- Lanes.Lib.Encoding.Base64
/-- info: 'Lanes.Base64.decode_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Base64.decode_eq_some_iff

/-- info: 'Lanes.Base64.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Base64.decode_encode

/-- info: 'Lanes.Base64.allowed_of_mem_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Base64.allowed_of_mem_encode

/-- info: 'Lanes.Base64.length_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Base64.length_encode

/-- info: 'Lanes.Base64.decode_eq_none_of_not_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Base64.decode_eq_none_of_not_allowed

/-- info: 'Lanes.Base64.decode_eq_none_of_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Base64.decode_eq_none_of_length

-- Lanes.Lib.Encoding.Digits
/-- info: 'Lanes.Digits.ofChars?_toChars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Digits.ofChars?_toChars

/-- info: 'Lanes.Digits.ofChars?_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Digits.ofChars?_fixed

/-- info: 'Lanes.Digits.head_toChars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Digits.head_toChars

/-- info: 'Lanes.Digits.join_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Digits.join_split

-- Lanes.Lib.Encoding.Json.BasicSound
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

/-- info: 'Lanes.Json.getObjVal?_mkObj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Json.getObjVal?_mkObj

-- Lanes.Lib.Encoding.Json.Classes
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

-- Lanes.Lib.Encoding.Json.ParserSound
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

-- Lanes.Lib.Encoding.Json.PrinterSound
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

-- Lanes.Lib.Mime.MediaTypeSound
/-- info: 'Lanes.MediaType.parse_format' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.parse_format

/-- info: 'Lanes.MediaType.parse_format_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.parse_format_eq

/-- info: 'Lanes.MediaType.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.parse_print

/-- info: 'Lanes.MediaType.isQdtext_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.isQdtext_of

/-- info: 'Lanes.MediaType.quoted_esc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.quoted_esc

-- Lanes.Lib.Net.Ip
/-- info: 'Lanes.Ip.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Ip.parse_print

/-- info: 'Lanes.Ip.longestZeroRun_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Ip.longestZeroRun_some

/-- info: 'Lanes.Ip.longestZeroRun_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Ip.longestZeroRun_none

/-- info: 'Lanes.Ip.Prefix.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Ip.Prefix.parse_print

/-- info: 'Lanes.Ip.Prefix.contains_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Ip.Prefix.contains_iff

/-- info: 'Lanes.Ip.Prefix.masked_masked' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Ip.Prefix.masked_masked

/-- info: 'Lanes.Ip.Prefix.contains_masked' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Ip.Prefix.contains_masked

-- Lanes.Lib.Net.UrlSound
/-- info: 'Lanes.Url.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.parse_print

/-- info: 'Lanes.Url.parse_print_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.parse_print_of_valid

/-- info: 'Lanes.Url.dotFree_removeDots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.dotFree_removeDots

/-- info: 'Lanes.Url.removeDots_of_dotFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.removeDots_of_dotFree

/-- info: 'Lanes.Url.removeDots_removeDots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.removeDots_removeDots

/-- info: 'Lanes.Url.resolve_of_scheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.resolve_of_scheme

/-- info: 'Lanes.Url.resolve_of_absolute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.resolve_of_absolute

/-- info: 'Lanes.Url.dotFree_resolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.dotFree_resolve

/-- info: 'Lanes.Url.normalize_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Url.normalize_normalize

-- Lanes.Lib.Postgres.ConnSound
/-- info: 'Lanes.Postgres.Conn.run_fifo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.run_fifo

/-- info: 'Lanes.Postgres.Conn.step_fifo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_fifo

/-- info: 'Lanes.Postgres.Conn.outcome_committed' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.outcome_committed

/-- info: 'Lanes.Postgres.Conn.step_committed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_committed

/-- info: 'Lanes.Postgres.Conn.step_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_query

/-- info: 'Lanes.Postgres.Conn.valid_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.valid_decode

/-- info: 'Lanes.Postgres.Conn.step_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_closed

/-- info: 'Lanes.Postgres.Conn.step_lost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_lost

/-- info: 'Lanes.Postgres.Conn.run_queue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.run_queue

/-- info: 'Lanes.Postgres.Conn.start_queue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.start_queue

/-- info: 'Lanes.Postgres.Conn.step_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_buffer

/-- info: 'Lanes.Postgres.Conn.onMessage_saslFinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_saslFinal

/-- info: 'Lanes.Postgres.Conn.onMessage_sasl_authOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_sasl_authOk

/-- info: 'Lanes.Postgres.Conn.onMessage_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_opened

-- Lanes.Lib.Postgres.MessageSound
/-- info: 'Lanes.Postgres.Backend.read_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Backend.read_encode

/-- info: 'Lanes.Postgres.Backend.decodeBody_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Backend.decodeBody_body

/-- info: 'Lanes.Postgres.Frontend.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Frontend.decode_encode

/-- info: 'Lanes.Postgres.Frame.read_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Frame.read_more

/-- info: 'Lanes.Postgres.Frame.read_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Frame.read_done

-- Lanes.Lib.Postgres.Scram
/-- info: 'Lanes.Postgres.Scram.respond_nonce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Scram.respond_nonce

/-- info: 'Lanes.Postgres.Scram.respond_iterations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Scram.respond_iterations

-- Lanes.Lib.RateLimit
/-- info: 'Lanes.RateLimit.credit_allow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.RateLimit.credit_allow_le

/-- info: 'Lanes.RateLimit.credit_reserve_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.RateLimit.credit_reserve_le

/-- info: 'Lanes.RateLimit.credit_allowAll_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.RateLimit.credit_allowAll_le

/-- info: 'Lanes.RateLimit.allowed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.RateLimit.allowed_le

/-- info: 'Lanes.RateLimit.allow_after_reserve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.RateLimit.allow_after_reserve

-- Lanes.Lib.Time.Civil
/-- info: 'Lanes.Civil.ofDays_toDays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Civil.ofDays_toDays

/-- info: 'Lanes.Civil.toDays_ofDays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Civil.toDays_ofDays

/-- info: 'Lanes.Civil.ofUnix_toUnix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Civil.ofUnix_toUnix

/-- info: 'Lanes.Civil.toUnix_ofUnix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Civil.toUnix_ofUnix

-- Lanes.Lib.Time.Format
/-- info: 'Lanes.TimeFormat.parseRfc3339_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.TimeFormat.parseRfc3339_print

/-- info: 'Lanes.TimeFormat.parseHttpDate_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.TimeFormat.parseHttpDate_print
