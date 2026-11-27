/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Http/`. -/

-- Lanes.Http.Basic
/-- info: 'Lanes.Http.percentDecode_percentEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.percentDecode_percentEncode

/-- info: 'Lanes.Http.percentEncode_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.percentEncode_plain

/-- info: 'Lanes.Http.parseForm_encodeForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.parseForm_encodeForm

/-- info: 'Lanes.Http.Request.param?_eq_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.param?_eq_lookup

/-- info: 'Lanes.Http.Request.header?_eq_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.header?_eq_lookup

/-- info: 'Lanes.Http.Request.field?_eq_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.field?_eq_lookup

/-- info: 'Lanes.Http.Request.form_encodeForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.form_encodeForm

-- Lanes.Http.CookieSound
/-- info: 'Lanes.Http.readSetCookie_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.readSetCookie_header

/-- info: 'Lanes.Http.setCookie_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.setCookie_read

/-- info: 'Lanes.Http.parseCookies_cookieHeader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.parseCookies_cookieHeader

/-- info: 'Lanes.Http.Request.sameOrigin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.sameOrigin_iff

/-- info: 'Lanes.Http.Request.bodyWithin_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Request.bodyWithin_iff

-- Lanes.Http.ConnSound
/-- info: 'Lanes.Http.Conn.wantsInput_room' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Conn.wantsInput_room

/-- info: 'Lanes.Http.Conn.run_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.run_writes

/-- info: 'Lanes.Http.Conn.run_submits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.run_submits

/-- info: 'Lanes.Http.Conn.run_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.run_buffer

/-- info: 'Lanes.Http.Conn.run_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.run_slots

/-- info: 'Lanes.Http.Conn.step_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.step_closed

/-- info: 'Lanes.Http.Conn.step_notReading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.step_notReading

/-- info: 'Lanes.Http.Conn.step_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.step_reading

/-- info: 'Lanes.Http.Conn.step_tick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.step_tick

/-- info: 'Lanes.Http.Conn.answer_ignored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.answer_ignored

/-- info: 'Lanes.Http.Conn.answer_waiting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.answer_waiting

/-- info: 'Lanes.Http.Conn.step_submit_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.step_submit_read

/-- info: 'Lanes.Http.Conn.sendable_writable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.sendable_writable

/-- info: 'Lanes.Http.Conn.read_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.read_encode

/-- info: 'Lanes.Http.Conn.Count.admit_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Conn.Count.admit_le

/-- info: 'Lanes.Http.Conn.Count.admit_stopping' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Conn.Count.admit_stopping

-- Lanes.Http.Front
/-- info: 'Lanes.Http.gateActor_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.gateActor_bounded

-- Lanes.Http.FrontSound
/-- info: 'Lanes.Http.Gate.answered_le_handled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.answered_le_handled

/-- info: 'Lanes.Http.fronted_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_answered_le_arrived

/-- info: 'Lanes.Http.fronted_answered_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_answered_nodup

/-- info: 'Lanes.Http.Gate.deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.deadlines_armed

/-- info: 'Lanes.Http.fronted_deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.fronted_deadlines_armed

/-- info: 'Lanes.Http.kernel_fronted_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.kernel_fronted_answered_le_arrived

/-- info: 'Lanes.Http.served_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_answered_le_arrived

/-- info: 'Lanes.Http.served_answered_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_answered_nodup

/-- info: 'Lanes.Http.kernel_served_answered_le_arrived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.kernel_served_answered_le_arrived

/-- info: 'Lanes.Http.served_deadlines_armed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.served_deadlines_armed

-- Lanes.Http.Gate
/-- info: 'Lanes.Http.Gate.step_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.step_bounded

-- Lanes.Http.MediaTypeSound
/-- info: 'Lanes.MediaType.parse_format' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.parse_format

/-- info: 'Lanes.MediaType.parse_format_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.parse_format_eq

/-- info: 'Lanes.MediaType.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.MediaType.parse_print

-- Lanes.Http.ReadRequestSound
/-- info: 'Lanes.Http.findL_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.findL_lines

/-- info: 'Lanes.Http.Request.read_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_extract

/-- info: 'Lanes.Http.Request.read_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_append

/-- info: 'Lanes.Http.Request.read_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_more

/-- info: 'Lanes.Http.Request.read_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_done

/-- info: 'Lanes.Http.Request.read_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_wire

/-- info: 'Lanes.Http.Request.read_wire_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_wire_extract

/-- info: 'Lanes.Http.Request.readHead_headWire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.readHead_headWire

/-- info: 'Lanes.Http.Request.read_lengthAndCoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_lengthAndCoding

/-- info: 'Lanes.Http.Request.read_twoLengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_twoLengths

/-- info: 'Lanes.Http.Request.read_blankInName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_blankInName

/-- info: 'Lanes.Http.Request.read_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_fold

/-- info: 'Lanes.Http.Request.read_bareCR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_bareCR

/-- info: 'Lanes.Http.Request.read_bareLF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_bareLF

/-- info: 'Lanes.Http.Request.read_badChunkSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.read_badChunkSize

-- Lanes.Http.Route
/-- info: 'Lanes.Http.Route.match?_link' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Http.Route.match?_link

-- Lanes.Http.RouteSound
/-- info: 'Lanes.Http.Slug.ofString?_text' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Slug.ofString?_text

/-- info: 'Lanes.Http.Slug.ofString?_eq_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Slug.ofString?_eq_some

/-- info: 'Lanes.Http.Route.link_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Route.link_target

/-- info: 'Lanes.Http.Route.match?_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Route.match?_target

/-- info: 'Lanes.Http.dispatch_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.dispatch_eq_some

/-- info: 'Lanes.Http.dispatch_eq_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.dispatch_eq_none

/-- info: 'Lanes.Http.dispatch_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.dispatch_link

-- Lanes.Http.UrlSound
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

-- Lanes.Http.Waiting
/-- info: 'Lanes.Http.Waiting.exec_handed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_handed

/-- info: 'Lanes.Http.Waiting.exec_handed_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_handed_nodup

/-- info: 'Lanes.Http.Waiting.exec_waiting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_waiting

/-- info: 'Lanes.Http.Waiting.exec_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_answered

/-- info: 'Lanes.Http.Waiting.exec_drain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Waiting.exec_drain

-- Lanes.Http.Wire
/-- info: 'Lanes.Http.Request.fields_framing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.fields_framing

/-- info: 'Lanes.Http.Request.head_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.head_plain

/-- info: 'Lanes.Http.Response.read_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_ended

-- Lanes.Http.WireSound
/-- info: 'Lanes.Http.Response.read_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_more

/-- info: 'Lanes.Http.Response.read_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_some

/-- info: 'Lanes.Http.Response.read_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_append

/-- info: 'Lanes.Http.Response.read_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wire

/-- info: 'Lanes.Http.Response.read_wire_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wire_extract

/-- info: 'Lanes.Http.Response.read_wireChunked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireChunked

/-- info: 'Lanes.Http.Response.read_wireChunked_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireChunked_extract

/-- info: 'Lanes.Http.Response.read_wireAfter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireAfter

/-- info: 'Lanes.Http.Response.read_wireAfter_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireAfter_extract

/-- info: 'Lanes.Http.Response.read_wireToEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireToEnd

/-- info: 'Lanes.Http.Response.read_wireToEnd_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_wireToEnd_open
