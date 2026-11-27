/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Web/`. -/

-- Lanes.Web.Auth.IdToken
/-- info: 'Lanes.OAuth.IdToken.check_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.IdToken.check_ok_iff

/-- info: 'Lanes.OAuth.IdToken.verify_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.IdToken.verify_accepted

-- Lanes.Web.Auth.Jose
/-- info: 'Lanes.Jose.Alg.parse?_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jose.Alg.parse?_eq_some

/-- info: 'Lanes.Jose.readHeader_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jose.readHeader_alg

/-- info: 'Lanes.Jose.Compact.read_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jose.Compact.read_alg

/-- info: 'Lanes.Jose.verify_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Jose.verify_ok

-- Lanes.Web.Auth.Login
/-- info: 'Lanes.Auth.Attempts.bounded_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Attempts.bounded_fail

/-- info: 'Lanes.Auth.Attempts.bounded_succeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Attempts.bounded_succeed

/-- info: 'Lanes.Auth.Attempts.fail_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Attempts.fail_repeat

/-- info: 'Lanes.Auth.Attempts.locked_unlock_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Attempts.locked_unlock_repeat

/-- info: 'Lanes.Auth.Attempts.locked_stays' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Auth.Attempts.locked_stays

/-- info: 'Lanes.Auth.Sessions.length_start_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.length_start_le

/-- info: 'Lanes.Auth.Sessions.live_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.live_open

/-- info: 'Lanes.Auth.Sessions.start_kept_closed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.start_kept_closed

/-- info: 'Lanes.Auth.Sessions.ids_starts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.ids_starts

/-- info: 'Lanes.Auth.Sessions.live_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.live_close

-- Lanes.Web.Auth.OAuth
/-- info: 'Lanes.OAuth.same_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.same_iff

/-- info: 'Lanes.OAuth.Pending.length_begin' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.OAuth.Pending.length_begin

/-- info: 'Lanes.OAuth.Pending.callback_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Pending.callback_ok

/-- info: 'Lanes.OAuth.Pending.callback_removes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Pending.callback_removes

/-- info: 'Lanes.OAuth.Pending.callback_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Pending.callback_sublist

/-- info: 'Lanes.OAuth.Pending.accepted_le_issued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Pending.accepted_le_issued

/-- info: 'Lanes.OAuth.Keys.lookup_fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Keys.lookup_fetch

/-- info: 'Lanes.OAuth.Keys.no_fetch_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Keys.no_fetch_within

/-- info: 'Lanes.OAuth.identity?_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.identity?_strip

/-- info: 'Lanes.OAuth.identity?_withIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.identity?_withIdentity

-- Lanes.Web.Auth.Token
/-- info: 'Lanes.Auth.verify_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_sign

/-- info: 'Lanes.Auth.checkForm_formToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.checkForm_formToken

-- Lanes.Web.Auth.TokenSound
/-- info: 'Lanes.Auth.verify_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_eq_some

/-- info: 'Lanes.Auth.message_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.message_inj

/-- info: 'Lanes.Auth.verify_sign_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_sign_other

/-- info: 'Lanes.Auth.checkForm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.checkForm_iff

/-- info: 'Lanes.Auth.checkForm_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.checkForm_other

-- Lanes.Web.Html.Basic
/-- info: 'Lanes.Html.escape_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.escape_safe

-- Lanes.Web.Html.BasicSound
/-- info: 'Lanes.Html.lex_render' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.lex_render

/-- info: 'Lanes.Html.nameChar_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.nameChar_safe

/-- info: 'Lanes.Html.mem_safeName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.mem_safeName

/-- info: 'Lanes.Html.render_void' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.render_void

/-- info: 'Lanes.Html.safeUrl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.safeUrl_eq

/-- info: 'Lanes.Html.safeUrl_scheme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Html.safeUrl_scheme

-- Lanes.Web.Html.HtmxSound
/-- info: 'Lanes.Hx.methodAttr_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Hx.methodAttr_inj

/-- info: 'Lanes.Hx.request_match?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Hx.request_match?

/-- info: 'Lanes.Hx.mem_eventName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Hx.mem_eventName

/-- info: 'Lanes.Hx.eventName_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Hx.eventName_plain

/-- info: 'Lanes.Hx.render_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Hx.render_plain

-- Lanes.Web.Http.Basic
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

-- Lanes.Web.Http.ConnSound
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

-- Lanes.Web.Http.CookieSound
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

-- Lanes.Web.Http.Front
/-- info: 'Lanes.Http.gateActor_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.gateActor_bounded

-- Lanes.Web.Http.FrontSound
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

-- Lanes.Web.Http.Gate
/-- info: 'Lanes.Http.Gate.step_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.step_bounded

-- Lanes.Web.Http.Grammar
/-- info: 'Lanes.Http.visible_of_tokenChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.visible_of_tokenChar

/-- info: 'Lanes.Http.plain_of_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.plain_of_visible

-- Lanes.Web.Http.Ops
/-- info: 'Lanes.Http.Ops.route?_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.route?_default

/-- info: 'Lanes.Http.Ops.route?_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.route?_some

/-- info: 'Lanes.Http.Ops.answer_ready' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Ops.answer_ready

/-- info: 'Lanes.Http.Ops.lookup_bumpKey' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Http.Ops.lookup_bumpKey

/-- info: 'Lanes.Http.Ops.RequestId.accept?_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.RequestId.accept?_eq_some

/-- info: 'Lanes.Http.Ops.RequestId.accept?_ofBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.RequestId.accept?_ofBytes

/-- info: 'Lanes.Http.Ops.RequestId.header_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.RequestId.header_tag

-- Lanes.Web.Http.OpsSound
/-- info: 'Lanes.Http.Ops.Access.parse_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.Access.parse_line

-- Lanes.Web.Http.ReadRequestSound
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

-- Lanes.Web.Http.Route
/-- info: 'Lanes.Http.Route.match?_link' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Http.Route.match?_link

-- Lanes.Web.Http.RouteSound
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

-- Lanes.Web.Http.Waiting
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

-- Lanes.Web.Http.Wire
/-- info: 'Lanes.Http.Request.fields_framing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.fields_framing

/-- info: 'Lanes.Http.Request.head_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.head_plain

/-- info: 'Lanes.Http.Request.fields_token' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.fields_token

/-- info: 'Lanes.Http.Request.target_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.target_visible

/-- info: 'Lanes.Http.Response.read_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.read_ended

-- Lanes.Web.Http.WireSound
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
