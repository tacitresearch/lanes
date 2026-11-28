/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Web/`. -/

-- Lanes.Web.Auth.IdToken
/-- info: 'Lanes.OAuth.DisplayName.length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.DisplayName.length_le

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

/-- info: 'Lanes.Auth.Sessions.start_kept_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.start_kept_closed

/-- info: 'Lanes.Auth.Sessions.ids_starts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.ids_starts

/-- info: 'Lanes.Auth.Sessions.live_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.live_close

/-- info: 'Lanes.Auth.Session.expired_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Session.expired_mono

/-- info: 'Lanes.Auth.Sessions.length_close_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.length_close_le

/-- info: 'Lanes.Auth.Sessions.accepts_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.accepts_iff

/-- info: 'Lanes.Auth.Sessions.sweep_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.sweep_ended

/-- info: 'Lanes.Auth.Sessions.Ended.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Sessions.Ended.run

-- Lanes.Web.Auth.OAuth
/-- info: 'Lanes.OAuth.same_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.same_iff

/-- info: 'Lanes.OAuth.check_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.check_ok

/-- info: 'Lanes.OAuth.Used.length_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Used.length_claim

/-- info: 'Lanes.OAuth.Used.claim_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Used.claim_ok

/-- info: 'Lanes.OAuth.Used.claim_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Used.claim_holds

/-- info: 'Lanes.OAuth.Used.claim_ok_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Used.claim_ok_holds

/-- info: 'Lanes.OAuth.Used.accepted_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Used.accepted_later

/-- info: 'Lanes.OAuth.Used.accepted_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Used.accepted_once

/-- info: 'Lanes.OAuth.Identity.under_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Identity.under_cons

/-- info: 'Lanes.OAuth.Keys.lookup_fetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Keys.lookup_fetch

/-- info: 'Lanes.OAuth.Keys.no_fetch_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.Keys.no_fetch_within

/-- info: 'Lanes.OAuth.identity?_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.identity?_strip

/-- info: 'Lanes.OAuth.identity?_withIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.OAuth.identity?_withIdentity

-- Lanes.Web.Auth.Password
/-- info: 'Lanes.Auth.Phc.parse?_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Phc.parse?_encode

/-- info: 'Lanes.Auth.Stored.read?_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Stored.read?_text

/-- info: 'Lanes.Auth.Password.verify_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Password.verify_hash

/-- info: 'Lanes.Auth.Password.verify_phc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Password.verify_phc

/-- info: 'Lanes.Auth.Password.verify_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.Password.verify_raw

-- Lanes.Web.Auth.Token
/-- info: 'Lanes.Auth.verify_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_sign

/-- info: 'Lanes.Auth.checkForm_formToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.checkForm_formToken

/-- info: 'Lanes.Auth.verify_expired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_expired

/-- info: 'Lanes.Auth.verify_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_rotate

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

/-- info: 'Lanes.Http.Conn.read_streamed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.read_streamed

/-- info: 'Lanes.Http.Conn.respond_opens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.respond_opens

/-- info: 'Lanes.Http.Conn.respond_ignored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.respond_ignored

/-- info: 'Lanes.Http.Conn.pulled_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.pulled_part

/-- info: 'Lanes.Http.Conn.pulled_ignored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.pulled_ignored

/-- info: 'Lanes.Http.Conn.pulled_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.pulled_large

/-- info: 'Lanes.Http.Conn.flushStream_ended' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Http.Conn.flushStream_ended

/-- info: 'Lanes.Http.Conn.flushStream_going' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.flushStream_going

/-- info: 'Lanes.Http.Conn.pump_piece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.pump_piece

/-- info: 'Lanes.Http.Conn.gather_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Conn.gather_length

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

/-- info: 'Lanes.Http.Gate.step_arrive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Gate.step_arrive

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

/-- info: 'Lanes.Http.Ops.allows_eq_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.allows_eq_true

/-- info: 'Lanes.Http.Ops.route?_metrics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.route?_metrics

/-- info: 'Lanes.Http.Ops.route?_metrics_loopback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.route?_metrics_loopback

/-- info: 'Lanes.Http.Ops.route?_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.route?_hidden

/-- info: 'Lanes.Http.Ops.route?_peer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Ops.route?_peer

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

-- Lanes.Web.Http.SseSound
/-- info: 'Lanes.Http.Sse.parse_written' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Sse.parse_written

/-- info: 'Lanes.Http.Sse.Event.ofResponse_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Sse.Event.ofResponse_valid

-- Lanes.Web.Http.SigV4Sound
/-- info: 'Lanes.SigV4.encode_chunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.encode_chunks

/-- info: 'Lanes.SigV4.decodePath_canonicalPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.decodePath_canonicalPath

/-- info: 'Lanes.SigV4.sortQuery_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.sortQuery_perm

/-- info: 'Lanes.SigV4.sortQuery_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.sortQuery_sorted

/-- info: 'Lanes.SigV4.canonicalQuery_sortQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.canonicalQuery_sortQuery

/-- info: 'Lanes.SigV4.canonicalHeaders_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.canonicalHeaders_sorted

/-- info: 'Lanes.SigV4.mem_canonicalHeaders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.mem_canonicalHeaders

/-- info: 'Lanes.SigV4.canonicalHeaders_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.canonicalHeaders_lower

/-- info: 'Lanes.SigV4.target_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.SigV4.target_sign

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

/-- info: 'Lanes.Http.Request.headOnly_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Request.headOnly_plain

/-- info: 'Lanes.Http.Response.readHead_ended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.Response.readHead_ended

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

-- Lanes.Web.S3.Multipart
/-- info: 'Lanes.S3.Multipart.Plan.count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.count_le

/-- info: 'Lanes.S3.Multipart.Plan.range_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.range_full

/-- info: 'Lanes.S3.Multipart.Plan.range_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.range_next

/-- info: 'Lanes.S3.Multipart.Plan.range_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.range_last

-- Lanes.Web.S3.PostSound
/-- info: 'Lanes.S3.Post.form_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Post.form_policy

/-- info: 'Lanes.S3.Post.decode?_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Post.decode?_encode

/-- info: 'Lanes.S3.Post.expiration_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Post.expiration_parse

/-- info: 'Lanes.S3.Post.check_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Post.check_holds

/-- info: 'Lanes.S3.Post.admitted_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Post.admitted_bounded

-- Lanes.Web.Http.SharedCache
/-- info: 'Lanes.Http.SharedCache.serve_storable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.SharedCache.serve_storable

/-- info: 'Lanes.Http.SharedCache.serve_reuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.SharedCache.serve_reuses

/-- info: 'Lanes.Http.SharedCache.serve_of_leaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Http.SharedCache.serve_of_leaks

-- Lanes.Web.Transcode
/-- info: 'Lanes.Transcode.verify_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Transcode.verify_iff
