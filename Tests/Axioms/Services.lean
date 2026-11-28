/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Lanes.Services

/-! Axiom gates for `Lanes/Services/` (see `Tests/Axioms.lean`). -/

-- Lanes.Services.Aws.CloudFrontSound

/-- info: 'Aws.CloudFront.cannedPolicy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.cannedPolicy_eq

/-- info: 'Aws.CloudFront.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.decode_encode

/-- info: 'Aws.CloudFront.fields_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.fields_safe

/-- info: 'Aws.CloudFront.cookies_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.cookies_valid

-- Lanes.Services.Aws.Refresh

/-- info: 'Aws.Refresh.current_fresh' depends on axioms: [propext] -/
#guard_msgs in #print axioms Aws.Refresh.current_fresh

/-- info: 'Aws.Refresh.current_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Refresh.current_answered

/-- info: 'Aws.Refresh.backoff_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms Aws.Refresh.backoff_le

/-- info: 'Aws.Refresh.retry_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Refresh.retry_within

/-- info: 'Aws.Refresh.accept_due' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Refresh.accept_due

/-- info: 'Aws.Refresh.refresh_in_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Refresh.refresh_in_time

/-- info: 'Aws.Refresh.currentHeld_creds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Aws.Refresh.currentHeld_creds

-- Lanes.Services.Aws.Imds

/-- info: 'Aws.Imds.containerSource?_container' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Imds.containerSource?_container

/-- info: 'Aws.Imds.chain_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Imds.chain_keys

/-- info: 'Aws.Imds.chain_container' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Imds.chain_container

/-- info: 'Aws.Imds.chain_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Imds.chain_instance

-- Lanes.Services.Aws.Ses

/-- info: 'Aws.Ses.Sent.admitted_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Ses.Sent.admitted_nodup

-- Lanes.Services.Aws.SesSound

/-- info: 'Aws.Ses.json_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Ses.json_parse

/-- info: 'Aws.Ses.toAddresses_json' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Ses.toAddresses_json

-- Lanes.Services.Postgres.Bytes
/-- info: 'Lanes.Postgres.inverse_byte' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Postgres.inverse_byte

/-- info: 'Lanes.Postgres.inverse_u16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.inverse_u16

/-- info: 'Lanes.Postgres.inverse_u32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.inverse_u32

/-- info: 'Lanes.Postgres.inverse_str' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.inverse_str

/-- info: 'Lanes.Postgres.inverse_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.inverse_value

/-- info: 'Lanes.Postgres.take_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Postgres.take_append

/-- info: 'Lanes.Postgres.untilNul_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Postgres.untilNul_append

/-- info: 'Lanes.Postgres.many_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Postgres.many_append

/-- info: 'Lanes.Postgres.inverse_list16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.inverse_list16

/-- info: 'Lanes.Postgres.getTerminated_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.getTerminated_append

/-- info: 'Lanes.Postgres.whole_append' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Postgres.whole_append

-- Lanes.Services.Postgres.ConnSound
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

/-- info: 'Lanes.Postgres.Conn.onMessage_requireScram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_requireScram

/-- info: 'Lanes.Postgres.Conn.onMessage_sasl_authOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_sasl_authOk

/-- info: 'Lanes.Postgres.Conn.onMessage_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_opened

/-- info: 'Lanes.Postgres.Conn.tls_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.tls_first

/-- info: 'Lanes.Postgres.Conn.run_beforeTls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.run_beforeTls

/-- info: 'Lanes.Postgres.Conn.step_beforeTls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_beforeTls

/-- info: 'Lanes.Postgres.Conn.step_refusedTls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_refusedTls

/-- info: 'Lanes.Postgres.Conn.step_startTls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_startTls

/-- info: 'Lanes.Postgres.Conn.step_secured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.step_secured

/-- info: 'Lanes.Postgres.Conn.choose_endPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.choose_endPoint

/-- info: 'Lanes.Postgres.Conn.choose_require' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.choose_require

/-- info: 'Lanes.Postgres.Conn.run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.run_bound

/-- info: 'Lanes.Postgres.Conn.onMessage_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Conn.onMessage_binds

-- Lanes.Services.Postgres.IO.Client
/-- info: 'Lanes.Postgres.Client.Config.sslmode_default' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Client.Config.sslmode_default

-- Lanes.Services.Postgres.MessageSound
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

-- Lanes.Services.Postgres.Pool
/-- info: 'Lanes.Postgres.Pool.run_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Pool.run_size

/-- info: 'Lanes.Postgres.Pool.run_waiting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Pool.run_waiting

/-- info: 'Lanes.Postgres.Pool.never_again' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Pool.never_again

-- Lanes.Services.Postgres.Scram
/-- info: 'Lanes.Postgres.Scram.respond_nonce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Scram.respond_nonce

/-- info: 'Lanes.Postgres.Scram.respond_iterations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Scram.respond_iterations

/-- info: 'Lanes.Postgres.Scram.respond_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Scram.respond_binds

/-- info: 'Lanes.Postgres.Scram.Binding.data_endPoint' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Postgres.Scram.Binding.data_endPoint

-- Lanes.Services.Postgres.Settings
/-- info: 'Lanes.Postgres.Address.preferred_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Address.preferred_spec

/-- info: 'Lanes.Postgres.Address.preferred_isSome' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Postgres.Address.preferred_isSome

/-- info: 'Lanes.Postgres.SslMode.defaultFor_loopback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.SslMode.defaultFor_loopback

/-- info: 'Lanes.Postgres.SslMode.defaultFor_remote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.SslMode.defaultFor_remote

/-- info: 'Lanes.Postgres.SslMode.defaultFor_disable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.SslMode.defaultFor_disable

/-- info: 'Lanes.Postgres.Address.name_remote' does not depend on any axioms -/
#guard_msgs in #print axioms Lanes.Postgres.Address.name_remote

/-- info: 'Lanes.Postgres.SslMode.defaultForAll_disable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.SslMode.defaultForAll_disable

/-- info: 'Lanes.Postgres.SslMode.defaultForAll_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.SslMode.defaultForAll_single

/-- info: 'Lanes.Postgres.TargetSessionAttrs.accepts_readWrite' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Postgres.TargetSessionAttrs.accepts_readWrite

/-- info: 'Lanes.Postgres.TargetSessionAttrs.accepts_primary' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.Postgres.TargetSessionAttrs.accepts_primary

/-- info: 'Lanes.Postgres.TargetSessionAttrs.passes_last' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Postgres.TargetSessionAttrs.passes_last

/-- info: 'Lanes.Postgres.PassFile.ownerOnly_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.PassFile.ownerOnly_bits

-- Lanes.Services.Postgres.Sql
/-- info: 'Lanes.Postgres.Sql.decode_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Sql.decode_param

/-- info: 'Lanes.Postgres.Sql.decodeRow_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Postgres.Sql.decodeRow_param

-- Lanes.Services.S3.Basic
/-- info: 'Lanes.S3.expiryWithin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.expiryWithin_le

/-- info: 'Lanes.S3.expiryWithin_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lanes.S3.expiryWithin_none

-- Lanes.Services.S3.Multipart
/-- info: 'Lanes.S3.Multipart.Plan.count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.count_le

/-- info: 'Lanes.S3.Multipart.Plan.range_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.range_full

/-- info: 'Lanes.S3.Multipart.Plan.range_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.range_next

/-- info: 'Lanes.S3.Multipart.Plan.range_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.S3.Multipart.Plan.range_last

-- Lanes.Services.S3.MultipartModel
/-- info: 'Lanes.Multipart.read_listed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Multipart.read_listed

/-- info: 'Lanes.Multipart.completed_sent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Multipart.completed_sent

-- Lanes.Services.S3.PostSound
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

-- Lanes.Services.Stripe.Payments
/-- info: 'Lanes.Payments.final' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Payments.final

/-- info: 'Lanes.Payments.succeeded_terminal' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in #print axioms Lanes.Payments.succeeded_terminal
