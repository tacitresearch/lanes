/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aws

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's three standard
axioms. If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

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

/-- info: 'Aws.Ses.json_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Ses.json_parse

/-- info: 'Aws.Ses.toAddresses_json' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.Ses.toAddresses_json

/-- info: 'Aws.CloudFront.cannedPolicy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.cannedPolicy_eq

/-- info: 'Aws.CloudFront.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.decode_encode

/-- info: 'Aws.CloudFront.cookies_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Aws.CloudFront.cookies_valid
