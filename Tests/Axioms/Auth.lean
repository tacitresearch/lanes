/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics

/-! The axiom gate (rule 5.5, see `Tests/Axioms.lean`) for the theorems of `Lanes/Auth/`. -/

-- Lanes.Auth.Login
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

-- Lanes.Auth.Token
/-- info: 'Lanes.Auth.verify_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.verify_sign

/-- info: 'Lanes.Auth.checkForm_formToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lanes.Auth.checkForm_formToken

-- Lanes.Auth.TokenSound
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
