/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Quota

/-!
The axiom gate (Lanes rule 5.5): each headline theorem depends only on Lean's standard axioms.
If a `sorry` or a new axiom reaches one, this file stops compiling.
-/

/-- info: 'Quota.V2.withinQuota' does not depend on any axioms -/
#guard_msgs in #print axioms Quota.V2.withinQuota

/-- info: 'Quota.within_quota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Quota.within_quota

/-- info: 'Quota.within_quota_at_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Quota.within_quota_at_start

/-- info: 'Quota.starts_migrated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Quota.starts_migrated
