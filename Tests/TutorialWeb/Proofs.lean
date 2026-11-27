/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Semantics
import Tests.TutorialWeb.Files

/-!
Proofs that need the proof layer (CSLib, Mathlib), and the axiom gates. Nothing executable
imports this file.
-/

namespace Shelf

open Lanes

/-- Whatever concurrent clients observe is a behaviour of `service`, each request taking effect
at one instant, in any environment that loses, duplicates and crashes nothing. -/
theorem implements (config : Config) (env : EnvModel sig) (henv : env.Faultless) :
    (system config).Implements env (service config) :=
  Server.implements (service config) env henv

end Shelf

/-- info: 'Shelf.only_uploader_deletes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shelf.only_uploader_deletes

/-- info: 'Shelf.system_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shelf.system_bounded

/-- info: 'Shelf.implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Shelf.implements
