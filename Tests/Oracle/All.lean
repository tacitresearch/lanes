/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Base64

/-! The packages compared with Go, and the replay of their recorded answers for `lake test`. -/

namespace Tests.Oracle

def packages : List Package := [Base64.package]

def unitTests : List (String × Bool) := Base64.tests

def replayAll : IO (List (String × Bool)) :=
  return (← packages.mapM Package.replay).flatten

end Tests.Oracle
