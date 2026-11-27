/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Checks.Refresh
import Checks.Imds
import Checks.Ses
import Tests.Durable

/-!
The AWS integration's checks, run by `lake test`: the refresh policy model-checked, and the
credentials, S3 and SES against fakes run here. Nothing calls AWS.
-/

open Tests.Durable (safely)

def main : IO UInt32 := do
  IO.println Checks.Refresh.report
  let live := (← safely "credentials" Checks.Imds.live) ++ (← safely "ses" Checks.Ses.live)
  let tests := Checks.Refresh.tests ++ Checks.Imds.unitTests ++ Checks.Ses.tests ++ live
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  IO.println s!"{tests.length - failed.length} passed, {failed.length} failed"
  return if failed.isEmpty then 0 else 1
