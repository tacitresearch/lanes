/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Engine
import Tests.Bank
import Tests.Runtime
import Tests.Html
import Tests.KV

/-! The regression test driver, run by `lake test`. -/

def main : IO UInt32 := do
  let results := Tests.Engine.tests ++ Tests.Bank.tests ++ Tests.Html.tests ++ Tests.KV.tests ++ (← Tests.Runtime.tests)
  let mut failed := 0
  for (name, ok) in results do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    if !ok then failed := failed + 1
  IO.println s!"{results.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
