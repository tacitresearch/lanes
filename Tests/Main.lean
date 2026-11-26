/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Engine
import Tests.Bank
import Tests.Json
import Tests.Runtime
import Tests.Html
import Tests.KV

/-!
The test driver behind `lake test`: the pure tests and the live runtime tests, well under a
second together. `lanesTest live` runs only the live tier, the one worth repeating. The larger
model checks are a separate binary, `lanesCheck`, because their results are computed when the
program starts.
-/

def report (results : List (String × Bool)) : IO UInt32 := do
  for (name, ok) in results do
    if !ok then IO.println s!"FAIL {name}"
  let failed := results.countP (!·.2)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  let pure := Tests.Engine.tests ++ Tests.Bank.tests ++ Tests.Json.tests ++ Tests.Html.tests
    ++ Tests.KV.tests
  match args with
  | [] => report (pure ++ (← Tests.Runtime.tests))
  | ["fast"] => report pure
  | ["live"] => report (← Tests.Runtime.tests)
  | _ =>
    IO.eprintln "usage: lanesTest [fast|live]"
    return 2
