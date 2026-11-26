/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Engine
import Tests.Fair
import Tests.Bank
import Tests.Json
import Tests.Runtime
import Tests.Html
import Tests.KV
import Tests.Gate
import Tests.Kernel
import Tests.Web
import Tests.Join
import Tests.Frame
import Tests.Durable
import Tests.Clock
import Tests.HttpClient

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
    ++ Tests.KV.tests ++ Tests.Gate.tests ++ Tests.Join.tests ++ Tests.Kernel.tests
    ++ Tests.Frame.tests ++ Tests.Clock.tests ++ Tests.HttpClient.tests ++ Tests.Fair.tests
  match args with
  | [] =>
    report (pure ++ (← Tests.Runtime.tests) ++ (← Tests.Web.tests) ++ (← Tests.Durable.tests)
      ++ (← Tests.Clock.live.block) ++ (← Tests.HttpClient.live.block))
  | ["fast"] => report pure
  | ["live"] =>
    report ((← Tests.Runtime.tests) ++ (← Tests.Web.tests) ++ (← Tests.Durable.tests)
      ++ (← Tests.Clock.live.block) ++ (← Tests.HttpClient.live.block))
  | ["journal-child", path] =>
    Tests.Durable.child path
    return 0
  | _ =>
    IO.eprintln "usage: lanesTest [fast|live]"
    return 2
