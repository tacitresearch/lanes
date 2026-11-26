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
import Tests.Fronted
import Tests.Kernel
import Tests.Web
import Tests.Join
import Tests.Frame
import Tests.Durable
import Tests.Clock
import Tests.HttpClient
import Tests.Codec
import Tests.Cluster
import Tests.Peers
import Tests.Courier
import Tests.Mailbox
import Tests.Split
import Tests.Batch

/-!
The test driver behind `lake test`: the pure tests and the live runtime tests, well under a
second together. `lanesTest live` runs only the live tier, the one worth repeating. The larger
model checks are a separate binary, `lanesCheck`, because their results are computed when the
program starts.
-/

def report (results : List (String × Bool)) : IO UInt32 := do
  let results := results ++ [("no shard is left running when the tests end",
    (← Lanes.Runtime.running) == 0)]
  for (name, ok) in results do
    if !ok then IO.println s!"FAIL {name}"
  let failed := results.countP (!·.2)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  (← IO.getStdout).flush
  IO.Process.exit (if failed == 0 then 0 else 1)

def live : IO (List (String × Bool)) := do
  return (← Tests.Runtime.tests) ++ (← Tests.Web.tests) ++ (← Tests.Durable.tests)
    ++ (← Tests.Clock.live.block) ++ (← Tests.HttpClient.live.block)
    ++ (← Tests.Cluster.tests) ++ (← Tests.Peers.live.block) ++ (← Tests.Peers.durable.block)
    ++ (← Tests.Peers.transport.block) ++ (← Tests.Fronted.live.block)
    ++ (← Tests.Fronted.busyTest.block) ++ (← Tests.Fronted.nodeTest.block)
    ++ (← Tests.Fronted.nodeDurable.block) ++ (← Tests.Fronted.durable.block)

def main (args : List String) : IO UInt32 := do
  let pure := Tests.Engine.tests ++ Tests.Bank.tests ++ Tests.Json.tests ++ Tests.Html.tests
    ++ Tests.KV.tests ++ Tests.Gate.tests ++ Tests.Fronted.tests ++ Tests.Join.tests
    ++ Tests.Kernel.tests ++ Tests.Frame.tests ++ Tests.Clock.tests ++ Tests.HttpClient.tests
    ++ Tests.Fair.tests ++ Tests.Codec.tests ++ Tests.Durable.fileTests ++ Tests.Split.tests
    ++ Tests.Peers.tests ++ Tests.Courier.tests ++ Tests.Mailbox.tests ++ Tests.Batch.tests
  match args with
  | [] => report (pure ++ (← live))
  | ["fast"] => report pure
  | ["live"] => report (← live)
  | ["journal-child", path] =>
    Tests.Durable.child path
    return 0
  | ["tape-child", path, round] =>
    Tests.Durable.tapeChild path round.toNat!
    return 0
  | _ =>
    IO.eprintln "usage: lanesTest [fast|live]"
    return 2
