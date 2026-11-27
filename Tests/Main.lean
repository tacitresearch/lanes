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
import Tests.Ending
import Tests.Clock
import Tests.HttpClient
import Tests.Tls
import Tests.Signature
import Tests.OAuth
import Tests.ReadRequest
import Tests.Codec
import Tests.Peers
import Tests.Courier
import Tests.HttpConn
import Tests.Loopback
import Tests.Mailbox
import Tests.Split
import Tests.Batch
import Tests.Pace
import Tests.Crypto
import Tests.Auth
import Tests.Clients
import Tests.Lease
import Tests.Lint
import Tests.New
import Tests.Tutorial
import Tests.Release
import Tests.Oracle.All
import Tests.Jobs
import Tests.Schedule
import Tests.Outside
import Tests.Ops
import Tests.Postgres
import Tests.PostgresConn
import Tests.PostgresLive
import Tests.Store
import Tests.SigV4
import Tests.S3

/-!
The test driver behind `lake test`: the pure tests and the live runtime tests, well under a
second together. `lanesTest live` runs only the live tier, the one worth repeating. The larger
model checks are a separate binary, `lanesCheck`, because their results are computed when the
program starts.
-/

def failures (results : List (String × Bool)) : IO Unit := do
  for (name, ok) in results do
    if !ok then IO.println s!"FAIL {name}"
  (← IO.getStdout).flush

/-- `shown` results at the start have had their failures printed already. -/
def report (results : List (String × Bool)) (shown : Nat := 0) : IO UInt32 := do
  let results := results ++ [("no shard is left running when the tests end",
    (← Lanes.Runtime.running) == 0)]
  failures (results.drop shown)
  let failed := results.countP (!·.2)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  (← IO.getStdout).flush
  IO.Process.exit (if failed == 0 then 0 else 1)

open Tests.Durable (safely) in
def live : IO (List (String × Bool)) := do
  let group (name : String) (tests : IO (List (String × Bool))) := safely name (liftM tests)
  return (← group "runtime" Tests.Runtime.tests) ++ (← group "web" Tests.Web.tests)
    ++ (← Tests.Durable.tests) ++ (← group "ending" Tests.Ending.tests)
    ++ (← safely "clock" Tests.Clock.live)
    ++ (← safely "http client" Tests.HttpClient.live) ++ (← safely "tls" Tests.Tls.live)
    ++ (← safely "signature" (liftM Tests.Signature.live)) ++ (← safely "oauth" Tests.OAuth.live)
    ++ (← safely "peers" Tests.Peers.live) ++ (← safely "peers on a journal" Tests.Peers.durable)
    ++ (← safely "transport" Tests.Peers.transport) ++ (← safely "fronted" Tests.Fronted.live)
    ++ (← safely "full inbox" Tests.Fronted.busyTest) ++ (← safely "node" Tests.Fronted.nodeTest)
    ++ (← safely "node on a journal" Tests.Fronted.nodeDurable)
    ++ (← safely "fronted on a journal" Tests.Fronted.durable)
    ++ (← safely "release" Tests.Release.liveTests) ++ (← safely "jobs" Tests.Jobs.live)
    ++ (← safely "ops" Tests.Ops.live) ++ (← Tests.Crypto.live)
    ++ (← safely "postgres" Tests.PostgresLive.live)
    ++ (← safely "s3" Tests.S3.live)

def main (args : List String) : IO UInt32 := do
  let pure := Tests.Engine.tests ++ Tests.Bank.tests ++ Tests.Json.tests ++ Tests.Html.tests
    ++ Tests.KV.tests ++ Tests.Gate.tests ++ Tests.Fronted.tests ++ Tests.Join.tests
    ++ Tests.Kernel.tests ++ Tests.Frame.tests ++ Tests.Clock.tests ++ Tests.HttpClient.tests ++ Tests.Tls.tests
    ++ Tests.Signature.tests ++ Tests.OAuth.tests
    ++ Tests.Fair.tests ++ Tests.Codec.tests ++ Tests.Durable.fileTests ++ Tests.Split.tests
    ++ Tests.Peers.tests ++ Tests.Courier.tests ++ Tests.Mailbox.tests ++ Tests.Batch.tests
    ++ Tests.Pace.tests
    ++ Tests.Crypto.tests ++ Tests.Auth.tests ++ Tests.Clients.tests ++ Tests.Lease.tests
    ++ Tests.Release.tests ++ Tests.ReadRequest.tests ++ Tests.Oracle.unitTests
    ++ Tests.HttpConn.tests ++ Tests.Loopback.tests
    ++ Tests.Jobs.tests ++ Tests.Schedule.tests ++ Tests.Outside.tests ++ Tests.Postgres.vectorTests ++ Tests.Ops.tests
    ++ Tests.SigV4.tests ++ Tests.S3.tests
  match args with
  | [] =>
    let pure := pure ++ (← Tests.ReadRequest.corpusTests) ++ (← Tests.Lint.tests)
      ++ (← Tests.New.tests) ++ (← Tests.Tutorial.tests) ++ (← Tests.Oracle.replayAll)
      ++ (← Tests.Json.suite) ++ (← Tests.HttpConn.checks) ++ (← Tests.Postgres.psqlTests) ++ (← Tests.PostgresConn.checks) ++ (← Tests.StoreModel.checks)
    failures pure
    report (pure ++ (← live)) pure.length
  | ["fast"] => report (pure ++ (← Tests.ReadRequest.corpusTests) ++ (← Tests.Lint.tests)
      ++ (← Tests.New.tests) ++ (← Tests.Tutorial.tests) ++ (← Tests.Oracle.replayAll)
      ++ (← Tests.Json.suite) ++ (← Tests.HttpConn.checks) ++ (← Tests.Postgres.psqlTests) ++ (← Tests.PostgresConn.checks) ++ (← Tests.StoreModel.checks))
  | ["live"] => report (← live)
  | ["journal-child", path] =>
    Tests.Durable.child path
    return 0
  | ["stop-child", drain_ms] =>
    Tests.Ops.stopChild drain_ms.toNat!
    return 0
  | ["tape-child", path, round] =>
    Tests.Durable.tapeChild path round.toNat!
    return 0
  | _ =>
    IO.eprintln "usage: lanesTest [fast|live]"
    return 2
