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
import Tests.Sign
import Tests.OAuth
import Tests.ReadRequest
import Tests.Codec
import Tests.Schema
import Tests.Body
import Tests.Match
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
import Tests.Copies
import Tests.Tutorial
import Tests.TutorialWeb
import Tests.Release
import Tests.Oracle.All
import Tests.Oracle.Service.All
import Tests.Jobs
import Tests.Schedule
import Tests.Outside
import Tests.Queue
import Tests.Reduce
import Tests.SharedCache
import Tests.Cache
import Tests.Throttle
import Tests.WallClock
import Tests.Ops
import Tests.Postgres
import Tests.PostgresConn
import Tests.PostgresPool
import Tests.PostgresSettings
import Tests.PostgresLive
import Tests.PostgresTls
import Tests.Store
import Tests.SigV4
import Tests.S3
import Tests.Multipart
import Tests.S3Upload
import Tests.Ship
import Tests.Testing

/-!
The test driver behind `lake test`: the pure tests and the live runtime tests, well under a
second together. `lanesTest live` runs only the live tier, the one worth repeating; `--json`
prints the results as JSON (`lake test -- --json`). The larger
model checks are a separate binary, `lanesCheck`, because their results are computed when the
program starts.
-/

/-- Print the failures of the pure tests before the live ones start, unless the output is JSON. -/
def failures (json : Bool) (results : List (String × Bool)) : IO Unit := do
  if json then return
  for line in (Lanes.Testing.Result.tests results).filterMap (Lanes.Testing.line ·) do
    IO.println line
  (← IO.getStdout).flush

/-- `shown` results at the start have had their failures printed already. With `--json` in
`args`, every result is printed as JSON (`Testing.report`). -/
def report (args : List String) (results : List (String × Bool)) (shown : Nat := 0) :
    IO UInt32 := do
  let results := results ++ [("no shard is left running when the tests end",
    (← Lanes.Runtime.running) == 0)]
  let code ← Lanes.Testing.report args (Lanes.Testing.Result.tests results)
    (if Lanes.Testing.wantsJson args then 0 else shown) (passes := false)
  IO.Process.exit code.toUInt8

open Tests.Durable (safely) in
def live : IO (List (String × Bool)) := do
  let group (name : String) (tests : IO (List (String × Bool))) := safely name (liftM tests)
  return (← group "runtime" Tests.Runtime.tests) ++ (← group "web" Tests.Web.tests)
    ++ (← Tests.Durable.tests) ++ (← group "ending" Tests.Ending.tests)
    ++ (← safely "clock" Tests.Clock.live)
    ++ (← safely "http client" Tests.HttpClient.live) ++ (← safely "tls" Tests.Tls.live)
    ++ (← safely "signature" (liftM Tests.Signature.live)) ++ (← safely "sign" (liftM Tests.Sign.live))
    ++ (← safely "oauth" Tests.OAuth.live)
    ++ (← safely "peers" Tests.Peers.live) ++ (← safely "peers on a journal" Tests.Peers.durable)
    ++ (← safely "transport" Tests.Peers.transport) ++ (← safely "fronted" Tests.Fronted.live)
    ++ (← safely "full inbox" Tests.Fronted.busyTest) ++ (← safely "node" Tests.Fronted.nodeTest)
    ++ (← safely "node on a journal" Tests.Fronted.nodeDurable)
    ++ (← safely "fronted on a journal" Tests.Fronted.durable)
    ++ (← safely "release" Tests.Release.liveTests) ++ (← safely "jobs" Tests.Jobs.live)
    ++ (← safely "ops" Tests.Ops.live) ++ (← Tests.Crypto.live)
    ++ (← safely "postgres" Tests.PostgresLive.live)
    ++ (← safely "postgres tls" Tests.PostgresTls.live)
    ++ (← safely "s3" Tests.S3.live) ++ (← safely "s3 uploads" Tests.S3Upload.live)
    ++ (← safely "ship" Tests.Ship.live)
    ++ (← safely "test kit" Tests.Testing.live)
    ++ (← safely "test kit worker" Tests.Testing.workerLive)
    ++ (← safely "tutorial web" Tests.TutorialWeb.live)

def main (args : List String) : IO UInt32 := do
  let pure := Tests.Engine.tests ++ Tests.Bank.tests ++ Tests.Json.tests ++ Tests.Html.tests
    ++ Tests.KV.tests ++ Tests.Gate.tests ++ Tests.Fronted.tests ++ Tests.Join.tests
    ++ Tests.Kernel.tests ++ Tests.Frame.tests ++ Tests.Clock.tests ++ Tests.HttpClient.tests ++ Tests.Tls.tests
    ++ Tests.Signature.tests ++ Tests.Sign.tests ++ Tests.OAuth.tests
    ++ Tests.Fair.tests ++ Tests.Codec.tests ++ Tests.Schema.tests ++ Tests.Body.tests ++ Tests.Match.tests ++ Tests.Durable.fileTests ++ Tests.Split.tests
    ++ Tests.Peers.tests ++ Tests.Courier.tests ++ Tests.Mailbox.tests ++ Tests.Batch.tests
    ++ Tests.Pace.tests
    ++ Tests.Crypto.tests ++ Tests.Auth.tests ++ Tests.Clients.tests ++ Tests.Lease.tests
    ++ Tests.Release.tests ++ Tests.ReadRequest.tests ++ Tests.Oracle.unitTests
    ++ Tests.HttpConn.tests ++ Tests.Loopback.tests
    ++ Tests.Jobs.tests ++ Tests.Schedule.tests ++ Tests.Outside.tests ++ Tests.Postgres.vectorTests
    ++ Tests.Postgres.downgradeTests ++ Tests.Postgres.tlsTests ++ Tests.Postgres.endPointTests
    ++ Tests.PostgresSettings.tests
    ++ Tests.Ops.tests
    ++ Tests.SigV4.tests ++ Tests.S3.tests ++ Tests.MultipartModel.tests ++ Tests.S3Upload.tests
    ++ Tests.Ship.tests
    ++ Tests.Testing.tests
    ++ Tests.Queue.tests ++ Tests.Reduce.tests ++ Tests.Cache.tests ++ Tests.WallClock.tests ++ Tests.Throttle.tests
    ++ Tests.SharedCache.tests
  let json := Lanes.Testing.wantsJson args
  match args.filter (· != "--json") with
  | [] =>
    let pure := pure ++ (← Tests.ReadRequest.corpusTests) ++ (← Tests.Lint.tests)
      ++ (← Tests.New.tests) ++ (← Tests.Copies.tests) ++ (← Tests.Tutorial.tests) ++ (← Tests.TutorialWeb.tests) ++ (← Tests.Oracle.replayAll) ++ (← Tests.Oracle.Service.replayAll)
      ++ (← Tests.Json.suite) ++ (← Tests.HttpConn.checks) ++ (← Tests.Postgres.psqlTests) ++ (← Tests.PostgresConn.checks) ++ (← Tests.PostgresPool.checks) ++ (← Tests.StoreModel.checks)
      ++ (← Tests.MultipartModel.checks) ++ (← Tests.Testing.runnerTests)
    failures json pure
    report args (pure ++ (← live)) pure.length
  | ["fast"] => report args (pure ++ (← Tests.ReadRequest.corpusTests) ++ (← Tests.Lint.tests)
      ++ (← Tests.New.tests) ++ (← Tests.Copies.tests) ++ (← Tests.Tutorial.tests) ++ (← Tests.TutorialWeb.tests) ++ (← Tests.Oracle.replayAll) ++ (← Tests.Oracle.Service.replayAll)
      ++ (← Tests.Json.suite) ++ (← Tests.HttpConn.checks) ++ (← Tests.Postgres.psqlTests) ++ (← Tests.PostgresConn.checks) ++ (← Tests.PostgresPool.checks) ++ (← Tests.StoreModel.checks)
      ++ (← Tests.MultipartModel.checks))
  | ["live"] => report args (← live)
  | ["journal-child", path] =>
    Tests.Durable.child path
    return 0
  | ["tape-child", path, round] =>
    Tests.Durable.tapeChild path round.toNat!
    return 0
  | _ =>
    IO.eprintln "usage: lanesTest [fast|live] [--json]"
    return 2
