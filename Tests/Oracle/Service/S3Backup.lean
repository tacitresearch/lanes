/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.S3
import Tests.Ship

/-!
A journal shipped to moto's S3 and restored from it (`oracles/moto`): a conditional put made
twice, whose answers `S3.shipped` must read as stored and then as there already; and a bank
that saves, ships its journal through `S3.backup`, starts again, and is restored, at its end and
at a point in time, in a bucket of us-east-2 made for the run. The record, in
`oracles/moto/s3-backup.jsonl`, holds the two answers and what the restores gave; `lake test`
reads the answers through `S3.shipped` again.
-/

namespace Tests.Oracle.Service.S3Backup

open Lanes Lanes.S3 Lanes.Http Std Std.Async Tests.Durable
open Tests.Oracle.Service.S3 (creds answerJson readAnswer k)

def bucket (host : String) (port : UInt16) (run : Nat) : Bucket :=
  { name := s!"lanes-backup-{run}", region := "us-east-2",
    endpoint := { host, port, scheme := .http, addressing := .path } }

/-- CreateBucket in us-east-2, which names its region in the body. -/
def createBucket (b : Bucket) : Async (Option Lanes.Http.Response) := do
  let body := s!"<CreateBucketConfiguration xmlns=\"http://s3.amazonaws.com/doc/2006-03-01/\">\
    <LocationConstraint>{b.region}</LocationConstraint></CreateBucketConfiguration>".toUTF8
  let hash := SigV4.payloadHash body
  let request : Request :=
    { method := .put, path := [b.name], headers := [("x-amz-content-sha256", hash)], body }
  let call : Client.Call := { host := b.endpoint.host, port := b.endpoint.port, request }
  let signed := SigV4.sign creds (← now) b.scope call.authority "PUT" hash request
  Client.exchange { call with request := signed } { timeout_ms := 5000 }

def target (b : Bucket) : Journal.Ship.Target :=
  S3.backup b creds "backups/" Tests.Ship.shipping { timeout_ms := 5000 }

def shipped (path : System.FilePath) (b : Bucket) : Journal.Store Bank3 :=
  { saving path with ship := some (target b) }

def checks (first second : Option (Rpc.Reply Answer)) : List (String × Bool) :=
  let reading := fun (r : Option (Rpc.Reply Answer)) => S3.shipped (match r with
    | some (.answer a) => some a
    | _ => none)
  [ ("s3-backup on moto: a conditional put where nothing is, is stored",
      reading first == .stored),
    ("s3-backup on moto: and made again, is refused as there already, and writes nothing",
      reading second == .present) ]

def exercise (b : Bucket) : Async (List (String × Bool) × List Json) := do
  let made ← createBucket b
  let status := made.map fun (r : Lanes.Http.Response) => r.status
  unless status == some 200 do
    return ([(s!"s3-backup on moto: the bucket is made, {status}", false)], [])
  let put := fun () => exchange b creds (backupPut (k "once/segment") "one".toUTF8) {}
  let first := (← put ()).map Rpc.Reply.answer
  let second := (← put ()).map Rpc.Reply.answer
  let kept ← exchange b creds (.get (k "once/segment")) {}
  let path ← scratch "moto-ship"
  let seen ← IO.mkRef #[]
  let before ← Tests.Ship.run (shipped path b) 8 0 30 seen
  let wall := (← S3.now).toUnix
  Async.sleep 2100
  let after ← Tests.Ship.run (shipped path b) 8 30 40 seen
  let copy ← scratch "moto-ship-copy"
  let latest ← (saving copy).restore (target b)
  let restored ← Tests.Ship.run (saving copy) 8 0 0 (← IO.mkRef #[])
  let earlier ← scratch "moto-ship-earlier"
  let atTime ← (saving earlier).restore (target b) (.time ((wall + 1) * 1000000000))
  let restoredEarlier ← Tests.Ship.run (saving earlier) 8 0 0 (← IO.mkRef #[])
  for p in [path, copy, earlier] do
    remove p
    if ← (p.addExtension "shipped").pathExists then IO.FS.removeFile (p.addExtension "shipped")
  let record := [
    Json.mkObj [("put", "once/segment"), ("first", (first.map answerJson).getD .null),
      ("second", (second.map answerJson).getD .null)],
    Json.mkObj [("restored", latest.point), ("balances", Json.arr (after.map (Json.str ∘ toString)).toArray)],
    Json.mkObj [("restored", atTime.point),
      ("balances", Json.arr (before.map (Json.str ∘ toString)).toArray)] ]
  return (checks first second ++ [
    ("s3-backup on moto: the first object is kept",
      match kept with | some (.object _ body) => body == "one".toUTF8 | _ => false),
    ("s3-backup on moto: a restore of the latest is the bank as it was",
      restored == after && latest.snapshot.isSome),
    ("s3-backup on moto: a restore to a time between the runs is the bank as the first left it",
      restoredEarlier == before && atTime.point < latest.point) ], record)

def run (host : String) (tcpPort : UInt16) : IO (List (String × Bool) × List Json) := do
  (exercise (bucket host tcpPort ((← IO.monoNanosNow) % 1000000000))).block

def replay (lines : List Json) : List (String × Bool) :=
  match lines with
  | put :: _ =>
    let read := fun (name : String) => (put.getObjVal? name).toOption.bind readAnswer
    checks (read "first") (read "second")
  | [] => [("s3-backup: the record has its puts", false)]

def oracle : Oracle where
  name := "s3-backup"
  reference := "moto"
  envVar := "LANES_MOTO"
  live host port := run host port
  replay

end Tests.Oracle.Service.S3Backup
