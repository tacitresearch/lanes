/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.EndToEnd

/-!
`videosLive`: the end-to-end flow (`Videos.EndToEnd.flow`) against the bucket the environment
names, as `videos` reads it (`VIDEOS_BUCKET`, `AWS_REGION`, `VIDEOS_S3_ENDPOINT`, `AWS_*`), with
the test kit's provider still run here. Every key it writes is under `videos-live-<n>/`, and it deletes
what is left at the end. Not run by `lake test`: it needs a bucket, credentials and the network.
The bucket's CORS rules do not matter here, since no browser is involved.
-/

open Lanes Lanes.Http Std.Async Videos Videos.Web Videos.EndToEnd

def bucket : IO (Option S3.Bucket) := do
  let some name := (← IO.getEnv "VIDEOS_BUCKET").filter (!·.isEmpty) | return none
  let region := ((← IO.getEnv "AWS_REGION").filter (!·.isEmpty)).getD "us-east-1"
  match (← IO.getEnv "VIDEOS_S3_ENDPOINT").filter (!·.isEmpty) with
  | none => return some { name, region, endpoint := S3.Endpoint.aws region }
  | some url =>
    let some e := OAuth.Endpoint.parse url | return none
    let scheme : Client.Scheme := if e.https then .https else .http
    return some { name, region, endpoint := { host := e.host, port := e.port, scheme, addressing := .path } }

def main : IO UInt32 := do
  let some b ← bucket | IO.eprintln "videosLive: VIDEOS_BUCKET is not set"; return 2
  let some creds ← S3.credentialsFromEnv
    | IO.eprintln "videosLive: AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY are not set"; return 2
  let keyPrefix := s!"videos-live-{← IO.monoNanosNow}/"
  let journal ← scratch
  let results ← try
      (do
        let provider ← Testing.OAuth.Fake.start (oidc := false)
        let d := deployment b creds provider journal keyPrefix
        let held (key : String) : Async Bool := do
          let some k := S3.Key.of? key | return false
          return (← S3.exchange b creds (.head k)) matches some (.found _)
        let results ← flow d provider held
        for v in [0, 1, 2] do
          if let some k := S3.Key.of? (d.settings.objectKey v) then
            discard <| S3.exchange b creds (.delete k)
        provider.stop
        return results : Async _).block
    finally
      remove journal
  let failed := results.filter (!·.2)
  for (name, ok) in results do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  IO.println s!"{results.length - failed.length} passed, {failed.length} failed, against {b.name}"
  return if failed.isEmpty then 0 else 1
