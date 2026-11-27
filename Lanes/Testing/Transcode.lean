/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Testing.S3
public import Lanes.Web.Transcode

/-!
A fake transcode worker for tests, on a local port, that speaks the wire format of
`Lanes.Web.Transcode`. It takes a job posted to `/jobs` only with its signature, answers `202`,
and takes a repeat of a job's id as the same job. It does nothing more until the test says so:
`Fake.work` reads each job's source from the store through the S3 client, writes small objects
at its targets (a rendition, `video/mp4`, and a thumbnail, `image/jpeg`), and posts the signed
report to the job's callback. A job whose source the store does not hold, or one the test asked
to fail (`Fake.fail`), is reported failed. `Fake.forge` posts a report signed with another key,
which a caller must refuse. Reports go to the callback's host, or to a site on this machine
(`Fake.reportTo`), which a test's site is, whatever origin it names.
-/

@[expose] public section

namespace Lanes.Testing.Transcode

open Lanes Lanes.Http Std Std.Async

/-- A job the fake took, and where its report goes. -/
structure Taken where
  job : Transcode.Job String String
  callback : String
  deriving DecidableEq, Repr

structure State where
  /-- Jobs taken and not yet worked on, oldest first. -/
  queue : List Taken := []
  /-- Every job taken, once each. -/
  taken : List Taken := []
  /-- How many of the next jobs worked on to report failed. -/
  failing : Nat := 0
  /-- The port of a site on this machine that reports go to. -/
  site : Option UInt16 := none

/-- The fake's answer to a request, and its state after: a job posted to `/jobs` with its
signature is taken, once by its id. -/
def take (key : Hmac.Key) (st : State) (r : Request) : Response × State :=
  let body := (String.fromUTF8? r.body).getD ""
  let signed := (r.header? Transcode.signatureHeader).any fun sig =>
    Bytes.same (Transcode.jobSignature key body).toUTF8 sig.toUTF8
  match r.method, r.path, Transcode.readJob? body with
  | .post, ["jobs"], some (job, callback) =>
    if !signed then (Response.text "forbidden\n" 403, st)
    else if st.taken.any (·.job.id == job.id) then (Response.text "taken\n" 202, st)
    else
      let t : Taken := { job, callback }
      (Response.text "taken\n" 202, { st with queue := st.queue ++ [t], taken := st.taken ++ [t] })
  | .post, ["jobs"], none => (Response.text "bad job\n" 400, st)
  | _, _, _ => (Response.text "not found\n" 404, st)

/-- What the fake writes at a rendition's key, from a source of `size` bytes. -/
def rendition (size : Nat) : ByteArray := s!"rendition of {size} bytes".toUTF8

def thumbnail : ByteArray := "a thumbnail".toUTF8

structure Fake where
  server : TCP.Socket.Server
  /-- Where jobs are posted: `http://127.0.0.1:<port>`. -/
  origin : String
  key : Hmac.Key
  bucket : S3.Bucket
  creds : SigV4.Credentials
  state : IO.Ref State

/-- A fake worker on a local port that takes jobs signed with `key` and works on them in
`bucket`, with `creds`. -/
def Fake.start (key : Hmac.Key) (bucket : S3.Bucket) (creds : SigV4.Credentials) : Async Fake := do
  let state ← IO.mkRef ({} : State)
  let (server, port) ← listen fun r => state.modifyGet fun st => take key st r
  return { server, origin := s!"http://127.0.0.1:{port}", key, bucket, creds, state }

/-- Reports go to the site listening on `port` of this machine. -/
def Fake.reportTo (f : Fake) (port : UInt16) : IO Unit := f.state.modify ({ · with site := some port })

/-- The next `n` jobs worked on are reported failed. -/
def Fake.fail (f : Fake) (n : Nat) : IO Unit := f.state.modify ({ · with failing := n })

/-- Every job taken, once each. -/
def Fake.taken (f : Fake) : IO (List Taken) := return (← f.state.get).taken

/-- Posts `r`, signed with `key`, to `callback`: the status the site answered, `0` for none. -/
def Fake.post (f : Fake) (key : Hmac.Key) (callback : String) (r : Transcode.Report String String) :
    Async Nat := do
  let parts := callback.splitOn "/"
  let origin := "/".intercalate (parts.take 3)
  let host := ((parts.drop 2).headD "")
  let request := Transcode.reportRequest key ((parts.drop 3).filter (!·.isEmpty)) r
  let call? : Option Client.Call := match (← f.state.get).site with
    | some port =>
      some { host := "127.0.0.1", port, request := { request with headers := request.headers ++ [("host", host)] } }
    | none => Client.Call.at origin request
  let some call := call? | return 0
  let answer ← try Client.exchange call { timeout_ms := 5000 } catch _ => pure none
  return (answer.map Response.status).getD 0

/-- What working on `t` comes to: its targets written from its source, or a failure. -/
def Fake.render (f : Fake) (t : Taken) (failing : Bool) : Async (Transcode.Report String String) := do
  let failed := Transcode.Report.failed t.job.id
  let (some source, [r, th]) := (S3.Key.of? t.job.source, t.job.targets) | return failed
  let (some rKey, some thKey) := (S3.Key.of? r, S3.Key.of? th) | return failed
  if failing then return failed
  let some (.object _ body) ← S3.exchange f.bucket f.creds (.get source) | return failed
  let wrote ← S3.exchange f.bucket f.creds (.put rKey (rendition body.size) (some "video/mp4"))
  let shot ← S3.exchange f.bucket f.creds (.put thKey thumbnail (some "image/jpeg"))
  match wrote, shot with
  | some (.stored _), some (.stored _) => return .done t.job.id [r, th]
  | _, _ => return failed

/-- Works on every job taken and not yet worked on, and posts each report: the reports, with the
status the site answered each. -/
def Fake.work (f : Fake) : Async (List (Transcode.Report String String × Nat)) := do
  let queue ← f.state.modifyGet fun st => (st.queue, { st with queue := [] })
  let mut sent := []
  for t in queue do
    let failing ← f.state.modifyGet fun st =>
      (decide (0 < st.failing), { st with failing := st.failing - 1 })
    let r ← f.render t failing
    sent := sent ++ [(r, ← f.post f.key t.callback r)]
  return sent

/-- Posts `r` to `callback` signed with a key that is not the worker's: the status the site
answered. -/
def Fake.forge (f : Fake) (callback : String) (r : Transcode.Report String String) : Async Nat :=
  f.post (.of "not the worker's key".toUTF8) callback r

def Fake.stop (f : Fake) : Async Unit := f.server.close

end Lanes.Testing.Transcode
