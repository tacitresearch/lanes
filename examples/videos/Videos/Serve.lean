/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Web

/-!
# Serving the site

The site and its scheduler behind the gate, with the sign-in and the time stamp in `arrive`, on
a journal with snapshots. The feed, the watch pages and the channel pages are reads, answered
from the site's state by `view` and never journalled. Each attempt the scheduler dispatches is
made through the S3 client, or, for a transcode, posted to the worker as its job
(`Lanes.Web.Transcode`), cut off at the attempt's deadline, and its answer, or `unknown` when
there is none, is handed back as an input. What each call is and what its answer means are the
pure functions below. `Main`, the end-to-end test and the live smoke start it the same way.

`S3.handler` needs the `Runtime` of the system, which `Http.serveFronted` keeps to itself, so
the call is made here with `S3.exchange` and answered with `Server.tryInput`. An answer that
finds the inbox full is dropped: the end of the attempt's wait then counts it as failed, and the
next attempt comes after the backoff. This file only performs (rule 3.9).
-/

namespace Videos.Web

open Lanes Lanes.Http Lanes.OAuth Std.Async

/-- What a job's attempt calls: the store, with S3 calls, or the worker, with its job. -/
inductive Exchange where
  | store (ops : List S3.Op)
  | worker (request : Http.Request)

/-- The calls of what a job asks: the head of the upload; the deletes of the upload, the
rendition and the thumbnail; the job of a round, posted to the worker. -/
def exchangeOf (s : Settings) (key : Hmac.Key) : Op → Option Exchange
  | .head v => (S3.Key.of? (s.objectKey v)).map fun k => .store [.head k]
  | .delete v =>
    ([s.objectKey v, s.renditionKey v, s.thumbnailKey v].mapM S3.Key.of?).map fun ks =>
      .store (ks.map .delete)
  | .transcode r => some (.worker (Transcode.jobRequest key s.workerPath (s.job r) s.callback))

/-- What the site makes of the S3 client's answer, or of none by the deadline. -/
def storeReply : Option S3.Answer → Rpc.Reply Answer
  | some (.found info) => .answer (.found info.size)
  | some .missing => .answer .missing
  | some .deleted => .answer .deleted
  | some _ => .answer .failed
  | none => .unknown

/-- What the site makes of the answers to the calls of one attempt: one call's, or every
delete's, which is `deleted` only if each is. -/
def storeReplies : List (Option S3.Answer) → Rpc.Reply Answer
  | [a] => storeReply a
  | as => if as.all (· matches some .deleted) then .answer .deleted
    else if as.any (·.isNone) then .unknown else .answer .failed

/-- What the site makes of the worker's answer to a job: taken with a `2xx`. -/
def workerReply : Option Http.Response → Rpc.Reply Answer
  | some r => if 200 ≤ r.status && r.status < 300 then .answer .accepted else .answer .failed
  | none => .unknown

structure Deployment where
  config : Config
  settings : Settings
  server : ServerConfig
  runtime : Runtime.Config := { snapshotEvery := 256 }
  journal : Option System.FilePath
  signIn : SignIn.Config
  http : Client.Config := {}

abbrev Site' (d : Deployment) := admittedFronted (system d.config) (bridge d.settings)

def nowSeconds : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat / 1000

/-- How the site's journal writes its inputs: the requests the gate admitted, and the scheduler's
and the site's own. -/
def logInput : Codec ((ReqId × Http.Request) ⊕ (SchedIn ⊕ Input)) :=
  Codec.sum (Codec.pair Codec.nat Http.Request.codec) (Codec.of (SchedIn ⊕ Input))

def logActors (config : Config) (settings : Settings) :
    Kernel.Image.Codecs (admittedFronted (system config) (bridge settings)) :=
  admittedFrontedActors (actors config) (bridge settings)

/-- The schemas of the site's journal and snapshot, pinned in `schemas/`: `lake exe lanes lint`
checks that the build reads what they wrote, and the corpus. -/
def journalSchema : Schema := Journal.Entry.schemaOf logInput.schema

def snapshotSchema (config : Config) (settings : Settings) : Schema :=
  (Journal.savedOf (logActors config settings)).schema

def openLog (d : Deployment) (path : System.FilePath) : IO (Journal.Log (Site' d)) :=
  Journal.Store.open (sys := Site' d)
    { path, system := d.server.journalName, input := logInput
      actors := some (logActors d.config d.settings) }

def start (d : Deployment) : Async (Server (Site' d)) := do
  let signIn ← SignIn.start d.signIn
  let arrive (r : Http.Request) : IO (Except Http.Response Http.Request) := do
    match ← signIn.arrive r with
    | .ok r => return .ok (stamp (← nowSeconds) r)
    | answer => return answer
  let running : IO.Promise (Option (Server (Site' d))) ← IO.Promise.new
  let perform (a : Schedule.Attempt Key Unit) : Async Unit := do
    let http := { d.http with timeout_ms := a.deadline_ms }
    let reply ← match exchangeOf d.settings d.config.workerKey a.key.op with
      | some (.store ops) => storeReplies <$> ops.mapM fun op => do
          try S3.exchange d.settings.bucket d.settings.creds op http catch _ => pure none
      | some (.worker request) => match Client.Call.at d.settings.worker request with
        | some call => workerReply <$> (try Client.exchange call http catch _ => pure none)
        | none => pure .unknown
      | none => pure .unknown
    if let some (some server) ← await running.result? then
      discard <| server.tryInput (.inl (.reply a.key a.attempt reply))
  let onOutput : SchedOut ⊕ Out → Async Unit
    | .inl (.call a) => background (perform a)
    | .inr (.orphan v) => IO.eprintln s!"videos: gave up deleting {d.settings.objectKey v} from the store"
    | _ => pure ()
  let log ← match d.journal with
    | some path => some <$> openLog d path
    | none => pure none
  let server ← serveFronted (system d.config) (bridge d.settings) d.server d.runtime (fun _ => onOutput) log
    (arrive := some arrive) (view := view d.config d.settings)
  running.resolve (some server)
  return server

end Videos.Web
