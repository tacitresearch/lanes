/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Web

/-!
# Serving the site

The site and its scheduler behind the gate, with the sign-in and the time stamp in `arrive`, on
a journal with snapshots. Each attempt the scheduler dispatches is made through the S3 client,
cut off at the attempt's deadline, and its answer, or `unknown` when there is none, is handed
back as an input. `Main`, the end-to-end test and the live smoke start it the same way.

`S3.handler` needs the `Runtime` of the system, which `Http.serveFronted` keeps to itself, so
the call is made here with `S3.exchange` and answered with `Server.tryInput`. An answer that
finds the inbox full is dropped: the end of the attempt's wait then counts it as failed, and the
next attempt comes after the backoff. This file only performs (rule 3.9).
-/

namespace Videos.Web

open Lanes Lanes.Http Lanes.OAuth Std.Async

/-- The S3 call of what a job asks the store. -/
def storeCall (s : Settings) : StoreOp → Option S3.Op
  | .head v => (S3.Key.of? (s.objectKey v)).map .head
  | .delete v => (S3.Key.of? (s.objectKey v)).map .delete

/-- What the site makes of the S3 client's answer, or of none by the deadline. -/
def storeReply : Option S3.Answer → Rpc.Reply StoreAnswer
  | some (.found info) => .answer (.found info.size)
  | some .missing => .answer .missing
  | some .deleted => .answer .deleted
  | some _ => .answer .failed
  | none => .unknown

structure Deployment where
  config : Config := {}
  settings : Settings
  server : ServerConfig
  runtime : Runtime.Config := { snapshotEvery := 256 }
  journal : Option System.FilePath
  signIn : SignIn.Config
  http : Client.Config := {}

abbrev Site' (d : Deployment) := fronted (system d.config) (bridge d.settings) d.server.gate

def nowSeconds : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat / 1000

def openLog (d : Deployment) (path : System.FilePath) : IO (Journal.Log (Site' d)) :=
  Journal.Store.open (sys := Site' d)
    { path, system := d.server.journalName
      input := Codec.sum (Codec.pair Codec.nat Http.Request.codec) (Codec.of (SchedIn ⊕ Input))
      actors := some (frontedActors (actors d.config) (Codec.of (SchedOut ⊕ Out)) (bridge d.settings)
        d.server.gate) }

def start (d : Deployment) : Async (Server (Site' d)) := do
  let signIn ← SignIn.start d.signIn
  let arrive (r : Http.Request) : IO (Except Http.Response Http.Request) := do
    match ← signIn.arrive r with
    | .ok r => return .ok (stamp (← nowSeconds) r)
    | answer => return answer
  let running : IO.Promise (Option (Server (Site' d))) ← IO.Promise.new
  let perform (a : Schedule.Attempt Key Unit) : Async Unit := do
    let answer ← match storeCall d.settings a.key.op with
      | some op =>
        try S3.exchange d.settings.bucket d.settings.creds op { d.http with timeout_ms := a.deadline_ms }
        catch _ => pure none
      | none => pure none
    if let some (some server) ← await running.result? then
      discard <| server.tryInput (.inl (.reply a.key a.attempt (storeReply answer)))
  let onOutput : SchedOut ⊕ Out → Async Unit
    | .inl (.call a) => background (perform a)
    | .inr (.orphan v) => IO.eprintln s!"videos: gave up deleting {d.settings.objectKey v} from the store"
    | _ => pure ()
  let log ← match d.journal with
    | some path => some <$> openLog d path
    | none => pure none
  let server ← serveFronted (system d.config) (bridge d.settings) d.server d.runtime onOutput log
    (arrive := some arrive)
  running.resolve (some server)
  return server

end Videos.Web
