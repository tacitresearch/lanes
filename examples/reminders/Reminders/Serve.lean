/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Reminders.Web

/-!
# Serving the reminders

The reminders and the scheduler behind the gate, on a journal with snapshots. Each attempt the
scheduler dispatches is a `POST` of the reminder's text to the notification service, with the
reminder's id in `Idempotency-Key`, the same for every attempt (rule 3.4), cut off at the
attempt's deadline; its answer, or `unknown` when there is none, is handed back as an input. An
answer that finds the inbox full is dropped: the end of the attempt's wait then counts it as
failed, and the next attempt comes after the backoff. This file only performs (rule 3.9).
-/

namespace Reminders.Serve

open Lanes Lanes.Http Std.Async

structure Deployment where
  config : Config := {}
  server : ServerConfig
  runtime : Runtime.Config := { snapshotEvery := 256 }
  journal : Option System.FilePath
  /-- The notification service: where a reminder is posted. -/
  notify : Client.Call
  http : Client.Config := {}

abbrev Site (d : Deployment) := fronted (system d.config) Web.bridge d.server.gate

def openLog (d : Deployment) (path : System.FilePath) : IO (Journal.Log (Site d)) :=
  Journal.Store.open (sys := Site d)
    { path, system := d.server.journalName
      input := Codec.sum (Codec.pair Codec.nat Http.Request.codec) (Codec.of (SchedIn ⊕ In))
      actors := some (frontedActors (Web.actors d.config) (Codec.of (SchedOut ⊕ Out)) Web.bridge
        d.server.gate) }

/-- The call that delivers a reminder, keyed by the reminder. -/
def delivery (notify : Client.Call) (a : Schedule.Attempt Key Task) : Option Client.Call :=
  match a.payload with
  | .deliver id text =>
    some { notify with request := { notify.request with
      method := .post
      headers := ("idempotency-key", s!"reminder-{id}") ::
        ("content-type", "text/plain; charset=utf-8") :: notify.request.headers
      body := text.toUTF8 } }
  | .sweep => none

def replyOf : Option Response → Rpc.Reply Answer
  | some r => .answer r.status
  | none => .unknown

def nowMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

def start (d : Deployment) : Async (Server (Site d)) := do
  let arrive (r : Http.Request) : IO (Except Http.Response Http.Request) :=
    return .ok (Web.stamp (← nowMs) r)
  let running : IO.Promise (Option (Server (Site d))) ← IO.Promise.new
  let perform (a : Schedule.Attempt Key Task) : Async Unit := do
    let some call := delivery d.notify a | return
    let answer ← try Client.exchange call { d.http with timeout_ms := a.deadline_ms }
      catch _ => pure none
    if let some (some server) ← await running.result? then
      discard <| server.tryInput (.inl (.reply a.key a.attempt (replyOf answer)))
  let onOutput : SchedOut ⊕ Out → Async Unit
    | .inl (.call a) => background (perform a)
    | .inr (.deadLetter id text attempts) =>
      IO.eprintln s!"reminders: gave up on reminder {id} ({text}) after {attempts} attempts"
    | _ => pure ()
  let log ← match d.journal with
    | some path => some <$> openLog d path
    | none => pure none
  let server ← serveFronted (system d.config) Web.bridge d.server d.runtime onOutput log
    (arrive := some arrive)
  running.resolve (some server)
  return server

end Reminders.Serve
