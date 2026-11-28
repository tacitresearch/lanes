/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Reminders.Web
import Lanes.Services.Postgres

/-!
# Serving the reminders

The front behind the gate, each of its calls run on PostgreSQL by the typed store's driver, and
the worker of the table beside it (`Postgres.Typed.Worker.start`). Each attempt is a `POST` of
the reminder's text to the notification service, with `reminder-` and the job's id in
`Idempotency-Key`, the same for every attempt (rule 3.4), cut off at the attempt's deadline.
This file only performs (rule 3.9).
-/

namespace Reminders.Serve

open Lanes Lanes.Http Lanes.Db Std.Async

structure Deployment where
  config : Config := {}
  server : ServerConfig
  runtime : Runtime.Config := {}
  /-- The database. -/
  postgres : Postgres.Client.Config
  /-- Each a file's name and its text. -/
  migrations : List (String × String)
  /-- The notification service: where a reminder is posted. -/
  notify : Client.Call
  http : Client.Config := {}
  attempt_ms : Nat := 5000
  poll_ms : Nat := 1000

abbrev Site := admittedFronted system Web.bridge

/-- The call that delivers a reminder. -/
def delivery (notify : Client.Call) (text : String) : Client.Call :=
  { notify with request := { notify.request with
    method := .post
    headers := ("content-type", "text/plain; charset=utf-8") :: notify.request.headers
    body := text.toUTF8 } }

def nowMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

/-- A running deployment: the server and the worker. -/
structure Running (d : Deployment) where
  server : Server Site
  worker : Postgres.Typed.Worker (Q := Action) (A := Answer) (W := String) (d.config.worker d.attempt_ms)

def Running.stop {d : Deployment} (r : Running d) : Async Unit := do
  r.worker.stop
  r.server.stop

/-- Run the migrations not yet run, check the table, and serve; or throw the problems that stop
it. -/
def start (d : Deployment) : Async (Running d) := do
  let problems ← Postgres.Typed.prepare d.postgres schema d.migrations
  unless problems.isEmpty do throw (IO.userError s!"reminders: not started: {problems}")
  let store : Postgres.Typed.Store (Action ⊕ Jobs.Req) (Answer ⊕ Jobs.Ans String) :=
    { pool := ← Postgres.Pool.new d.postgres, handler := Reminders.store d.config }
  let arrive (r : Http.Request) : IO (Except Http.Response Http.Request) :=
    return .ok (Web.stamp (← nowMs) r)
  let running : IO.Promise (Option (Server Site)) ← IO.Promise.new
  let onOutput : Out → Async Unit
    | .call c => background do
      let result ← try store.call c.request catch _ => pure .unknown
      if let some (some server) ← await running.result? then
        discard <| server.tryInput (.store { id := c.id, result })
    | _ => pure ()
  let server ← serveFronted system Web.bridge d.server d.runtime onOutput (arrive := some arrive)
  running.resolve (some server)
  let worker ← Postgres.Typed.Worker.start (d.config.worker d.attempt_ms) store
    (fun id deadline_ms text => do
      let r ← Jobs.http d.http "reminder-" "Idempotency-Key" id deadline_ms (delivery d.notify text)
      return r.map (·.status))
    d.poll_ms
  return { server, worker }

end Reminders.Serve
