import Rookery.Web
import Lanes.Services.Postgres

/-!
# Serving rookery

The front behind the gate, its calls run on PostgreSQL by the typed store's driver
(`Postgres.Typed.serve`), after the migrations not yet run and a check that the tables are the
declared ones (`Postgres.Typed.prepare`). `arrive` gives `Web.arrive` the time, 16 random bytes
and, for a log-in, the hash stored for its name, read in a transaction of its own; it decides
nothing (rule 3.9).
-/

namespace Rookery.Serve

open Lanes Lanes.Http Lanes.Db Std.Async

structure Deployment where
  config : Config := {}
  settings : Web.Settings
  server : ServerConfig
  runtime : Runtime.Config := {}
  postgres : Postgres.Client.Config
  /-- Each a file's name and its text. -/
  migrations : List (String × String)

/-- The hash stored for a name. -/
def hashOf : Handler String (Option String) := fun n => do
  return (← members.get [.text n]).map (·.hash)

abbrev Site (d : Deployment) := admittedFronted system (Web.bridge d.settings)

/-- What a request needs before it enters: the time, a salt, and a log-in's stored hash. A log-in
whose hash cannot be read is answered `503`. -/
def arrive (s : Web.Settings) (hashes : Postgres.Typed.Store String (Option String))
    (r : Http.Request) : IO (Except Http.Response Http.Request) := do
  let now_s := (← Log.wallMs) / 1000
  let salt ← Lanes.randomBytes 16
  let name := if (Web.Routes.logIn.match? r).isSome then r.field? "name" else none
  match name with
  | none => return .ok (Web.arrive s now_s salt none r)
  | some n =>
    match ← (hashes.call n).block with
    | .committed stored => return .ok (Web.arrive s now_s salt stored r)
    | _ => return .error (Http.Response.text "rookery is not available; try again.\n" 503)

/-- Serve, or the problems that stop it: a database that cannot be reached, a migration that
fails, or tables other than the declared ones. -/
def start (d : Deployment) : Async (Except (List String) (Server (Site d))) := do
  let problems ← Postgres.Typed.prepare d.postgres (schema d.config) d.migrations
  unless problems.isEmpty do return .error problems
  let pool ← Postgres.Pool.new d.postgres
  let store : Postgres.Typed.Store Ask Response := { pool, handler := handler d.config }
  let hashes : Postgres.Typed.Store String (Option String) := { pool, handler := hashOf }
  return .ok (← Postgres.Typed.serve system (Web.bridge d.settings) port store
    { d.server with streams := some Web.streams } d.runtime (arrive := some (arrive d.settings hashes)))

end Rookery.Serve
