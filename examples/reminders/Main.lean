import Reminders.Serve

/-!
`reminders [port]`. The reminders are kept in PostgreSQL, connected as libpq's variables say
(`PGHOST`, `PGPORT`, `PGUSER`, `PGPASSWORD`, `PGDATABASE`), in the table `migrations/` makes:
at the start the migrations not yet run are run, and it refuses to start on another table.
Each reminder is posted, at its time, to the notification service `NOTIFY_URL` names, and
retried until it answers `2xx`. `setup` reads the rest of the environment once, at the
start, and the process refuses to start with a list of every variable that is not valid.
-/

open Lanes Reminders

structure Setup where
  host : String
  notify : Http.Client.Call
  migrations : String

open Environment in
def setup : Environment.Reader Setup := do
  let host ← get "LANES_HOST" "127.0.0.1" (doc := "The address to listen on.")
  let path ← get "NOTIFY_PATH" "/" (doc := "The path reminders are posted to.")
  let request : Http.Request := { method := .post, path := (path.splitOn "/").filter (· != "") }
  let url : Environment.Var :=
    { name := "NOTIFY_URL", doc := "The notification service: http://host:port."
      default := some "http://127.0.0.1:9090" }
  let notify ← field url fun url => (Http.Client.Call.at url request).elim (.error "not an origin, http://host:port") .ok
  let migrations ← get "LANES_MIGRATIONS" "migrations"
    (doc := "The directory of the .sql files each run once, in the order of their names, at the start.")
  return { host, migrations, notify := notify.getD { host := "127.0.0.1", port := 9090, request } }

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let d ← Environment.load setup "reminders"
  let running ← (Serve.start
    { server := { host := d.host, port := port.toUInt16 }
      postgres := ← Postgres.Client.fromEnv, notify := d.notify
      migrations := ← Postgres.Typed.readMigrations d.migrations }).block
  IO.println s!"reminders listening on http://{d.host}:{running.server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block (running.server.stopOnSignal 10000)
