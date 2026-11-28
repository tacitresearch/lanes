import Counter.Web

/-!
`counter [port]`. The process keeps nothing: the count is in PostgreSQL, so the process can be
stopped, replaced or run as several instances behind a load balancer at any moment.

Everything comes from the environment, so that a deployment sets it without a change here:

- the database: `DATABASE_URL`, a `postgresql://` URI or libpq's `keyword=value` pairs, and
  for what it leaves out libpq's variables (`PGHOST`, `PGUSER`, `PGPASSWORD`, `PGDATABASE`,
  `PGSSLMODE`, …) or a deploy's (`LANES_DB_HOST`, `LANES_DB_PASSWORD_FILE`, …:
  `Postgres.Client.fromEnv`);
- the migrations, the `.sql` files of `LANES_MIGRATIONS` (`migrations` unless set), each run once,
  in the order of their names, at the start;
- `LANES_HOST`, the address (`127.0.0.1` unless set; `0.0.0.0` behind a load balancer),
  `LANES_IDLE_MS`, how long an idle connection is kept, and `LANES_DRAIN_MS`, how long SIGTERM or
  SIGINT waits for the requests in flight.

It refuses to start when the database's tables differ from the ones `Counter.schema` declares.
The server answers `/readyz` and `/healthz`, which a load balancer asks, `/metrics` to this
machine only, and writes an access log to stderr (`ServerConfig.ops`).
-/

open Lanes Counter

def main (args : List String) : IO UInt32 := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let ms (name : String) (default : Nat) : IO Nat := do
    let some text ← IO.getEnv name | return default
    let some n := text.toNat? | throw (IO.userError s!"counter: {name} is not a number: {text}")
    return n
  let host := (← IO.getEnv "LANES_HOST").getD "127.0.0.1"
  let config : Http.ServerConfig :=
    { host, port := port.toUInt16
      idle_ms := ← ms "LANES_IDLE_MS" 10000
      ops := { readinessPath := some "/readyz", livenessPath := some "/healthz",
               metricsPath := some "/metrics", accessLog := .stderr, requestIds := true } }
  let drain_ms ← ms "LANES_DRAIN_MS" 10000
  let postgres ← Postgres.Client.fromEnv ((← IO.getEnv "DATABASE_URL").getD "")
  let migrations ← Postgres.Typed.readMigrations ((← IO.getEnv "LANES_MIGRATIONS").getD "migrations")
  match ← (Web.start postgres migrations config).block with
  | .error problems =>
    IO.eprintln "counter: not started: the database is not ready, or not as declared:"
    for p in problems do IO.eprintln s!"  {p}"
    return 1
  | .ok server =>
    IO.println s!"counter listening on http://{host}:{server.port.getD 0}"
    (← IO.getStdout).flush
    Lanes.block (server.stopOnSignal drain_ms)
    return 0
