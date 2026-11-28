import Rookery.Serve

/-!
rookery as a web application: `rookery [port] [secrets] [memory_kib] [maxPerWindow] [lockout_s]`.

Everything it keeps is in PostgreSQL, connected as `DATABASE_URL` says (a `postgresql://` URI),
and for what it leaves out libpq's variables (`PGHOST`, `PGUSER`, `PGPASSWORD`, `PGDATABASE`,
`PGSSLMODE`, …) or a deploy's (`LANES_DB_*`, `Postgres.Client.fromEnv`). At the start it runs the migrations of `LANES_MIGRATIONS`
(`migrations` unless set) not yet run, and refuses to start when the tables differ from the
declared ones. So the process can be killed, replaced or run as several instances at any moment.

`secrets` holds the key that signs cookies, API tokens and form tokens, 32 random bytes, then 32
more that are the pepper of `Auth.Password`, made at the first start if the file is not there.
Every instance must read the same file: with another, every session and token is another. A
password's hash is Argon2id, two passes over `memory_kib` KiB (19 MiB unless given); a hash made
at another cost is made again at the next log-in. `LANES_HOST` is the address to listen on
(`127.0.0.1` unless set), and `ROOKERY_ORIGIN` the origin pages are served from
(`http://127.0.0.1:<port>` unless set).
-/

open Lanes Rookery

def loadSecrets (path : System.FilePath) : IO ByteArray := do
  if ← path.pathExists then
    let bytes ← IO.FS.readBinFile path
    if bytes.size != 64 then throw (IO.userError s!"rookery: {path} does not hold 64 bytes")
    return bytes
  let bytes ← Lanes.randomBytes 64
  IO.FS.writeBinFile path bytes
  return bytes

def main (args : List String) : IO UInt32 := do
  let port := (args[0]? >>= String.toNat?).getD 8080
  let secrets ← loadSecrets ((args[1]?.map System.FilePath.mk).getD "rookery.secrets")
  let mem_kib := ((args[2]? >>= String.toNat?).getD 19456).toUInt32
  let maxPerWindow := (args[3]? >>= String.toNat?).getD 10
  let lockout_s := (args[4]? >>= String.toNat?).getD 300
  let some cost := if h : 8 ≤ mem_kib then some ({ ops := 2, mem_kib, mem_min := h } : Argon2id)
      else none
    | IO.eprintln "rookery: Argon2id needs at least 8 KiB"; return 2
  let host := (← IO.getEnv "LANES_HOST").getD "127.0.0.1"
  let settings : Web.Settings :=
    { keys := .of (.of (secrets.extract 0 32))
      password := { cost, pepper := secrets.extract 32 64 }
      origin := (← IO.getEnv "ROOKERY_ORIGIN").getD s!"http://127.0.0.1:{port}"
      secure := false }
  let d : Serve.Deployment :=
    { config := { maxPerWindow, lockout_s }, settings
      server := { host, port := port.toUInt16, poll_ms := 500 }
      postgres := ← Postgres.Client.fromEnv ((← IO.getEnv "DATABASE_URL").getD "")
      migrations := ← Postgres.Typed.readMigrations ((← IO.getEnv "LANES_MIGRATIONS").getD "migrations") }
  match ← (Serve.start d).block with
  | .error problems =>
    IO.eprintln "rookery: not started: the database is not ready, or not as declared:"
    for p in problems do IO.eprintln s!"  {p}"
    return 1
  | .ok server =>
    IO.println s!"rookery listening on http://{host}:{server.port.getD 0}"
    (← IO.getStdout).flush
    Lanes.block (server.stopOnSignal 10000)
    return 0
