/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Services.Postgres.IO.Client

/-!
The client against a real PostgreSQL server, when one is there: `LANES_POSTGRES=host:port`
names it, set up as `scripts/postgres-test-server` sets one up (a database `lanes_test`, and
users `lanes_trust`, `lanes_md5` with password `md5-pw` stored as MD5, `lanes_scram` with
`scram-pw` stored as SCRAM, `lanes_clear` with `clear-pw` asked in cleartext). Without it the
tests say they are skipped and pass; CI does not run a server.

Authentication by each method, and a wrong password refused; `localhost` by name, and the
settings of libpq's variables and password file, which `psql` reads too; rows, `NULL`, UTF-8 and errors; a
failed transaction's `COMMIT` rolled back; and runs of the store (`Lanes/Outside/Store/Basic.lean`)
on a table at read committed and at serializable, with two transactions interleaved and a
`COMMIT` whose reply is lost, each recorded and checked against the model with
`Store.State.run`: that the server behaves like the model is the premise of every theorem proved
against it.
-/

namespace Tests.PostgresLive

open Lanes Lanes.Postgres Std.Async

def server : IO (Option (String × UInt16)) := do
  let some spec ← IO.getEnv "LANES_POSTGRES" | return none
  match spec.splitOn ":" with
  | [host, port] => return port.toNat?.map fun p => (host, p.toUInt16)
  | _ => return none

/-- `legacy` lets the server skip SCRAM and ask for MD5, as `lanes_md5` and `lanes_clear` need. -/
def config (host : String) (port : UInt16) (user : String) (password : Option String)
    (allowCleartext : Bool := false) (legacy : Bool := false) : Client.Config :=
  { host, port, sslmode := .disable,
    conn := { user, database := "lanes_test", password, allowCleartext,
              allowMd5 := legacy, requireScram := !legacy } }

def opens (cfg : Client.Config) : IO Bool := do
  match ← (connect cfg).block with
  | .ok s =>
    let reply ← (s.exec (.statement { sql := "SELECT current_user" })).block
    (s.close).block
    return reply == .rows { columns := ["current_user"], rows := [[some cfg.conn.user]], tag := "SELECT 1" }
  | .error _ => return false

def table : Table := { name := "lanes_live" }

abbrev Event := Store.Request Nat String ⊕ Store.Reply Nat String

/-- A run of the store, recorded: each request and its answer. -/
structure Recorder where
  cfg : Client.Config
  isolation : Store.Isolation
  sessions : Store.Sessions
  events : IO.Ref (List Event)
  next : IO.Ref Nat

def Recorder.new (cfg : Client.Config) (isolation : Store.Isolation) : IO Recorder := do
  return { cfg, isolation, sessions := ← IO.mkRef [], events := ← IO.mkRef [], next := ← IO.mkRef 0 }

def Recorder.ask (r : Recorder) (txn : Nat) (op : Store.Op Nat String) : IO (Store.Answer Nat String) := do
  let id ← r.next.modifyGet fun n => (n, n + 1)
  let request : Store.Request Nat String := { id, txn, op }
  r.events.modify (· ++ [.inl request])
  let answer ← (Store.perform r.cfg table r.isolation r.sessions request).block
  r.events.modify (· ++ [.inr { id, answer }])
  return answer

def model (isolation : Store.Isolation) : Store.Config Nat :=
  { isolation, nextKey := fun keys => keys.foldl max 0 + 1 }

/-- Whether the recorded run is one the model allows, from the rows the table had. -/
def Recorder.allowed (r : Recorder) (rows : List (Nat × String)) : IO Bool := do
  let start : Store.State Nat String := { worlds := [{ db := rows, base := rows }] }
  return (start.run (model r.isolation) (← r.events.get)).isSome

def reset (cfg : Client.Config) : IO Unit := do
  let .ok s ← (connect cfg).block | throw (IO.userError "no connection")
  discard <| (s.exec (.statement (table.create))).block
  discard <| (s.exec (.statement { sql := s!"DELETE FROM {table.name}" })).block
  (s.close).block

/-- Two transactions that each read the key the other writes: whether both committed, and the
run recorded. -/
def writeSkewRun (cfg : Client.Config) (isolation : Store.Isolation) : IO (Bool × Recorder) := do
  reset cfg
  let r ← Recorder.new cfg isolation
  discard <| r.ask 1 .begin
  discard <| r.ask 2 .begin
  discard <| r.ask 1 (.read 1)
  discard <| r.ask 2 (.read 2)
  discard <| r.ask 1 (.write 2 "one")
  discard <| r.ask 2 (.write 1 "two")
  let a ← r.ask 1 .commit
  let b ← r.ask 2 .commit
  return (a == .committed && b == .committed, r)

def writeSkew (cfg : Client.Config) (isolation : Store.Isolation) : IO (Bool × Bool) := do
  let (both, r) ← writeSkewRun cfg isolation
  return (both, ← r.allowed [])

/-- A `COMMIT` sent and its connection broken before the reply is read: the outcome is unknown
to the client, and what a later transaction reads must be one the model allows. -/
def lostCommitRun (cfg : Client.Config) (isolation : Store.Isolation) : IO (Bool × Recorder) := do
  reset cfg
  let r ← Recorder.new cfg isolation
  discard <| r.ask 1 .begin
  discard <| r.ask 1 (.insert 7 "seven")
  let some s := (← r.sessions.get).lookup 1 | return (false, r)
  r.events.modify (· ++ [.inl { id := 100, txn := 1, op := .commit }])
  discard <| (s.tell (.submit 9 .commit)).block
  let late ← (s.tell .broken).block
  let lost := late.any (· == .reply 9 .unknown)
  r.events.modify (· ++ [.inr { id := 100, answer := .unknown }])
  IO.sleep 200
  discard <| r.ask 2 .begin
  discard <| r.ask 2 (.read 7)
  discard <| r.ask 2 .commit
  return (lost, r)

def lostCommit (cfg : Client.Config) (isolation : Store.Isolation) : IO (Bool × Bool) := do
  let (lost, r) ← lostCommitRun cfg isolation
  return (lost, ← r.allowed [])

def hasPsql : IO Bool := do
  try return (← IO.Process.output { cmd := "psql", args := #["--version"] }).exitCode == 0
  catch _ => return false

/-- `localhost` by name, with the defaults for it; and the settings libpq's variables give, with
a password file, which `psql` reads too where there is one. -/
def byName (port : UInt16) : IO (List (String × Bool)) := do
  let named ← opens
    { host := "localhost", port,
      conn := { user := "lanes_scram", database := "lanes_test", password := some "scram-pw" } }
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-pgpass-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let passfile := dir / "pgpass"
  IO.FS.writeFile passfile
    s!"# the test's\nlocalhost:*:lanes_test:lanes_md5:wrong\n*:{port}:lanes\\_test:lanes_scram:scram-pw\n"
  IO.setAccessRights passfile { user := { read := true, write := true } }
  let vars := [("PGHOST", "localhost"), ("PGPORT", toString port), ("PGUSER", "lanes_scram"),
    ("PGDATABASE", "lanes_test"), ("PGPASSFILE", passfile.toString)]
  let env : Env IO := { Env.io with var := fun name => pure (vars.lookup name) }
  let settings ← (Settings.read env).run
  let fromEnv ← match settings with
    | .ok s => opens (.ofSettings s)
    | .error _ => pure false
  let libpq ← if ← hasPsql then do
      let env := (vars.map fun (n, v) => (n, some v)).toArray
        ++ #[("PGPASSWORD", none), ("PGSSLMODE", none), ("PGSERVICE", none)]
      let out ← IO.Process.output
        { cmd := "psql", args := #["-w", "-Atc", "SELECT current_user"], env }
      pure (out.exitCode == 0 && out.stdout.trimAscii.toString == "lanes_scram")
    else pure true
  IO.FS.removeDirAll dir
  return [
    ("postgres live: localhost by name, without TLS by default", named),
    ("postgres live: libpq's variables and password file, as psql reads them",
      fromEnv && libpq && settings.toOption.map (·.sslmode) == some .disable) ]

/-- One value the server gives a session opened with `cfg`. -/
def ask (cfg : Client.Config) (sql : String) : IO (Option String) := do
  match ← (connect cfg).block with
  | .ok s =>
    let reply ← (s.exec (.statement { sql })).block
    (s.close).block
    return match reply with
      | .rows { rows := [[v]], .. } => v
      | _ => none
  | .error _ => return none

/-- A service file and a connection string with libpq's options, through `Settings.read`; a host
where nothing listens tried before the server; and the kind of server asked for. -/
def options (port : UInt16) : IO (List (String × Bool)) := do
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/lanes-service-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let file := dir / "pg_service.conf"
  IO.FS.writeFile file
    s!"[lanes]\nhost=127.0.0.1\nport={port}\nuser=lanes_scram\npassword=scram-pw\ndbname=lanes_test\n"
  let vars := [("PGSERVICEFILE", file.toString), ("USER", "nobody")]
  let env : Env IO := { Env.io with var := fun name => pure (vars.lookup name) }
  let read (conninfo : String) : IO (Option Client.Config) := do
    return ((← (Settings.read env conninfo).run).toOption.map .ofSettings)
  let given ← read "service=lanes application_name=lanes-live options='-c search_path=lanes_x'"
  let appName ← match given with
    | some cfg => ask cfg "SELECT current_setting('application_name')"
    | none => pure none
  let searchPath ← match given with
    | some cfg => ask cfg "SHOW search_path"
    | none => pure none
  let closed := port + 1
  let tried ← read s!"service=lanes host=127.0.0.1,localhost port={closed},{port} connect_timeout=2"
  let second ← match tried with
    | some cfg => ask cfg "SELECT current_user"
    | none => pure none
  let kind (attrs : String) : IO (Option String) := do
    match ← read s!"service=lanes target_session_attrs={attrs}" with
    | some cfg => ask cfg "SELECT 'here'"
    | none => pure none
  let readWrite ← kind "read-write"
  let primary ← kind "primary"
  let standby ← kind "standby"
  let preferStandby ← kind "prefer-standby"
  IO.FS.removeDirAll dir
  return [
    ("postgres live: a service file and a string's application_name and options reach the session",
      appName == some "lanes-live" && searchPath == some "lanes_x"),
    ("postgres live: a host where nothing listens is passed for the next",
      second == some "lanes_scram"),
    ("postgres live: a primary is taken as read-write and primary, refused as standby, taken by prefer-standby",
      readWrite == some "here" && primary == some "here" && standby.isNone
        && preferStandby == some "here") ]

def live : IO (List (String × Bool)) := do
  let some (host, port) ← server | return [("postgres live: skipped, LANES_POSTGRES is not set", true)]
  let trust := config host port "lanes_trust" none
  let probe ← (connect trust).block
  match probe with
  | .error none => return [(s!"postgres live: skipped, no server at {host}:{port}", true)]
  | .error (some _) => return [(s!"postgres live: the server at {host}:{port} refused lanes_trust", false)]
  | .ok s => (s.close).block
  let scram ← opens (config host port "lanes_scram" (some "scram-pw"))
  let md5 ← opens (config host port "lanes_md5" (some "md5-pw") (legacy := true))
  let md5Refused ← opens (config host port "lanes_md5" (some "md5-pw"))
  let clear ← opens (config host port "lanes_clear" (some "clear-pw") (allowCleartext := true)
    (legacy := true))
  let clearRefused ← opens (config host port "lanes_clear" (some "clear-pw") (legacy := true))
  let wrong ← (connect (config host port "lanes_scram" (some "wrong"))).block
  let wrongRefused := match wrong with
    | .error (some (.server fields)) => fields.any (·.value == "28P01")
    | _ => false
  let .ok s ← (connect trust).block | return [("postgres live: connects", false)]
  let rows ← (s.exec (.statement { sql := "SELECT $1::text AS a, NULL::int AS b, 'é' AS c", params := [some "x"] })).block
  let boom ← (s.exec (.statement { sql := "SELECT 1 / 0" })).block
  discard <| (s.exec (.begin .readCommitted)).block
  discard <| (s.exec (.statement { sql := "SELECT 1 / 0" })).block
  let failedCommit ← (s.exec .commit).block
  (s.close).block
  let (skewSer, skewSerAllowed) ← writeSkew trust .serializable
  let (skewRc, skewRcAllowed) ← writeSkew trust .readCommitted
  let (lostRc, lostRcAllowed) ← lostCommit trust .readCommitted
  let (lostSer, lostSerAllowed) ← lostCommit trust .serializable
  let named ← byName port
  let withOptions ← options port
  let zero := match boom with
    | .error fields => fields.any (·.value == "22012")
    | _ => false
  return [
    ("postgres live: SCRAM-SHA-256, MD5 and an allowed cleartext password authenticate",
      scram && md5 && clear),
    ("postgres live: a cleartext password is not sent unless allowed", !clearRefused),
    ("postgres live: by default a server that asks for MD5 is refused", !md5Refused),
    ("postgres live: a wrong password is refused", wrongRefused),
    ("postgres live: rows with a parameter, NULL and UTF-8; an error with its SQLSTATE",
      rows == .rows { columns := ["a", "b", "c"], rows := [[some "x", none, some "é"]], tag := "SELECT 1" }
        && zero),
    ("postgres live: a failed transaction's COMMIT is rolled back", failedCommit == .rolledBack),
    ("postgres live: write skew: serializable commits one, read committed both", !skewSer && skewRc),
    ("postgres live: the write-skew runs are runs the store model allows at their level",
      skewSerAllowed && skewRcAllowed),
    ("postgres live: a COMMIT whose reply is lost is answered unknown", lostRc && lostSer),
    ("postgres live: what is read after a lost COMMIT is what the store model allows",
      lostRcAllowed && lostSerAllowed) ] ++ named ++ withOptions

end Tests.PostgresLive
