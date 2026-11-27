/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Lib.Postgres.IO.Client

/-!
The client against a real PostgreSQL server, when one is there: `LANES_POSTGRES=host:port`
names it, set up as `scripts/postgres-test-server` sets one up (a database `lanes_test`, and
users `lanes_trust`, `lanes_md5` with password `md5-pw` stored as MD5, `lanes_scram` with
`scram-pw` stored as SCRAM, `lanes_clear` with `clear-pw` asked in cleartext). Without it the
tests say they are skipped and pass; CI does not run a server.

Authentication by each method, and a wrong password refused; rows, `NULL`, UTF-8 and errors; a
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
  { host, port, conn := { user, database := "lanes_test", password, allowCleartext,
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

def writeSkew (cfg : Client.Config) (isolation : Store.Isolation) : IO (Bool × Bool) := do
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
  return (a == .committed && b == .committed, ← r.allowed [])

/-- A `COMMIT` sent and its connection broken before the reply is read: the outcome is unknown
to the client, and what a later transaction reads must be one the model allows. -/
def lostCommit (cfg : Client.Config) (isolation : Store.Isolation) : IO (Bool × Bool) := do
  reset cfg
  let r ← Recorder.new cfg isolation
  discard <| r.ask 1 .begin
  discard <| r.ask 1 (.insert 7 "seven")
  let some s := (← r.sessions.get).lookup 1 | return (false, false)
  r.events.modify (· ++ [.inl { id := 100, txn := 1, op := .commit }])
  discard <| (s.tell (.submit 9 .commit)).block
  let late ← (s.tell .broken).block
  let lost := late.any (· == .reply 9 .unknown)
  r.events.modify (· ++ [.inr { id := 100, answer := .unknown }])
  IO.sleep 200
  discard <| r.ask 2 .begin
  discard <| r.ask 2 (.read 7)
  discard <| r.ask 2 .commit
  return (lost, ← r.allowed [])

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
      lostRcAllowed && lostSerAllowed) ]

end Tests.PostgresLive
