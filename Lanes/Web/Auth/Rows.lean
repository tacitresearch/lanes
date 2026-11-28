/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Txn
public import Lanes.Web.Auth.Login

/-!
# Failed log-ins and sessions, as rows

An actor's state is lost at a restart (`docs/decisions/D110-volatile-actors.md`), and two things
an application that lets users log in keeps must not be:

- **Failed log-ins.** A count kept in memory starts again from zero at each restart, so an
  attacker who can make the process restart guesses without a lock. `Failures` keeps them in a
  row per user, each transaction applying the pure `Auth.Attempts.fail` and `succeed`;
  `Lanes/Web/Auth/RowsSound.lean` proves every row within its limit (`Failures.bounded`).
- **Sessions.** A signed token (`Lanes/Web/Auth/Token.lean`) needs no state to be checked. What
  the server must remember of a session is whether it was closed before its token expired:
  `Sessions` keeps a row per open session, which a log-out deletes, so that a closed session
  stays closed across a restart (`Sessions.closed_refused`).
-/

@[expose] public section

namespace Lanes.Auth.Rows

open Lanes.Db

/-- A user's failed log-ins, as a row. The count fits a 64-bit integer because it never passes
the limit (`Failures.Config.limit`). -/
structure AttemptsRow where
  user : String
  failures : Int64
  locked : Bool
  deriving DecidableEq, Repr, Hashable

def AttemptsRow.attempts (r : AttemptsRow) : Attempts := { failures := r.failures.toInt.toNat, locked := r.locked }

def AttemptsRow.of (user : String) (a : Attempts) : AttemptsRow :=
  { user, failures := Int64.ofNat a.failures, locked := a.locked }

namespace Failures

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  /-- Failures that lock an account; below `2 ^ 63`. -/
  limit : Nat := 5
  name : String := "login_attempts"

variable (cfg : Config)

def table : TableOf AttemptsRow where
  table := { name := cfg.name, key := 1,
             columns := [{ name := "user", ty := .text }, { name := "failures", ty := .int }, { name := "locked", ty := .bool }] }
  toRow r := [.text r.user, .int r.failures, .bool r.locked]
  ofRow
    | [.text user, .int failures, .bool locked] => some { user, failures, locked }
    | _ => none
  ofRow_toRow _ := rfl

/-- A user's failed log-ins: none if there is no row. -/
def read (user : String) : Txn Attempts := do
  return ((← (table cfg).get [.text user]).map (·.attempts)).getD {}

def write (user : String) (a : Attempts) : Txn Unit := discard <| (table cfg).upsert (AttemptsRow.of user a)

/-- A failed log-in: the count after it. -/
def failed (user : String) : Txn Attempts := do
  let a := (← read cfg user).fail cfg.limit
  write cfg user a
  return a

def succeeded (user : String) : Txn Unit := do write cfg user (← read cfg user).succeed

def unlock (user : String) : Txn Unit := write cfg user Auth.Attempts.unlock

def locked (user : String) : Txn Bool := do return (← read cfg user).locked

end Failures

/-! ## Sessions -/

/-- An open session: its id (the one its signed token carries), its user, and when it began and
was last used, in seconds. -/
structure SessionRow where
  id : Int64
  user : String
  started_s : Int64
  used_s : Int64
  deriving DecidableEq, Repr, Hashable

namespace Sessions

structure Config where
  name : String := "sessions"
  /-- How long a session lasts after it was last used, and after it began. -/
  idle_s : Int64 := 86400
  absolute_s : Int64 := 2592000

variable (cfg : Config)

/-- A user's sessions, so that an application can count and close them. -/
def byUser : Index := { name := "by_user", columns := [1] }

def table : TableOf SessionRow where
  table := { name := cfg.name, key := 1,
             columns := [{ name := "id", ty := .int }, { name := "user", ty := .text },
                         { name := "started_s", ty := .int }, { name := "used_s", ty := .int }],
             indexes := [byUser] }
  toRow r := [.int r.id, .text r.user, .int r.started_s, .int r.used_s]
  ofRow
    | [.int id, .text user, .int started_s, .int used_s] => some { id, user, started_s, used_s }
    | _ => none
  ofRow_toRow _ := rfl

def SessionRow.live (r : SessionRow) (now_s : Int64) : Bool :=
  now_s < r.used_s + cfg.idle_s && now_s < r.started_s + cfg.absolute_s

/-- Open a session under an id its token will carry; `false` if the id is taken. -/
def «open» (id : Int64) (user : String) (now_s : Int64) : Txn Bool :=
  (table cfg).insert { id, user, started_s := now_s, used_s := now_s }

/-- The user of a session that is open and not over at `now_s`, which it marks used. A time
before the session was last used is judged as that time, and leaves it: a clock that steps back,
another instance's that lags, or a request that carries no time (`0`) neither ends a session nor
lets one in that is over. -/
def accepts (id : Int64) (now_s : Int64) : Txn (Option String) := do
  match ← (table cfg).get [.int id] with
  | some r =>
    let t := max now_s r.used_s
    if SessionRow.live cfg r t then
      discard <| (table cfg).update { r with used_s := t }
      return some r.user
    else return none
  | none => return none

/-- Close a session: its token lets nobody in again. -/
def close (id : Int64) : Txn Unit := discard <| (table cfg).delete [.int id]

/-- A user's open sessions, at most `limit`, by id. -/
def ofUser (user : String) (limit : Nat) : Txn (List SessionRow) :=
  (table cfg).lookup byUser [.text user] limit

end Sessions

end Lanes.Auth.Rows
