/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Txn

/-!
# A call, its attempts, and when the driver tries again

A call runs a handler's transaction to its result (`Result`): committed with the handler's
answer, failed (it did not take effect), or unknown (the connection was lost after `COMMIT` was
sent). The driver runs it in attempts, each a transaction of its own, and decides after each
with `Retry.next`, pure, which `Lanes/Services/Postgres/IO/Db.lean` only follows: a conflict (a
serialization failure, a deadlock, or what `Postgres.Sql.retryable` counts with them), or a
connection lost before `COMMIT` was sent, rolled the attempt back, so it is tried again, up to
`attempts_max` attempts; anything else ends the call. A lost `COMMIT` is never tried again: it may have committed.

`Served` is what the server did with an attempt, for the theorem that a call that committed
after retries is one run of its transaction against the state it committed against
(`Retry.loop_committed`, `Lanes/Db/Sound.lean`).
-/

@[expose] public section

namespace Lanes.Db

/-- Why a call failed. A failed call did not take effect. -/
inductive Failure where
  /-- Every attempt met a serialization failure or a deadlock. -/
  | conflict
  /-- No connection, or each was lost before `COMMIT` was sent. -/
  | unavailable
  /-- The transaction aborted, or asked what its schema does not admit. -/
  | aborted (why : String)
  /-- The server refused a statement, with this SQLSTATE. -/
  | error (sqlstate : String)
  deriving DecidableEq, Repr, Hashable

inductive Result (A : Type) where
  | committed (a : A)
  | failed (why : Failure)
  /-- The connection was lost after `COMMIT` was sent: it may or may not have committed. -/
  | unknown
  deriving DecidableEq, Repr, Hashable

/-- How one attempt ended. -/
inductive Attempt (A : Type) where
  | committed (a : A)
  | aborted (why : String)
  /-- A serialization failure or a deadlock: rolled back. -/
  | conflict
  /-- No connection, or it was lost before `COMMIT` was sent: not committed. -/
  | dropped
  /-- The connection was lost after `COMMIT` was sent. -/
  | unknown
  /-- Another error: rolled back. -/
  | error (sqlstate : String)
  deriving DecidableEq, Repr, Hashable

namespace Retry

/-- After attempt `n`, counted from 0, ended so: the call's result, or `none` to try again. -/
def next {A : Type} (attempts_max n : Nat) : Attempt A → Option (Result A)
  | .committed a => some (.committed a)
  | .aborted why => some (.failed (.aborted why))
  | .error s => some (.failed (.error s))
  | .unknown => some .unknown
  | .conflict => if n + 1 < attempts_max then none else some (.failed .conflict)
  | .dropped => if n + 1 < attempts_max then none else some (.failed .unavailable)

/-- The driver's loop, over the outcomes of its attempts from attempt `n`. -/
def loop {A : Type} (attempts_max : Nat) (n : Nat) : List (Attempt A) → Result A
  | [] => .failed .unavailable
  | a :: rest =>
    match next attempts_max n a with
    | some r => r
    | none => loop attempts_max (n + 1) rest

end Retry

/-- What the server did with one attempt: rolled it back for a conflict or lost its connection
before `COMMIT`, or ran it as one serializable transaction against the database `db`. -/
inductive Served where
  | conflict
  | dropped
  | against (db : Db)

/-- The outcome the driver sees of an attempt the server served so: its answer and the state
it committed, when it ran against a database. -/
def Served.attempt {A : Type} (t : Txn A) : Served → Attempt (A × Db)
  | .conflict => .conflict
  | .dropped => .dropped
  | .against db =>
    match t.run db with
    | .ok r => .committed r
    | .error e => .aborted e

end Lanes.Db
