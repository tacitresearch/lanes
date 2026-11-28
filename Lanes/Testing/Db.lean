/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Model

/-!
The typed store in memory, for a test of a whole application without a PostgreSQL: each call
runs its handler's transaction on a database held in a reference, one at a time, as `Txn.run`
says. So every call commits in the order it was made, and none conflicts, fails or is lost: what
the store's model allows beyond that is the model checker's to explore, and PostgreSQL's
behaviour the driver's tests'.
-/

@[expose] public section

namespace Lanes.Testing

open Lanes.Db

structure Store (Q A : Type) where
  db : IO.Ref Db
  handler : Handler Q A

namespace Store

variable {Q A : Type}

/-- A store whose tables hold nothing. -/
def empty (schema : Schema) (handler : Handler Q A) : BaseIO (Store Q A) :=
  return { db := ← IO.mkRef (Db.empty schema), handler }

/-- Run a call: committed with what its transaction answers, or failed if it aborts, which
changes nothing. -/
def call (s : Store Q A) (q : Q) : BaseIO (Result A) :=
  s.db.modifyGet fun db =>
    match (s.handler q).run db with
    | .ok (a, db') => (.committed a, db')
    | .error why => (.failed (.aborted why), db)

end Store

end Lanes.Testing
