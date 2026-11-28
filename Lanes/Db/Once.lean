/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Jobs

/-!
# Acting once: an idempotency key stored in the transaction

A request that may arrive twice (a client that retries, a link that hands a message over again,
a call whose `COMMIT` was lost and that runs again) carries a key. `Keys.once key body` runs
`body` and stores the key with its answer in the same transaction; a later run under the key
finds it, runs nothing, and answers what the first answered. The key is the primary key of the
table, so a repeat that races the first is a unique violation, which the driver retries, and the
retry finds the key. Unlike `Lanes.Once.actor`, which keeps its memo in an actor and loses it at
a restart, the keys are rows: a restart forgets none.

`Lanes/Db/OnceSound.lean` proves that a run under a key that committed makes every later run
under it a no-op that answers the same (`Keys.once_again`).
-/

@[expose] public section

namespace Lanes.Db

/-- A table of keys acted on, with the answer each was given. -/
structure Keys (A : Type) where
  name : String
  payload : Jobs.Payload A

namespace Keys

variable {A : Type} (k : Keys A)

def table : Table :=
  { name := k.name, key := 1, columns := [{ name := "key", ty := .text }, { name := "answer", ty := .text }] }

def ofRow : Row → Option (String × A)
  | [.text key, .text answer] => (k.payload.decode answer).map (key, ·)
  | _ => none

def rows : TableOf (String × A) where
  table := k.table
  toRow p := [.text p.1, .text (k.payload.encode p.2)]
  ofRow := k.ofRow
  ofRow_toRow p := by simp [ofRow, k.payload.decode_encode]

/-- Run `body` once under `key`: a key already stored answers what it was given, and runs
nothing. -/
def once (key : String) (body : Txn A) : Txn A := do
  match ← k.rows.get [.text key] with
  | some (_, a) => pure a
  | none =>
    let a ← body
    if ← k.rows.insert (key, a) then pure a else .abort s!"the key {key} was taken in its own transaction"

end Keys

end Lanes.Db
