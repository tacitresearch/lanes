/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# todo-db

A to-do list kept in PostgreSQL. One actor takes `add key title` from its users and stores each
to-do in a transaction of the store (`Lanes/Outside/Store/Basic.lean`): `begin`, the insert,
`commit`. When an answer does not come, or says the transaction failed, it tries again in a new
transaction, up to `attempts_max` times.

The classic bug is there to be found (`Config.keyed := false`): the to-do is appended, under a key
the database chooses, and a `COMMIT` whose answer is lost is retried. If the lost commit had
taken effect, or takes effect later, the list now has the to-do twice. `Check.lean` runs the
checker against the store model, which keeps both outcomes of a lost commit, and it finds the
duplicate. The fix (`keyed := true`) stores the to-do under the key its user gave it, which
identifies the request: a retry first reads that key, and inserts only if it is not there; the
key is the table's primary key, so a second insert of it fails rather than adding a row. The
checker finds no duplicate, and `TodoDb/Proofs.lean` proves what the fix rests on.

`Live.lean` runs the system on a real PostgreSQL through `Postgres.Store.handler`.
-/

namespace TodoDb

open Lanes

lanes_data inductive Id where
  | app
  deriving DecidableEq, Repr, Hashable, Enum

abbrev Request := Store.Request Nat String

abbrev Reply := Store.Reply Nat String

inductive In where
  /-- A user adds a to-do; `key` is chosen by the user's client and identifies the request. -/
  | add (key : Nat) (title : String)
  | store (reply : Reply)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | store (request : Request)
  /-- The to-do is stored. -/
  | added (key : Nat)
  /-- It could not be stored: the queue was full or every attempt failed. -/
  | gaveUp (key : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev Msg : Id → Type
  | .app => In

instance : ∀ i, DecidableEq (Msg i) := by instance_by_cases

abbrev sig : Signature where
  Id := Id
  Msg := Msg
  In := In
  Out := Out

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  /-- The fix: store a to-do under its user's key, read that key first, insert only if it is free. -/
  keyed : Bool
  attempts_max : Nat := 2
  queue_max : Nat := 4

inductive Stage where
  | begin
  /-- Reading the key, before inserting (the fix only). -/
  | check
  | insert
  | commit
  deriving DecidableEq, Repr, Hashable

/-- The to-do being stored, the transaction it is tried in, and the request waited for. -/
structure Attempt where
  key : Nat
  title : String
  txn : Nat
  stage : Stage
  /-- The number of the request whose answer the attempt waits for. -/
  request : Nat
  tries : Nat
  deriving DecidableEq, Repr, Hashable

structure State where
  waiting : List (Nat × String) := []
  current : Option Attempt := none
  nextTxn : Nat := 0
  nextRequest : Nat := 0
  deriving DecidableEq, Repr, Hashable

variable (cfg : Config)

/-- Send an operation of the attempt's transaction, and wait for its answer. -/
def ask (s : State) (a : Attempt) (stage : Stage) (op : Store.Op Nat String) :
    State × List (Effect sig .app) :=
  ({ s with current := some { a with stage, request := s.nextRequest }, nextRequest := s.nextRequest + 1 },
    [.emit (.store { id := s.nextRequest, txn := a.txn, op })])

/-- Begin a new transaction for the to-do `key`, `title`, after `tries` tries. -/
def attempt (s : State) (key : Nat) (title : String) (tries : Nat) : State × List (Effect sig .app) :=
  ask { s with nextTxn := s.nextTxn + 1 }
    { key, title, txn := s.nextTxn, stage := .begin, request := 0, tries } .begin .begin

/-- Take the next to-do waiting, if nothing is being stored. -/
def next (s : State) : State × List (Effect sig .app) :=
  match s.current, s.waiting with
  | none, (key, title) :: rest => attempt { s with waiting := rest } key title 0
  | _, _ => (s, [])

def finish (s : State) (out : Out) : State × List (Effect sig .app) :=
  let (s, effects) := next { s with current := none }
  (s, .emit out :: effects)

/-- The attempt failed: try again in a new transaction, or give up. -/
def retry (s : State) (a : Attempt) : State × List (Effect sig .app) :=
  if a.tries + 1 < cfg.attempts_max then attempt s a.key a.title (a.tries + 1)
  else finish s (.gaveUp a.key)

/-- The answer to the request the attempt waits for. -/
def answered (s : State) (a : Attempt) : Store.Answer Nat String → State × List (Effect sig .app)
  | .failed | .unknown => retry cfg s a
  | answer =>
    match a.stage, answer with
    | .begin, _ =>
      if cfg.keyed then ask s a .check (.read a.key) else ask s a .insert (.append a.title)
    | .check, .value (some _) =>
      let (s', effects) := finish { s with nextRequest := s.nextRequest + 1 } (.added a.key)
      (s', .emit (.store { id := s.nextRequest, txn := a.txn, op := .rollback }) :: effects)
    | .check, .value none => ask s a .insert (.insert a.key a.title)
    | .check, _ => retry cfg s a
    | .insert, _ => ask s a .commit .commit
    | .commit, .committed => finish s (.added a.key)
    | .commit, _ => retry cfg s a

def step (s : State) : In → State × List (Effect sig .app)
  | .add key title =>
    if cfg.queue_max ≤ s.waiting.length then (s, [.emit (.gaveUp key)])
    else next { s with waiting := s.waiting ++ [(key, title)] }
  | .store reply =>
    match s.current with
    | some a => if reply.id == a.request then answered cfg s a reply.answer else (s, [])
    | none => (s, [])

def app : sig.Actor .app State where
  init := {}
  step := step cfg

abbrev system : System sig where
  State _ := State
  actor
    | .app => app cfg
  accept x := ⟨.app, x⟩

/-- How the store sees the system: its requests and the inputs that answer them. -/
def port : Store.Port sig Nat String where
  request
    | .store r => some r
    | _ => none
  reply r := .store r
  replied
    | .store r => some r
    | _ => none

end TodoDb
