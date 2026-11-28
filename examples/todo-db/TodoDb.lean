/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# todo-db

A to-do list kept in PostgreSQL through the typed store (`Lanes/Db/`). Each request is handled by
one pure transaction (`handler`): add a to-do, complete one, remove one, list a user's. A to-do's
id is chosen in Lean, one more than the largest; the database assigns nothing.

A user's to-dos are unique by title. No constraint says so: `add` first looks the title up by the
index `by_title`, and inserts only if it is not there. `TodoDb/Proofs.lean` proves that every
transaction keeps the invariant (`Unique`), and so, through `Db.invariant`, that every database
the store may hold satisfies it, with lost `COMMIT`s, failures and calls taking effect late.

The actor (`app`) takes requests from users and sends each to the store as a call. A call
answered unknown, or failed, is sent again, up to `attempts_max` times. That is safe because each
request is idempotent: a second `add` of a title finds it. The unchecked handler
(`Config.checked := false`) inserts without looking, and `Check.lean` finds the duplicate a lost
`COMMIT` and a retry make; the checked one keeps every database unique.

`Live.lean` runs the system on a real PostgreSQL through `Postgres.Typed.handler`.
-/

namespace TodoDb

open Lanes.Db

/-! ## The table -/

/-- The table `todos`, keyed by `id`. The index `todos.byTitle` on `(owner, title)` is not
unique: uniqueness is the invariant, proved per transaction. -/
lanes_data structure Todo where
  id : Int64
  owner : Int64
  title : String
  done : Bool := false
  deriving DecidableEq, Repr, Hashable
  table todos key id
    index byTitle on owner, title

def schema : Schema := [todos.table]

/-! ## Requests and their transactions -/

inductive Request where
  | add (owner : Int64) (title : String)
  | complete (owner id : Int64)
  | remove (owner id : Int64)
  | list (owner : Int64)
  deriving DecidableEq, Repr, Hashable

inductive Answer where
  | added (id : Int64)
  /-- The user has a to-do with this title already. -/
  | existing (id : Int64)
  | done
  | missing
  | list (todos : List Todo)
  deriving DecidableEq, Repr, Hashable

/-- The most to-dos a list returns (rule 2.6). -/
def list_max : Nat := 100

/-- The next id: one more than the largest, or 0. -/
def nextId : Txn Int64 := do
  match ← todos.scan { table := todos.table, order := .desc, limit := 1 } with
  | t :: _ => pure (t.id + 1)
  | [] => pure 0

def insertNew (owner : Int64) (title : String) : Txn Answer := do
  let id ← nextId
  if ← todos.insert { id, owner, title } then pure (.added id) else .abort "the next id is taken"

/-- `checked`: look the title up first. -/
def add (checked : Bool) (owner : Int64) (title : String) : Txn Answer :=
  if checked then do
    match ← todos.lookup todos.byTitle [.int owner, .text title] 1 with
    | t :: _ => pure (.existing t.id)
    | [] => insertNew owner title
  else insertNew owner title

def complete (owner id : Int64) : Txn Answer := do
  match ← todos.get [.int id] with
  | some t =>
    if t.owner = owner then do
      let _ ← todos.update { t with done := true }
      pure .done
    else pure .missing
  | none => pure .missing

def remove (owner id : Int64) : Txn Answer := do
  match ← todos.get [.int id] with
  | some t =>
    if t.owner = owner then do
      let _ ← todos.delete [.int id]
      pure .done
    else pure .missing
  | none => pure .missing

def handler (checked : Bool) : Handler Request Answer
  | .add owner title => add checked owner title
  | .complete owner id => complete owner id
  | .remove owner id => remove owner id
  | .list owner => .list <$> todos.scan { table := todos.table, index := some todos.byTitle, eq := [.int owner], limit := list_max }

/-! ## The actor -/

open Lanes

lanes_data inductive Id where
  | app
  deriving DecidableEq, Repr, Hashable, Enum

inductive In where
  /-- A user's request, numbered by the user's client. -/
  | request (n : Nat) (r : Request)
  | store (reply : Db.Reply Answer)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Db.Call Request)
  | answered (n : Nat) (a : Answer)
  /-- Every attempt failed, or the queue was full. -/
  | gaveUp (n : Nat)
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
  checked : Bool := true
  attempts_max : Nat := 2
  inflight_max : Nat := 4

/-- A request sent as the call `call`, after `tries` earlier calls. -/
structure Pending where
  n : Nat
  request : Request
  call : Nat
  tries : Nat
  deriving DecidableEq, Repr, Hashable

structure State where
  pending : List Pending := []
  nextCall : Nat := 0
  deriving DecidableEq, Repr, Hashable

variable (cfg : Config)

def send (s : State) (n : Nat) (r : Request) (tries : Nat) : State × List (Effect sig .app) :=
  ({ pending := s.pending ++ [{ n, request := r, call := s.nextCall, tries }], nextCall := s.nextCall + 1 },
    [.emit (.call { id := s.nextCall, request := r })])

def replied (s : State) (p : Pending) : Db.Result Answer → State × List (Effect sig .app)
  | .committed a => ({ s with pending := s.pending.erase p }, [.emit (.answered p.n a)])
  | _ =>
    let s := { s with pending := s.pending.erase p }
    if p.tries + 1 < cfg.attempts_max then send s p.n p.request (p.tries + 1)
    else (s, [.emit (.gaveUp p.n)])

def step (s : State) : In → State × List (Effect sig .app)
  | .request n r =>
    if cfg.inflight_max ≤ s.pending.length then (s, [.emit (.gaveUp n)]) else send s n r 0
  | .store reply =>
    match s.pending.find? (·.call == reply.id) with
    | some p => replied cfg s p reply.result
    | none => (s, [])

def app : sig.Actor .app State where
  init := {}
  step := step cfg

abbrev system : System sig where
  State _ := State
  actor
    | .app => app cfg
  accept x := ⟨.app, x⟩

/-- How the store sees the system: its calls and the inputs that answer them. -/
def port : Db.Port sig Request Answer where
  call
    | .call c => some c
    | _ => none
  reply r := .store r
  replied
    | .store r => some r
    | _ => none

end TodoDb
