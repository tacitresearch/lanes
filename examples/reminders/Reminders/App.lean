/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reminders: work that is due later, in a jobs table

A reminder is a text and a time. Each is a job of the table `reminders` (`Lanes.Db.Jobs`),
written by the request that asks for it, due at its time; the worker
(`Lanes/Db/Worker.lean`) posts it then to a notification service, under the job's id as the
idempotency key, and again after a backoff until the service takes it, its attempts run out, or
it is cancelled. Everything is in the table, so a restart loses no reminder and repeats none
that was taken.

Each request is one transaction (`handler`) of an `Action`: remind, cancel, list. No more than
`maxReminders` reminders wait at once (`remind` counts them first). The front (`front`) holds
nothing: it sends each request to the store under the request's own id, and answers it with
what the store answered.
-/

namespace Reminders

open Lanes Lanes.Db Lanes.Db.Jobs

def payload : Payload String := { encode := id, decode := some, decode_encode := fun _ => rfl }

def queue : Queue String := { name := "reminders", payload }

def schema : Schema := [queue.table]

/-- Every limit is explicit (Lanes rule 2.6). -/
structure Config where
  maxReminders : Nat := 100
  maxText_bytes : Nat := 280
  /-- The most reminders a list shows, the latest first. -/
  shown_max : Nat := 50
  jobs : Jobs.Config := { attempts_max := 5, lease_ms := 30000, backoff_ms := 1000, backoff_max_ms := 60000 }

inductive Action where
  | remind (text : String) (due_ms : Int64)
  | cancel (id : Int64)
  | list
  deriving DecidableEq, Repr, Hashable

/-- A notice, and the reminders after the request. -/
structure Answer where
  notice : String
  reminders : List (Job String)
  deriving DecidableEq, Repr, Hashable

variable (config : Config)

/-- The reminders waiting, at most `maxReminders`. -/
def waiting : Txn (List (Job String)) :=
  queue.rows.scan (queue.due Int64.maxValue config.maxReminders)

def shown : Txn (List (Job String)) :=
  queue.rows.scan { table := queue.table, order := .desc, limit := min config.shown_max Scan.limit_max }

def answer (notice : String) : Txn Answer := do
  return { notice, reminders := ← shown config }

def remind (text : String) (due_ms : Int64) : Txn Answer := do
  if text.isEmpty || config.maxText_bytes < text.utf8ByteSize then
    answer config s!"A reminder is between 1 and {config.maxText_bytes} bytes."
  else if config.maxReminders ≤ (← waiting config).length then
    answer config "Too many reminders wait."
  else
    let id ← queue.nextId
    discard <| queue.enqueue s!"#{id}" text due_ms
    answer config "Scheduled."

def cancel (id : Int64) : Txn Answer := do
  match ← queue.rows.get [.int id] with
  | some j =>
    if ← queue.cancel j.key then answer config "Cancelled." else answer config "That reminder does not wait."
  | none => answer config "No such reminder."

def handler : Handler Action Answer
  | .remind text due_ms => remind config text due_ms
  | .cancel id => cancel config id
  | .list => answer config ""

/-- The store's handler: the application's transactions and the worker's. -/
def store : Handler (Action ⊕ Req) (Answer ⊕ Ans String) := beside (handler config) (queue.handler config.jobs)

/-! ## The front -/

inductive In where
  /-- A request, numbered by the server. -/
  | request (n : Nat) (a : Action)
  | store (reply : Db.Reply (Answer ⊕ Ans String))
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Db.Call (Action ⊕ Req))
  | answered (n : Nat) (a : Answer)
  /-- The store failed the request, or its answer is not known. -/
  | failed (n : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- A request goes to the store under its own number, and its answer comes back under it: the
front keeps nothing, so a restart forgets nothing. -/
def step : In → List (Effect sig ())
  | .request n r => [.emit (.call ⟨n, .inl r⟩)]
  | .store ⟨n, .committed (.inl a)⟩ => [.emit (.answered n a)]
  | .store ⟨_, .committed (.inr _)⟩ => []
  | .store ⟨n, _⟩ => [.emit (.failed n)]

def front : sig.Actor () Unit where
  init := ()
  step _ x := ((), step x)

abbrev system : System sig where
  State _ := Unit
  actor _ := front
  accept x := ⟨(), x⟩

def port : Db.Port sig (Action ⊕ Req) (Answer ⊕ Ans String) where
  call
    | .call c => some c
    | _ => none
  reply r := .store r
  replied
    | .store r => some r
    | _ => none

/-! ## The worker -/

/-- The service's answer to a delivery: its HTTP status, `2xx` taken, `4xx` refused for good. -/
def classify (status : Nat) : Verdict :=
  if 200 ≤ status ∧ status < 300 then .ok
  else if 400 ≤ status ∧ status < 500 then .fatal s!"refused: {status}"
  else .retry s!"status {status}"

def Config.worker (attempt_ms : Nat := 5000) : Worker.Config Nat :=
  { jobs := config.jobs, attempt_ms, claim_ms := attempt_ms, classify }

end Reminders
