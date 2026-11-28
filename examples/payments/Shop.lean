/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# A shop that charges each order once

The shop keeps its orders in PostgreSQL through the typed store (`Lanes/Db/`), and charges each
through a payment service (`Lanes.Payments`) from an outbox (`Lanes/Db/Jobs.lean`):

- **Placing an order** is one transaction under the customer's idempotency key
  (`Keys.once`): it adds the order and, in the same transaction, a charge to the outbox, under
  the key `charge-<order>`. A request that arrives twice, or whose `COMMIT` was lost and that
  runs again, places the order once; an order placed twice under two keys is refused the second
  time.
- **The worker** (`Lanes/Db/Worker.lean`) makes each charge with the job's id as the payment's
  idempotency key, again after a backoff while the service refuses or does not answer, and
  again under the same key after a restart. Its attempt is named by the job and its lease, not
  by a counter that a restart sets back.
- **An order is paid** only by a webhook's transaction that says its payment succeeded; a
  webhook that says it was declined declines an order not yet paid. The answer to a charge says
  only that the payment exists.

`Shop/Proofs.lean` proves that the service makes at most one payment for each order, in every
run, with restarts (`Shop.charged_at_most_once`).
-/

namespace Shop

open Lanes Lanes.Db Lanes.Db.Jobs

abbrev IntentId := Nat

structure Charge where
  order : Int64
  amount : Int64
  deriving DecidableEq, Repr, Hashable

def chargePayload : Payload Charge :=
  (Payload.pair Payload.int64 Payload.int64 Payload.int64_colon).iso (fun c => (c.order, c.amount))
    (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

/-- The outbox of charges. -/
def charges : Queue Charge := { name := "charges", payload := chargePayload }

/-- The key of an order's charge in the outbox: one charge for each order. -/
def chargeKey (order : Int64) : String := s!"charge-{order.toInt}"

inductive Status where
  | placed
  | paid
  | declined
  deriving DecidableEq, Repr, Hashable

def Status.code : Status → Int64
  | .placed => 0
  | .paid => 1
  | .declined => 2

def Status.ofCode (i : Int64) : Option Status :=
  if i = 0 then some .placed else if i = 1 then some .paid else if i = 2 then some .declined else none

structure Order where
  id : Int64
  amount : Int64
  status : Status
  deriving DecidableEq, Repr, Hashable

def orders : TableOf Order where
  table := { name := "orders", key := 1,
             columns := [{ name := "id", ty := .int }, { name := "amount", ty := .int }, { name := "status", ty := .int }] }
  toRow o := [.int o.id, .int o.amount, .int o.status.code]
  ofRow
    | [.int id, .int amount, .int status] => (Status.ofCode status).map fun status => { id, amount, status }
    | _ => none
  ofRow_toRow o := by cases o with | mk id amount status => cases status <;> rfl

def boolPayload : Payload Bool where
  encode b := if b then "1" else "0"
  decode s := if s = "1" then some true else if s = "0" then some false else none
  decode_encode b := by cases b <;> rfl

/-- The customers' idempotency keys, with whether the order was placed. -/
def placed : Keys Bool := { name := "placed", payload := boolPayload }

def schema : Schema := [orders.table, charges.table, placed.table]

abbrev Answer := Payments.Answer IntentId

abbrev Webhook := Payments.Webhook IntentId Charge

inductive Action where
  /-- Place an order, under the customer's idempotency key. -/
  | place (key : String) (order amount : Int64)
  | webhook (w : Webhook)
  | status (order : Int64)
  deriving DecidableEq, Repr, Hashable

inductive Reply where
  | placed
  /-- The order was placed already, under another key. -/
  | refused
  | status (s : Option Status)
  | noted
  deriving DecidableEq, Repr, Hashable

/-- Add the order and its charge, unless the order is there. -/
def add (order amount : Int64) : Txn Bool := do
  match ← orders.get [.int order] with
  | some _ => pure false
  | none =>
    if ← orders.insert { id := order, amount, status := .placed } then
      discard <| charges.enqueue (chargeKey order) { order, amount } 0
      pure true
    else pure false

def place (key : String) (order amount : Int64) : Txn Reply := do
  if ← placed.once key (add order amount) then pure .placed else pure .refused

/-- What a webhook says of its order: paid once it succeeded, which nothing undoes; declined if
not paid yet. -/
def settle (o : Order) : Payments.Status → Option Order
  | .succeeded => if o.status = .paid then none else some { o with status := .paid }
  | .requiresPaymentMethod => if o.status = .placed then some { o with status := .declined } else none
  | _ => none

def webhook (w : Webhook) : Txn Reply := do
  match ← orders.get [.int w.params.order] with
  | some o =>
    match settle o w.state with
    | some o' => discard <| orders.update o'
    | none => pure ()
    pure .noted
  | none => pure .noted

def handler : Handler Action Reply
  | .place key order amount => place key order amount
  | .webhook w => webhook w
  | .status order => do return .status ((← orders.get [.int order]).map (·.status))

/-! ## The worker -/

/-- A payment made, in whatever status, is the charge done: what it comes to, a webhook tells.
A refusal is a repeat while the first is being handled: try again. -/
def classify : Answer → Verdict
  | .made _ _ => .ok
  | .refused => .retry "refused for now"

structure Config where
  jobs : Jobs.Config := { attempts_max := 5, lease_ms := 30000, backoff_ms := 1000 }
  attempt_ms : Nat := 10000

def Config.worker (config : Config) : Worker.Config Answer :=
  { jobs := config.jobs, attempt_ms := config.attempt_ms, claim_ms := config.attempt_ms, classify }

/-- The store's handler: the shop's transactions and the worker's. -/
def store (config : Config) : Handler (Action ⊕ Req) (Reply ⊕ Ans Charge) :=
  beside handler (charges.handler config.jobs)

/-- The transactions that carry an event of the payment service: webhooks. -/
def event : Action → Option Webhook
  | .webhook w => some w
  | _ => none

abbrev sig := Worker.sig Action Reply Charge Answer

abbrev worker (config : Config) : System sig :=
  Worker.system (Q := Action) (A := Reply) (W := Charge) config.worker

/-- The payment service behind keys, each webhook delivered at most `maxDeliveries` times. -/
def service (maxDeliveries : Nat) :
    Rpc.Server (Effects.Model Int64 IntentId Payments.Status Charge) (Idempotent.Keyed Int64 Charge)
      Answer Webhook :=
  Effects.service Payments.lifecycle maxDeliveries

/-- The worker's outsides: any clients, the store with the shop's transactions, and the payment
service, which sends the webhooks. -/
def world {D : Type} (clients : Outside sig D) (dbcfg : Db.Config) (config : Config) (start : Db)
    (maxDeliveries : Nat) :=
  Worker.world clients dbcfg (store config) start (service maxDeliveries) event

/-- The payments the service may have made for `order`, seen by the shop or not. -/
def chargesFor {S : Type} (held : Rpc.State (Idempotent.State Int64 Charge Answer S)) (order : Int64) : Nat :=
  (held.server.slots.filter (·.request.order == order)).length

end Shop
