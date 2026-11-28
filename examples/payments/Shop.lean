/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Lanes.Services.Stripe

/-!
# A shop that charges each order once

The shop takes orders and charges each through a payment service (`Lanes.Payments`): a call
that makes and confirms a payment under an idempotency key. The answer may come, come late,
never come, or be `unknown` at the deadline, and a payment that took effect may be reported
only by a webhook, late, twice or out of order. The shop retries a call that times out, up to
`maxAttempts`, and marks an order paid when the answer or a webhook says its payment succeeded.

The key of every call for an order is the order itself, so a retry, a retry after a crash, and a
late answer all name one payment at the service: an order is charged at most once
(`Shop.charged_at_most_once`). The `keyedRetries` switch exists to seed the classic bug: with it
off, a retry is sent without the key, and the checker finds the order charged twice
(`Check.lean`).
-/

namespace Shop

open Lanes

abbrev IntentId := Nat

lanes_data structure Charge where
  order : Nat
  amount : Nat
  deriving DecidableEq, Repr, Hashable

/-- A key that is the order, and nothing else, is the same after a crash. -/
abbrev Request := Idempotent.Keyed Nat Charge

abbrev Answer := Payments.Answer IntentId

abbrev Webhook := Payments.Webhook IntentId Charge

lanes_data inductive In where
  | order (order amount : Nat)
  | reply (call : Nat) (reply : Rpc.Reply Answer)
  | webhook (e : Webhook)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Out where
  | charge (call : Rpc.Call Request)
  | paid (order : Nat)
  | declined (order : Nat)
  /-- The shop holds `maxOrders` orders and took no more. -/
  | full (order : Nat)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Msg where
  | order (order amount : Nat)
  | reply (call : Nat) (reply : Rpc.Reply Answer)
  | webhook (e : Webhook)
  /-- The shop's own deadline for a call: the answer may never come. -/
  | expire (call : Nat)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Status where
  | charging (call attempt : Nat)
  /-- No attempt left, or the payment is still being decided: a webhook will tell. -/
  | waiting
  | paid
  | declined
  deriving DecidableEq, Repr, Hashable

lanes_data structure Order where
  order : Nat
  amount : Nat
  status : Status
  deriving DecidableEq, Repr, Hashable

/-- Durable: a restart that forgot an order would charge it again under a key it no longer
knew, or never tell its customer. -/
lanes_data structure State where
  orders : List Order
  /-- Every call made, with its order. -/
  calls : List (Nat × Nat)
  nextCall : Nat
  deriving DecidableEq, Repr, Hashable

structure Config where
  maxOrders : Nat := 100
  /-- At least one. -/
  maxAttempts : Nat := 3
  deadline_ms : Nat := 10000
  /-- Whether a retry carries the key. Turn off only to seed the bug. -/
  keyedRetries : Bool := true

abbrev sig : Signature where
  Id := Unit
  Msg _ := Msg
  In := In
  Out := Out

abbrev Eff := Effect sig ()

def Config.key (config : Config) (order attempt : Nat) : Option Nat :=
  if attempt = 1 || config.keyedRetries then some order else none

def find (s : State) (order : Nat) : Option Order := s.orders.find? (·.order == order)

def setStatus (s : State) (order : Nat) (status : Status) : State :=
  { s with orders := s.orders.map fun o => if o.order = order then { o with status } else o }

/-- Attempt `attempt` of charging `o`, under a new call. -/
def call (config : Config) (s : State) (o : Order) (attempt : Nat) : State × List Eff :=
  let id := s.nextCall
  ({ setStatus s o.order (.charging id attempt) with
      calls := (id, o.order) :: s.calls, nextCall := id + 1 },
    [.emit (.charge ⟨id, config.deadline_ms, ⟨config.key o.order attempt, ⟨o.order, o.amount⟩⟩⟩),
      .after config.deadline_ms (.expire id)])

/-- The call of attempt `attempt` brought no answer: another, or a wait for a webhook. -/
def retry (config : Config) (s : State) (o : Order) (attempt : Nat) : State × List Eff :=
  if attempt < config.maxAttempts then call config s o (attempt + 1)
  else (setStatus s o.order .waiting, [])

def stopWaiting (o : Order) : List Eff :=
  match o.status with
  | .charging call _ => [.cancel (.expire call)]
  | _ => []

/-- The service says the payment of `o` is in `st`. Paid is final; a decline may still be
followed by a success, when the customer pays another way. -/
def settle (s : State) (o : Order) (st : Payments.Status) : State × List Eff :=
  match o.status, st with
  | .paid, _ => (s, [])
  | _, .succeeded => (setStatus s o.order .paid, stopWaiting o ++ [.emit (.paid o.order)])
  | .declined, _ => (s, [])
  | _, .requiresPaymentMethod =>
    (setStatus s o.order .declined, stopWaiting o ++ [.emit (.declined o.order)])
  | _, _ => (setStatus s o.order .waiting, stopWaiting o)

def place (config : Config) (s : State) (order amount : Nat) : State × List Eff :=
  if (find s order).isSome then (s, [])
  else if config.maxOrders ≤ s.orders.length then (s, [.emit (.full order)])
  else
    let o : Order := ⟨order, amount, .waiting⟩
    call config { s with orders := o :: s.orders } o 1

/-- An answer to call `id`, which may be late: a call given up on still names its order. -/
def replied (config : Config) (s : State) (id : Nat) (reply : Rpc.Reply Answer) :
    State × List Eff :=
  match (s.calls.lookup id).bind (find s) with
  | none => (s, [])
  | some o =>
    match reply, o.status with
    | .answer (.made _ st), _ => settle s o st
    | _, .charging call attempt =>
      if call = id then
        let (s', effs) := retry config s o attempt
        (s', .cancel (.expire call) :: effs)
      else (s, [])
    | _, _ => (s, [])

def expired (config : Config) (s : State) (id : Nat) : State × List Eff :=
  match (s.calls.lookup id).bind (find s) with
  | some o =>
    match o.status with
    | .charging call attempt => if call = id then retry config s o attempt else (s, [])
    | _ => (s, [])
  | none => (s, [])

def step (config : Config) (s : State) : Msg → State × List Eff
  | .order order amount => place config s order amount
  | .reply id reply => replied config s id reply
  | .webhook e =>
    match find s e.params.order with
    | some o => settle s o e.state
    | none => (s, [])
  | .expire id => expired config s id

def rearm (config : Config) (s : State) : List Eff :=
  s.orders.filterMap fun o =>
    match o.status with
    | .charging call _ => some (.after config.deadline_ms (.expire call))
    | _ => none

abbrev shop (config : Config) : System sig where
  State _ := State
  actor _ :=
    { init := ⟨[], [], 0⟩
      step := step config
      recover := fun s => (s, rearm config s) }
  accept
    | .order order amount => ⟨(), .order order amount⟩
    | .reply id reply => ⟨(), .reply id reply⟩
    | .webhook e => ⟨(), .webhook e⟩
  boot := [()]

/-- How the shop's outputs and inputs carry calls, answers and webhooks. -/
def port : Rpc.Port sig Request Answer Webhook where
  called
    | .charge c => some c
    | _ => none
  replied
    | .reply id r => some (id, r)
    | _ => none
  notified
    | .webhook e => some e
    | _ => none

/-- What the payment service may do, each webhook delivered at most `maxDeliveries` times. -/
def service (maxDeliveries : Nat) := Payments.outside port maxDeliveries

/-- What the service holds for the shop. -/
abbrev Held := Rpc.State (Effects.Model Nat IntentId Payments.Status Charge)

def isOrder : In → Bool
  | .order .. => true
  | _ => false

/-- The payments the service may have made for `order`, seen by the shop or not: each one a
charge of the customer's card, or one that may yet be. -/
def charges (held : Held) (order : Nat) : Nat :=
  (held.server.slots.filter (·.request.order == order)).length

/-- No order is charged twice. -/
def chargedAtMostOnce (held : Held) (orders : List Nat) : Bool :=
  orders.all fun order => charges held order ≤ 1

end Shop
