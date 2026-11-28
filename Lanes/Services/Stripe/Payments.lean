/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Effects.Basic

/-!
# Payments

A payment as the common payment APIs hold it, with the states and events Stripe documents for a
PaymentIntent. The caller makes one with a request under an idempotency key (a POST with
`Idempotency-Key`), and confirms it with it or leaves the customer's browser to; the payment then
moves on its own as the customer and the banks act, and each move is reported by a webhook.

That a payment service behaves as this model says is a premise of every theorem about a system
that uses it, not a fact: what is assumed, and must be checked against the service's test mode,
is listed in the decision on models of external systems.
-/

@[expose] public section

namespace Lanes.Payments

open Effects

/-- Stripe's `status` of a PaymentIntent, without `requires_capture` (capture is not modelled:
a payment is captured when it succeeds). -/
lanes_data inductive Status where
  | requiresPaymentMethod
  | requiresConfirmation
  | requiresAction
  | processing
  | succeeded
  | canceled
  deriving DecidableEq, Repr, Hashable, Enum

namespace Status

def next : Status → Status → Bool
  | .requiresPaymentMethod, .requiresConfirmation | .requiresPaymentMethod, .requiresAction
  | .requiresPaymentMethod, .processing | .requiresPaymentMethod, .succeeded
  | .requiresPaymentMethod, .canceled => true
  | .requiresConfirmation, .requiresPaymentMethod | .requiresConfirmation, .requiresAction
  | .requiresConfirmation, .processing | .requiresConfirmation, .succeeded
  | .requiresConfirmation, .canceled => true
  | .requiresAction, .requiresPaymentMethod | .requiresAction, .processing
  | .requiresAction, .succeeded | .requiresAction, .canceled => true
  | .processing, .requiresPaymentMethod | .processing, .succeeded => true
  | _, _ => false

/-- No status is final but `succeeded` and `canceled`. A payment that fails goes back to
`requiresPaymentMethod`, and the event says so (`payment_intent.payment_failed`). -/
def phase : Status → Phase
  | .requiresPaymentMethod | .requiresConfirmation => .created
  | .requiresAction | .processing => .pending
  | .succeeded => .succeeded
  | .canceled => .canceled

/-- The webhook sent when a payment enters a status, if any. -/
def event : Status → Option String
  | .requiresPaymentMethod => some "payment_intent.payment_failed"
  | .requiresConfirmation => none
  | .requiresAction => some "payment_intent.requires_action"
  | .processing => some "payment_intent.processing"
  | .succeeded => some "payment_intent.succeeded"
  | .canceled => some "payment_intent.canceled"

end Status

/-- A payment just made may be in any status but `canceled`: declined (`requiresPaymentMethod`),
not yet confirmed, waiting for the customer, processing or already succeeded. -/
def lifecycle : Lifecycle Status where
  first st := st != .canceled
  next := Status.next
  phase := Status.phase
  reported st := (Status.event st).isSome

theorem final : lifecycle.Final := by
  intro a b h
  cases a <;> cases b <;> simp_all [lifecycle, Status.next, Status.phase, Phase.final]

/-- A payment that succeeded stays so. -/
theorem succeeded_terminal : lifecycle.Terminal .succeeded := by
  intro x
  cases x <;> rfl

abbrev Answer (R : Type) : Type := Effects.Answer R Status

abbrev Webhook (R P : Type) : Type := Report R Status P

variable {σ : Signature} {K R P : Type} [DecidableEq K] [DecidableEq R] [DecidableEq P]

/-- What a payment service may do, its webhooks each delivered at most `maxDeliveries` times. -/
def outside (port : Rpc.Port σ (Idempotent.Keyed K P) (Answer R) (Webhook R P))
    (maxDeliveries : Nat) : Outside σ (Rpc.State (Model K R Status P)) :=
  Effects.outside port lifecycle maxDeliveries

end Lanes.Payments
