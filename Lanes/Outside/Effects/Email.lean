/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Effects.Basic

/-!
# Sending email

A message as an email-sending API holds it: the caller sends it with a request under an
idempotency key, the API accepts or rejects it at once, and later reports by webhook that it was
sent on, delivered or bounced. Accepted is not delivered: a message accepted may still bounce, and
a caller that resends one whose answer it never got sends it twice unless the key is the same.

What is assumed of a real API, and must be checked against it, is listed in the decision on
models of external systems.
-/

@[expose] public section

namespace Lanes.Email

open Effects

lanes_data inductive Status where
  /-- Queued by the API. -/
  | accepted
  /-- Refused by the API: a suppressed or invalid address, or content it will not send. -/
  | rejected
  /-- Handed to the recipient's mail server. -/
  | sent
  | delivered
  | bounced
  deriving DecidableEq, Repr, Hashable, Enum

namespace Status

def next : Status → Status → Bool
  | .accepted, .rejected | .accepted, .sent | .accepted, .bounced => true
  | .sent, .delivered | .sent, .bounced => true
  | _, _ => false

def phase : Status → Phase
  | .accepted => .created
  | .sent => .pending
  | .delivered => .succeeded
  | .rejected | .bounced => .failed

end Status

/-- The answer to a send is that the message was accepted or rejected; every move after is
reported, except the queueing itself. -/
def lifecycle : Lifecycle Status where
  first st := st == .accepted || st == .rejected
  next := Status.next
  phase := Status.phase
  reported st := st != .accepted

theorem final : lifecycle.Final := by
  intro a b h
  cases a <;> cases b <;> simp_all [lifecycle, Status.next, Status.phase, Phase.final]

abbrev Answer (R : Type) : Type := Effects.Answer R Status

abbrev Webhook (R P : Type) : Type := Report R Status P

variable {σ : Signature} {K R P : Type} [DecidableEq K] [DecidableEq R] [DecidableEq P]

/-- What an email API may do, its webhooks each delivered at most `maxDeliveries` times. -/
def outside (port : Rpc.Port σ (Idempotent.Keyed K P) (Answer R) (Webhook R P))
    (maxDeliveries : Nat) : Outside σ (Rpc.State (Model K R Status P)) :=
  Effects.outside port lifecycle maxDeliveries

end Lanes.Email
