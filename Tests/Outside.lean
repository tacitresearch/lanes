/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The models of external systems (`Lanes/Outside/`), checked beside a payer that pays each order
with a call under the order's key and retries once after `unknown`. Every answer, timeout,
refusal, late, repeated and stale webhook the payment model allows is explored, with crashes;
paying again without the key is caught. Recorded runs, written as a real service would give
them, are tested against the payment and email models with `Outside.allows`.
-/

namespace Tests.Outside

open Lanes

abbrev Keyed := Idempotent.Keyed Nat Nat

abbrev Hook := Payments.Webhook Nat Nat

inductive In where
  | pay (order : Nat)
  | reply (call : Nat) (reply : Rpc.Reply (Payments.Answer Nat))
  | hook (e : Hook)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | call (c : Rpc.Call Keyed)
  | told (order : Nat) (status : Payments.Status)
  deriving DecidableEq, Repr, Hashable

abbrev paySig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- The next call id, and each call made with its order and attempt. -/
structure Payer where
  next : Nat
  calls : List (Nat × Nat × Nat)
  deriving DecidableEq, Repr, Hashable

def Payer.call (s : Payer) (order attempt : Nat) (key : Option Nat) : Payer × List (Effect paySig ()) :=
  ({ next := s.next + 1, calls := (s.next, order, attempt) :: s.calls },
    [.emit (.call ⟨s.next, 1000, ⟨key, order⟩⟩)])

/-- `keyed` off seeds the bug: a retry without the key. -/
def payerStep (keyed : Bool) (s : Payer) : In → Payer × List (Effect paySig ())
  | .pay order => s.call order 1 (some order)
  | .reply id reply =>
    match s.calls.find? (·.1 == id), reply with
    | some (_, order, _), .answer (.made _ st) => (s, [.emit (.told order st)])
    | some (_, order, attempt), _ =>
      if attempt < 2 then s.call order (attempt + 1) (if keyed then some order else none)
      else (s, [])
    | none, _ => (s, [])
  | .hook e => (s, [.emit (.told e.params e.state)])

abbrev payer (keyed : Bool) : System paySig where
  State _ := Payer
  actor _ :=
    { init := ⟨0, []⟩
      step := payerStep keyed
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : paySig.Inspect := {}
instance (keyed : Bool) : (payer keyed).Inspect := {}

def port : Rpc.Port paySig Keyed (Payments.Answer Nat) Hook where
  called
    | .call c => some c
    | .told .. => none
  replied
    | .reply id r => some (id, r)
    | _ => none
  notified
    | .hook e => some e
    | _ => none

/-- Orders still to pay, each once; whether the payer was told a payment succeeded, and whether
it was told `processing` after that. -/
structure Told where
  toPay : List Nat
  succeeded : Bool := false
  stale : Bool := false
  deriving DecidableEq, Hashable

instance : BEq Told := instBEqOfDecidableEq

def customer (orders : List Nat) : Outside paySig Told where
  init := { toPay := orders }
  allow d
    | .pay order => if order ∈ d.toPay then some { d with toPay := d.toPay.erase order } else none
    | _ => none
  observe d
    | .told _ .succeeded => { d with succeeded := true }
    | .told _ .processing => { d with stale := d.stale || d.succeeded }
    | _ => d

abbrev Model := Rpc.State (Effects.Model Nat Nat Payments.Status Nat)

def world (orders : List Nat) := (customer orders).both (Payments.outside port 2) (· matches .pay _)

abbrev PayWorld (keyed : Bool) := World (payer keyed) (Told × Model)

def statuses : List Payments.Status := [.processing, .succeeded]

def samples (d : Told × Model) : List In :=
  let model := d.2.server
  let things := model.inner.inner.things
  let fresh := things.length + 7
  d.1.toPay.map .pay
    ++ d.2.pending.flatMap (fun id =>
      .reply id .unknown :: .reply id (.answer .refused) ::
        ((fresh :: things.map (·.id)).flatMap fun r =>
          statuses.map fun st => .reply id (.answer (.made r st))))
    ++ things.flatMap (fun t => statuses.map fun st => .hook ⟨t.id, st, t.params⟩)
    ++ model.inner.inner.unseen.flatMap fun (_, p) => statuses.map fun st => .hook ⟨fresh, st, p⟩

def keysDistinct (w : PayWorld keyed) : Bool :=
  let keys := w.driver.2.server.slots.filterMap (·.key)
  keys.eraseDups.length == keys.length

def onceEach (w : PayWorld keyed) : Bool :=
  [0, 1].all fun o => (w.driver.2.server.slots.filter (·.request == o)).length ≤ 1

def deliveriesBounded (w : PayWorld keyed) : Bool :=
  w.driver.2.server.inner.delivered.all (·.2 ≤ 2)

def check (keyed : Bool) (orders : List Nat) (maxCrashes : Nat := 0) :=
  Check.system (payer keyed)
    { env := { link := fun _ _ => .unordered, mayCrash := fun _ => true, restarts := fun _ => true }
      driver := (world orders).driver samples, maxCrashes }
    [ .always "no two effects share a key" keysDistinct,
      .always "each order has at most one effect" onceEach,
      .always "each webhook is delivered at most twice" deliveriesBounded,
      .sometimes "a payment is first seen through a webhook" fun w =>
        w.driver.2.server.inner.inner.things.any fun t =>
          (w.driver.2.server.slots[t.slot]?).any (·.result.isNone),
      .sometimes "a retry is answered as the first was" fun w =>
        w.driver.2.server.routes.length > w.driver.2.server.slots.length
          && w.driver.2.server.slots.any (·.result.isSome),
      .sometimes "a webhook is delivered twice" fun w =>
        w.driver.2.server.inner.delivered.any (·.2 == 2),
      .sometimes "a stale webhook comes after the payment succeeded" (·.driver.1.stale) ]
    { maxStates := 400000 }

/-! Recorded runs: what a service may send, checked against the models. -/

def outPay (id : Nat) (key : Option Nat) : Event paySig := .output (.call ⟨id, 1000, ⟨key, 0⟩⟩)

def inReply (id : Nat) (r : Rpc.Reply (Payments.Answer Nat)) : Event paySig := .input (.reply id r)

def inHook (st : Payments.Status) (intent : Nat := 7) : Event paySig := .input (.hook ⟨intent, st, 0⟩)

/-- A timeout, a retry under the same key answered with the payment its webhook named first, a
webhook repeated and one about an earlier status after a later one. -/
def recorded : List (Event paySig) :=
  [outPay 0 (some 0), inReply 0 .unknown, outPay 1 (some 0), inHook .processing,
    inReply 1 (.answer (.made 7 .processing)), inHook .succeeded, inHook .processing,
    inHook .succeeded]

def model := Payments.outside port 2

inductive MailIn where
  | reply (call : Nat) (reply : Rpc.Reply (Email.Answer Nat))
  | hook (e : Email.Webhook Nat Nat)
  deriving DecidableEq

abbrev mailSig : Signature where
  Id := Unit
  Msg _ := MailIn
  In := MailIn
  Out := Rpc.Call Keyed

def mailPort : Rpc.Port mailSig Keyed (Email.Answer Nat) (Email.Webhook Nat Nat) where
  called c := some c
  replied
    | .reply id r => some (id, r)
    | .hook _ => none
  notified
    | .hook e => some e
    | .reply .. => none

def mail := Email.outside mailPort 2

def send (id : Nat) (key : Option Nat := some 3) : Event mailSig := .output ⟨id, 1000, ⟨key, 3⟩⟩

def mailHook (st : Email.Status) : Event mailSig := .input (.hook ⟨5, st, 3⟩)

/-- A send that timed out, sent again under its key, accepted, then sent on and delivered,
the delivery reported twice. -/
def mailRecorded : List (Event mailSig) :=
  [send 0, .input (.reply 0 .unknown), send 1, .input (.reply 1 (.answer (.made 5 .accepted))),
    mailHook .sent, mailHook .delivered, mailHook .delivered]

def slotsAfter (events : List (Event mailSig)) : Option Nat :=
  (mail.after events).map (·.server.slots.length)

def tests : List (String × Bool) :=
  let keyed := check true [0]
  let crashing := check true [0] (maxCrashes := 1)
  let unkeyed := check false [0]
  [ (s!"payments model: one effect per order under every answer, timeout and webhook "
        ++ s!"({keyed.states} states)",
      keyed.ok && keyed.witnesses.length == 4),
    (s!"payments model: the same with a crash ({crashing.states} states)",
      crashing.ok),
    ("payments model: a retry without the key is a second effect",
      match unkeyed.failure with
      | some (.violated "each order has at most one effect" _) => true
      | _ => false),
    ("payments model: a recorded run with a timeout, a retry and late webhooks is allowed",
      model.allows recorded),
    ("payments model: a retry answered with another payment is not",
      !model.allows [outPay 0 (some 0), inReply 0 (.answer (.made 7 .processing)),
        outPay 1 (some 0), inReply 1 (.answer (.made 8 .processing))]),
    ("payments model: a third delivery of one webhook is not",
      !model.allows (recorded ++ [inHook .succeeded])),
    ("payments model: a canceled webhook after success is not",
      !model.allows (recorded ++ [inHook .canceled])),
    ("payments model: a webhook for a payment nobody asked for is not",
      !model.allows [inHook .succeeded]),
    ("email model: a recorded run with a timeout, a resend and a repeated webhook is allowed",
      mail.allows mailRecorded),
    ("email model: a resend under the key is one message, without it two",
      slotsAfter [send 0, send 1] == some 1 && slotsAfter [send 0 none, send 1 none] == some 2),
    ("email model: a bounce after delivery is not allowed",
      !mail.allows (mailRecorded ++ [mailHook .bounced])),
    ("email model: a message rejected at once may be reported rejected, not delivered",
      mail.allows [send 0, .input (.reply 0 (.answer (.made 5 .rejected))), mailHook .rejected]
        && !mail.allows [send 0, .input (.reply 0 (.answer (.made 5 .rejected))),
          mailHook .delivered]) ]

end Tests.Outside
