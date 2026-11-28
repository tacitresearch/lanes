/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The queue model (`Lanes/Outside/Queue.lean`) against a consumer that credits an account with
each message it receives and then deletes it. A message may be received again before its
delete is handed over, as a visibility timeout that passes while the consumer works makes it:
without a table of the ids it applied the consumer credits twice, and the checker finds it; with
one it credits each message once, through every redelivery and a crash. Recorded runs are
tested against the model with `Outside.allows`.
-/

namespace Tests.Queue

open Lanes

abbrev Msg := Queue.Message Nat

inductive In where
  | received (receipt : Nat) (m : Msg)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | delete (receipt : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

/-- The ids applied are kept, newest first, up to this many (rule 2.6). -/
def maxApplied : Nat := 8

structure Account where
  balance : Nat := 0
  applied : List Nat := []
  deriving DecidableEq, Repr, Hashable

/-- `dedup` off seeds the bug: every message received is applied. -/
def step (dedup : Bool) (s : Account) : In → Account × List (Effect sig ())
  | .received receipt m =>
    if dedup && m.id ∈ s.applied then (s, [.emit (.delete receipt)])
    else ({ balance := s.balance + m.body, applied := (m.id :: s.applied).take maxApplied },
      [.emit (.delete receipt)])

abbrev consumer (dedup : Bool) : System sig where
  State _ := Account
  actor _ := { init := {}, step := step dedup, recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance (dedup : Bool) : (consumer dedup).Inspect := {}

def port : Queue.Port sig Nat where
  deleted | .delete receipt => some receipt
  received | .received receipt m => some (receipt, m)

def messages : List Msg := [⟨0, 0, 2⟩, ⟨1, 0, 3⟩]

def total : Nat := (messages.map (·.body)).sum

def queue (fifo : Bool := false) (maxReceives : Nat := 2) :=
  Queue.outside port { maxReceives, fifo } messages

/-- Every message the queue holds, with a new receipt. The model says which may come now. -/
def samples (d : Queue.State Nat) : List In :=
  d.messages.map (.received d.receipts.length)

def check (dedup : Bool) (fifo : Bool := false) (maxCrashes : Nat := 0) :=
  Check.system (consumer dedup)
    { driver := (queue fifo).driver samples
      env := { mayCrash := fun _ => true, restarts := fun _ => true }, maxCrashes }
    [ .always "each message is applied at most once" fun w =>
        (w.state.state ()).balance ≤ total,
      .sometimes "a message is received again before its delete" fun w =>
        w.driver.received.any (·.2 == 2),
      .sometimes "every message is applied" fun w => (w.state.state ()).balance == total ]

def steps : Option (Check.Failure (World (consumer false) (Queue.State Nat)) (Event sig)) → Nat
  | some (.violated _ t) => t.steps.length
  | _ => 0

def recv (receipt id : Nat) : Event sig :=
  .input (.received receipt ((messages.find? (·.id == id)).getD ⟨id, 0, 0⟩))

def del (receipt : Nat) : Event sig := .output (.delete receipt)

def tests : List (String × Bool) :=
  let buggy := check false
  let fixed := check true
  let crashing := check true (maxCrashes := 1)
  let fifo := check true (fifo := true)
  [ (s!"queue model: a consumer without a table of applied ids credits twice "
        ++ s!"({steps buggy.failure} steps)",
      match buggy.failure with
      | some (.violated "each message is applied at most once" _) => true
      | _ => false),
    (s!"queue model: with the table each message is applied once, through every redelivery "
        ++ s!"({fixed.states} states)",
      fixed.ok),
    (s!"queue model: and with a crash ({crashing.states} states)", crashing.ok),
    (s!"queue model: and from a FIFO queue ({fifo.states} states)", fifo.ok),
    ("queue model: a message received, its visibility passing, received again and deleted is allowed",
      (queue).allows [recv 0 0, recv 1 0, del 1, recv 2 1, del 2]),
    ("queue model: a message deleted with its latest receipt is not received again",
      !(queue).allows [recv 0 0, del 0, recv 1 0]),
    ("queue model: a delete with an earlier receipt may leave it to be received again",
      (queue (maxReceives := 3)).allows [recv 0 0, recv 1 0, del 0, recv 2 0]),
    ("queue model: a third receive of one copy is not allowed: it is in the dead-letter queue",
      !(queue).allows [recv 0 0, recv 1 0, recv 2 0]),
    ("queue model: a standard queue may give the second message first, a FIFO queue may not",
      (queue).allows [recv 0 1] && !(queue true).allows [recv 0 1]
        && (queue true).allows [recv 0 0, recv 1 1]),
    ("queue model: a receipt is given once", !(queue).allows [recv 0 0, recv 0 1]) ]

end Tests.Queue
