/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The store model (`Lanes/Outside/Store/Basic.lean`) as the checker drives it, with a system that
runs one transaction at a time from a script: `begin`, a write, `commit`, then a read in a new
transaction. The store answers each request with what it may, fails it, or loses the answer.
What the system reads after a commit answered `committed` is always what it wrote; after a
commit whose answer was lost it may read either value, and both happen.
-/

namespace Tests.StoreModel

open Lanes

lanes_data inductive Id where
  | client
  deriving DecidableEq, Repr, Hashable, Enum

abbrev Request := Store.Request Nat Nat

abbrev Reply := Store.Reply Nat Nat

inductive Out where
  | store (r : Request)
  /-- What the read of key 1 gave, after the commit was answered `committed` or not. -/
  | read (committed : Bool) (value : Option Nat)
  deriving DecidableEq, Repr, Hashable

abbrev Msg : Id → Type
  | .client => Reply

abbrev sig : Signature where
  Id := Id
  Msg := Msg
  In := Reply
  Out := Out

instance : ∀ i, DecidableEq (Msg i) := by instance_by_cases
instance : sig.Inspect := by instance_by_cases

/-- The step the client is at, the request it waits on, and how its commit was answered. -/
structure State where
  stage : Nat := 0
  committed : Bool := false
  deriving DecidableEq, Repr, Hashable

def send (s : State) (txn : Nat) (op : Store.Op Nat Nat) : State × List (Effect sig .client) :=
  ({ s with stage := s.stage + 1 }, [.emit (.store { id := s.stage, txn, op })])

def step (s : State) (reply : Reply) : State × List (Effect sig .client) :=
  if reply.id != s.stage - 1 then (s, [])
  else
    match s.stage, reply.answer with
    | 1, .ok => send s 0 (.write 1 7)
    | 2, .ok => send s 0 .commit
    | 3, a => send { s with committed := a == .committed } 1 .begin
    | 4, .ok => send s 1 (.read 1)
    | 5, .value v => ({ s with stage := 6 }, [.emit (.read s.committed v)])
    | _, _ => ({ s with stage := 6 }, [])

abbrev system : System sig where
  State _ := State
  actor _ := { init := {}, step, recover := fun _ => ({ stage := 1 }, [.emit (.store { id := 0, txn := 0, op := .begin })]) }
  accept r := ⟨.client, r⟩
  boot := [.client]

instance : system.Inspect := by instance_by_cases

def port : Store.Port sig Nat Nat where
  request
    | .store r => some r
    | _ => none
  reply r := r
  replied r := some r

def model (isolation : Store.Isolation) : Store.Config Nat :=
  { isolation, nextKey := fun keys => keys.foldl max 0 + 1 }

def reads (w : World system (Store.State Nat Nat)) : List (Bool × Option Nat) :=
  w.state.outbox.filterMap fun | .read c v => some (c, v) | _ => none

/-- Not a constant, so that the search runs when the tests do, not whenever the test binary
starts. -/
@[never_extract] def check (isolation : Store.Isolation) :=
  Check.system system
    { driver := (Store.outside (model isolation) port).driver (Store.samples (model isolation) port true true) }
    [ .always "after a commit answered committed, the write is read" fun w =>
        (reads w).all fun (c, v) => !c || v == some 7,
      .always "a read gives the write or nothing" fun w =>
        (reads w).all fun (_, v) => v == some 7 || v == none,
      .sometimes "after a lost commit the write is read" fun w =>
        (reads w).any (· == (false, some 7)),
      .sometimes "after a lost commit nothing is read" fun w =>
        (reads w).any (· == (false, none)) ]

def checks : IO (List (String × Bool)) := do
  let rc := check .readCommitted
  let ser := check .serializable
  return [ ("store model: a committed write is read, and a lost commit's may or may not be, at read committed",
      rc.ok && rc.complete),
    ("store model: and at serializable", ser.ok && ser.complete) ]

end Tests.StoreModel
