/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reference app: a bank of account actors

Every account is an actor that owns its balance. A transfer is two steps in two lanes: the source
account debits itself and sends a `credit` message, and the destination account applies it. No
state is shared, so the only way money moves between accounts is a message in flight.

Properties:

- per actor: a balance is never negative (`Account.balance_nonneg`);
- system: money is conserved, counting credits in flight (`conserved`), checked here on small
  instances and proved for all instances in `Tests.Fixtures.BankProofs`.

The accounts are generic over the account name type `A`, so the checker runs them with two or
three accounts and production runs them with real identifiers.
-/

namespace Tests.Fixtures.Bank

open Lanes

/-- Identifies a client request, so a response can be matched to it (rule 1.5). -/
abbrev ReqId := Nat

structure Transfer (A : Type) where
  req : ReqId
  src : A
  dst : A
  amount : Nat
  deriving DecidableEq, Repr, Hashable

inductive Request (A : Type) where
  | transfer (t : Transfer A)
  | balance (req : ReqId) (account : A)
  deriving DecidableEq, Repr, Hashable

inductive Outcome where
  /-- The source account was debited and the credit is on its way. -/
  | accepted
  | insufficient
  | balance (amount : Int)
  deriving DecidableEq, Repr, Hashable

structure Response where
  req : ReqId
  outcome : Outcome
  deriving DecidableEq, Repr, Hashable

inductive Msg (A : Type) where
  | transfer (req : ReqId) (dst : A) (amount : Nat)
  | credit (amount : Nat)
  | query (req : ReqId)
  deriving DecidableEq, Repr, Hashable

abbrev sig (A : Type) [DecidableEq A] : Signature where
  Id := A
  Msg _ := Msg A
  In := Request A
  Out := Response

structure Account where
  balance : Int
  deriving DecidableEq, Repr, Hashable

variable {A : Type} [DecidableEq A]

/-- A crash of the actor keeps its balance (`recover`); a restart of the process starts it from
the opening balance. -/
def account (opening : Nat) (self : A) : (sig A).Actor self Account where
  init := { balance := opening }
  step s
    | .transfer req dst amount =>
      if (amount : Int) ≤ s.balance then
        ({ balance := s.balance - amount },
          [.send dst (.credit amount), .emit ⟨req, .accepted⟩])
      else (s, [.emit ⟨req, .insufficient⟩])
    | .credit amount => ({ balance := s.balance + amount }, [])
    | .query req => (s, [.emit ⟨req, .balance s.balance⟩])
  recover s := (s, [])

abbrev bank (A : Type) [DecidableEq A] (opening : Nat) : System (sig A) where
  State _ := Account
  actor := account opening
  accept
    | .transfer t => ⟨t.src, .transfer t.req t.dst t.amount⟩
    | .balance req account => ⟨account, .query req⟩

/-- A balance is never negative. -/
theorem Account.balance_nonneg (opening : Nat) (self : A) :
    (account opening self).Invariant fun s => 0 ≤ s.balance := by
  actor_invariant [account]

/-- In every reachable state of the bank, under any environment model, no balance is negative. -/
theorem balance_nonneg (opening : Nat) (env : EnvModel (sig A)) (a : A) :
    (bank A opening).Invariant env fun c => 0 ≤ (c.state a).balance :=
  System.invariant_of_actor (bank A opening) a (Account.balance_nonneg opening a) env

section Check

variable [Enum A]

/-- The money in a state: all balances, plus every credit in flight. -/
def total {opening : Nat} (c : SysState (bank A opening)) : Int :=
  ((Enum.all (α := A)).map fun a => (c.state a).balance).sum
    + (c.net.map fun e => match e.msg with
        | .credit amount => (amount : Int)
        | .transfer .. | .query _ => 0).sum

/-- Money is conserved: the total is what the accounts opened with. -/
def conserved {opening : Nat} (c : SysState (bank A opening)) : Bool :=
  total c == (Enum.all (α := A)).length * opening

end Check

end Tests.Fixtures.Bank
