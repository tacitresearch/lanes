/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Two systems written apart and joined: a front that takes questions and a back that doubles
numbers. The front's queries are wired to the back and the back's results to the front, so from
outside the join takes questions and gives answers, and no query is ever seen leaving.
-/

namespace Tests.Join

open Lanes

inductive FrontIn where
  | ask (n : Nat)
  | reply (n : Nat)
  deriving DecidableEq, Repr, Hashable

inductive FrontOut where
  | query (n : Nat)
  | result (n : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev frontSig : Signature where
  Id := Unit
  Msg _ := FrontIn
  In := FrontIn
  Out := FrontOut

/-- The state counts the answers given. -/
abbrev front : System frontSig where
  State _ := Nat
  actor _ :=
    { init := 0
      step := fun s msg =>
        match msg with
        | .ask n => (s, [.emit (.query n)])
        | .reply n => (s + 1, [.emit (.result n)])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

abbrev backSig : Signature where
  Id := Unit
  Msg _ := Nat
  In := Nat
  Out := Nat

abbrev back : System backSig where
  State _ := Unit
  actor _ := { init := (), step := fun _ n => ((), [.emit (2 * n)]), recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

def wiring : Wiring frontSig backSig where
  toRight
    | .query n => some n
    | .result _ => none
  toLeft n := some (.reply n)

abbrev joined := front.join back wiring

/-- From outside: a number in, a number out. -/
abbrev service := joined.mapIO (In := Nat) (Out := Nat) (fun n => .inl (.ask n)) fun
  | .inl (.result n) => n
  | _ => 0

instance : frontSig.Inspect := {}
instance : front.Inspect := {}
instance : backSig.Inspect := {}
instance : back.Inspect := {}
instance : (joinSig frontSig backSig).Inspect := .join
instance : joined.Inspect := .join
instance : ((joinSig frontSig backSig).withIO Nat Nat).Inspect := .withIO
instance : service.Inspect := .mapIO

def check :=
  Check.system service { driver := Driver.anyOrder [3, 5] }
    [ .always "only doubled questions come out" fun w => w.state.outbox.all (· ∈ [6, 10]),
      .always "the front has answered no more than was asked" fun w =>
        w.state.state (.inl ()) ≤ 2,
      .sometimes "both answers are waiting to leave" fun w =>
        w.state.outbox.length == 2 ]
    { checkDeadlock := true
      terminal := fun w => w.driver.isEmpty && w.state.state (.inl ()) == 2 }

def tests : List (String × Bool) :=
  [ ("join: two systems wired together answer through each other, in every interleaving",
      check.ok && check.complete),
    ("join: a wired output is a message to the other system, not an output of the join",
      match (SysState.init joined {}).run {}
          [.input (.inl (.ask 4)), .start (.inl ()), .deliver ⟨none, .inl (), .ask 4⟩] with
      | some c => c.outbox.isEmpty && c.net == [⟨some (.inl ()), .inr (), (4 : Nat)⟩]
      | none => false) ]

end Tests.Join
