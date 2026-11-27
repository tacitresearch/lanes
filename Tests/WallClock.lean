/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The wall-clock model (`Clock.wall`, `Lanes/Outside/Clock.lean`) against a token that expires
`ttl_ms` after it is issued. Checked as the difference of two wall-clock readings, a token found
expired is found valid again after the clock is set back, and the checker finds it; checked
against the latest time seen (a floor, as `Clock.Wall` and the sessions' `seen_s` keep one), it
never comes back. The bug is not there against a monotonic clock (`Clock.outside`).
-/

namespace Tests.WallClock

open Lanes

inductive In where
  | issue
  | check (n : Nat)
  | time (question time_ms : Nat)
  deriving DecidableEq, Repr, Hashable

inductive Out where
  | ask (question : Nat)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

def ttl_ms : Nat := 2

def skew_ms : Nat := 1

/-- When the token was issued, the latest time seen, and the verdicts given, newest first. -/
structure Tokens where
  issued_ms : Option Nat := none
  seen_ms : Nat := 0
  verdicts : List Bool := []
  deriving DecidableEq, Repr, Hashable

/-- `floor` off seeds the bug: the time is the reading, which may go back. -/
def step (floor : Bool) (s : Tokens) : In → Tokens × List (Effect sig ())
  | .issue => (s, [.emit (.ask 0)])
  | .check n => (s, [.emit (.ask (n + 1))])
  | .time question reading =>
    let now := if floor then max s.seen_ms reading else reading
    let s := { s with seen_ms := max s.seen_ms reading }
    match question, s.issued_ms with
    | 0, _ => ({ s with issued_ms := some now }, [])
    | _, some issued => ({ s with verdicts := decide (now - issued < ttl_ms) :: s.verdicts }, [])
    | _, none => (s, [])

abbrev tokens (floor : Bool) : System sig where
  State _ := Tokens
  actor _ := { init := {}, step := step floor, recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance (floor : Bool) : (tokens floor).Inspect := {}

def port : Clock.Port sig where
  asked | .ask question => some question
  tell := .time
  told
    | .time question time_ms => some (question, time_ms)
    | _ => none

def checks : Nat := 2

/-- The token is issued once and checked `checks` times; each question is asked once. -/
def clients : Outside sig (List Nat) where
  init := []
  allow d
    | .issue => if 0 ∈ d then none else some (0 :: d)
    | .check n => if n + 1 ∈ d ∨ checks ≤ n then none else some ((n + 1) :: d)
    | .time .. => none

def mine (x : sig.In) : Bool := !(x matches .time ..)

/-- A token found expired is not found valid after: the verdicts, oldest first, are some
`true`s and then only `false`s. -/
def expiryHolds (s : Tokens) : Bool :=
  (s.verdicts.reverse.dropWhile (· == true)).all (· == false)

def times : List Nat := List.range 6

def props {D : Type} (floor : Bool) : List (Check.Property (World (tokens floor) D)) :=
  [ .always "an expired token is never valid again" fun w => expiryHolds (w.state.state ()),
    .sometimes "a token is found expired" fun w => (w.state.state ()).verdicts.contains false ]

def checkWall (floor : Bool) :=
  Check.system (tokens floor)
    { driver := (clients.both (Clock.wall port skew_ms) mine).driver fun d =>
        [.issue] ++ (List.range checks).map .check
          ++ d.2.asked.flatMap fun q => times.map (.time q) }
    (props floor)

def checkMonotonic (floor : Bool) :=
  Check.system (tokens floor)
    { driver := (clients.both (Clock.outside port) mine).driver fun d =>
        [.issue] ++ (List.range checks).map .check
          ++ d.2.1.flatMap fun q => times.map (.time q) }
    (props floor)

def steps {S L : Type} : Option (Check.Failure S L) → Nat
  | some (.violated _ t) => t.steps.length
  | _ => 0

def ask (q : Nat) : Event sig := .output (.ask q)

def tell (q t : Nat) : Event sig := .input (.time q t)

def tests : List (String × Bool) :=
  let buggy := checkWall false
  let fixed := checkWall true
  let monotonic := checkMonotonic false
  [ (s!"wall clock: expiry worked out from wall-clock readings comes back after the clock is set back "
        ++ s!"({steps buggy.failure} steps)",
      match buggy.failure with
      | some (.violated "an expired token is never valid again" _) => true
      | _ => false),
    (s!"wall clock: worked out from the latest time seen, it never does ({fixed.states} states)",
      fixed.ok && fixed.complete),
    (s!"wall clock: against a monotonic clock the first is not caught ({monotonic.states} states)",
      monotonic.ok && monotonic.complete),
    ("wall clock: a reading twice the skew before the latest is allowed, and no further",
      (Clock.wall port 1).allows [ask 0, tell 0 5, ask 1, tell 1 3]
        && !(Clock.wall port 1).allows [ask 0, tell 0 5, ask 1, tell 1 2]),
    ("wall clock: a monotonic clock allows no step back",
      !(Clock.outside port).allows [ask 0, tell 0 5, ask 1, tell 1 4]) ]

end Tests.WallClock
