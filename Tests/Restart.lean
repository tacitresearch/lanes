/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The checker explores process restarts (`Event.restart`) where the environment model allows them
(`EnvModel.mayRestart`) and within the scenario's budget (`Scenario.maxRestarts`), as it does
crashes. A counter that reports its count after each input keeps its bound across a restart,
since a restart takes it back to zero, but it can fall below a count the outside has seen: the
checker finds the restart after a report. Without restarts, or with a budget of none, it never
does.
-/

namespace Tests.Restart

open Lanes

abbrev sig : Signature where
  Id := Unit
  Msg _ := Unit
  In := Unit
  Out := Nat

/-- Counts the inputs and reports the count after each. -/
abbrev counter : System sig where
  State _ := Nat
  actor _ := { init := 0, step := fun n _ => (n + 1, [.emit (n + 1)]) }
  accept x := ⟨(), x⟩
  boot := [()]

instance : sig.Inspect := {}
instance : counter.Inspect := {}

/-- Sends three inputs, and remembers the counts it sees, newest first. -/
def driver : Driver sig (Nat × List Nat) where
  init := (3, [])
  inputs
    | (k + 1, seen) => [((), (k, seen))]
    | (0, _) => []
  observe d out := (d.1, out :: d.2)

abbrev W := World counter (Nat × List Nat)

def bounded : Check.Property W :=
  .always "the count is at most the inputs sent" fun w => w.state.state () ≤ 3 - w.driver.1

def atLeastSeen : Check.Property W :=
  .always "the count is at least every count seen" fun w =>
    w.driver.2.all (· ≤ w.state.state ())

def restarted : Check.Property W :=
  .sometimes "the process restarted" fun w => w.restarts == 1

def check (env : EnvModel sig) (maxRestarts : Nat) (props : List (Check.Property W)) :=
  Check.system counter { env, driver, maxRestarts } props

def tests : List (String × Bool) :=
  let none := check {} 0 [bounded, atLeastSeen]
  let down := check { mayRestart := true } 1 [atLeastSeen]
  let kept := check { mayRestart := true } 1 [bounded, restarted]
  let budget := check { mayRestart := true } 0 [bounded, atLeastSeen]
  [ (s!"restart: without restarts the count never falls below one seen ({none.states} states)",
      none.ok),
    ("restart: with one restart the checker finds the count below one seen, after a restart",
      match down.failure with
      | some (.violated "the count is at least every count seen" t) => t.labels.contains .restart
      | _ => false),
    (s!"restart: the bound holds across a restart, and a restart is reached ({kept.states} states)",
      kept.ok),
    ("restart: a budget of no restarts explores none, though the environment allows them",
      budget.ok && budget.states == none.states) ]

end Tests.Restart
