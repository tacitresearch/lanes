/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
`Check.systemReduced` on a driver that keeps what it has seen as a list it only reads as a set:
an actor echoes every input as an output, and the driver sends its inputs in any order and logs
the outputs it sees. Keeping the log sorted merges the worlds that differ only in the order it
was seen in. `Tests/ReduceProofs.lean` proves that the reduced pass is a pass of the plain check
(`Check.systemReduced_sound`).
-/

namespace Tests.Reduce

open Lanes

abbrev sig : Signature where
  Id := Unit
  Msg _ := Nat
  In := Nat
  Out := Nat

/-- Adds each message to its total and echoes it. -/
abbrev echo : System sig where
  State _ := Nat
  actor _ := { init := 0, step := fun s n => (s + n, [.emit n]), recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

instance : sig.Inspect := {}
instance : echo.Inspect := {}

/-- The inputs still to send, and the outputs seen, newest first. -/
abbrev D := List Nat × List Nat

def driver (xs : List Nat) : Driver sig D where
  init := (xs, [])
  inputs d := ((Driver.anyOrder xs).inputs d.1).map fun (x, rest) => (x, (rest, d.2))
  observe d out := (d.1, out :: d.2)

/-- The log, sorted. -/
def canon (w : World echo D) : World echo D :=
  { w with driver := (w.driver.1, w.driver.2.mergeSort) }

def inputs : List Nat := [1, 2, 3, 4]

def props : List (Check.Property (World echo D)) :=
  [ .always "only inputs are seen" fun w => w.driver.2.all (inputs.contains ·),
    .always "no more outputs are seen than inputs sent" fun w =>
      w.driver.2.length + w.driver.1.length ≤ inputs.length,
    .sometimes "every input is seen" fun w => w.driver.2.length == inputs.length ]

def scenario : Scenario sig D := { driver := driver inputs }

def tests : List (String × Bool) :=
  let plain := Check.system echo scenario props
  let reduced := Check.systemReduced echo scenario canon props
  [ ("reduce: the check passes with and without the reduction, and the reduction stores fewer",
      plain.ok && reduced.ok
        && reduced.witnesses.length == 1 && reduced.states < plain.states) ]

end Tests.Reduce
