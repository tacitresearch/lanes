/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-! Tests of the bank reference app: model checking, the scheduler and trace replay. -/

namespace Tests.Bank

open Lanes Examples.Bank

instance : (sig (Fin 2)).Inspect := {}
instance : (bank (Fin 2) 2).Inspect := {}

abbrev Bank2 := bank (Fin 2) 2
abbrev W := World Bank2 (List (Request (Fin 2)))

def transfers : List (Request (Fin 2)) :=
  [.transfer ⟨1, 0, 1, 1⟩, .transfer ⟨2, 1, 0, 3⟩, .transfer ⟨3, 0, 1, 2⟩]

def props : List (Check.Property W) :=
  [ .always "money is conserved" fun w => conserved w.state,
    .always "no negative balance" fun w =>
      (Enum.all (α := Fin 2)).all fun a => 0 ≤ (w.state.state a).balance,
    .sometimes "a credit arrives" fun w =>
      (Enum.all (α := Fin 2)).any fun a => (w.state.state a).balance > 2,
    .sometimes "a transfer is rejected" fun w =>
      w.state.outbox.any fun r => r.outcome == .insufficient ]

def lossy : EnvModel (sig (Fin 2)) := { link := fun _ _ => Link.network }

def tests : List (String × Bool) :=
  let reliable := Check.system Bank2 { driver := Driver.anyOrder transfers } props
  let broken := Check.system Bank2 { env := lossy, driver := Driver.anyOrder transfers } props
  let run := simulate Bank2 { driver := Driver.anyOrder transfers } (seed := 42)
  let again := simulate Bank2 { driver := Driver.anyOrder transfers } (seed := 42)
  let replayed := (SysState.init Bank2 {}).run {} run.events.toList
  [ ("bank, reliable links: all properties hold, 293 states",
      reliable.ok && reliable.complete && reliable.states == 293),
    ("bank, reliable links: both vacuity checks have witnesses",
      reliable.witnesses.length == 2),
    ("bank, lossy links: conservation violated by dropping a credit",
      match broken.failure with
      | some (.violated "money is conserved" t) =>
        t.steps.length == 4 && (match t.labels.getLast? with
          | some (.drop _) => true
          | _ => false)
      | _ => false),
    ("scheduler: a run ends quiescent with money conserved",
      run.quiescent && conserved run.final.state),
    ("scheduler: same seed, same run",
      run.events.size == again.events.size
        && run.final.state.equiv {} again.final.state),
    ("replay: the run's events lead to the same state through SysState.run",
      match replayed with
      | some c => c.equiv {} run.final.state
      | none => false) ]

end Tests.Bank
