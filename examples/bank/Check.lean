import Lanes
import Bank

/-!
Model checks of the bank on two accounts and three transfers in any order, run by `lake test`
(Lanes rule 5.1). Over reliable links money is conserved and no balance goes negative, and the
two `sometimes` properties show a credit arriving and a transfer refused (rule 5.3). Over links
that lose messages, the checker finds the dropped credit that breaks conservation. A seeded run
of the scheduler is the same run each time, and its events replay through `SysState.run`.
-/

open Lanes Bank

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
  [ ("reliable links: every property holds in every reachable state",
      reliable.ok && reliable.complete),
    ("reliable links: both sometimes properties have a witness", reliable.witnesses.length == 2),
    ("lossy links: dropping a credit breaks conservation",
      match broken.failure with
      | some (.violated "money is conserved" t) =>
        match t.labels.getLast? with
        | some (.drop _) => true
        | _ => false
      | _ => false),
    ("scheduler: a run ends quiescent with money conserved",
      run.quiescent && conserved run.final.state),
    ("scheduler: the same seed gives the same run",
      run.events.size == again.events.size && run.final.state.equiv {} again.final.state),
    ("replay: the run's events lead to the same state through SysState.run",
      match replayed with
      | some c => c.equiv {} run.final.state
      | none => false) ]

def main : IO UInt32 := do
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  return if failed.isEmpty then 0 else 1
