import Ledger

/-!
# Strangers are reclaimed

A log-in for a name nobody has signed up leaves `user n` vacant, the state a start gives it
(`Actor.fresh`), so the kernel releases it once it has answered
(`docs/decisions/D51-release-actors-at-rest.md`). Without that, a stranger guessing names grows
the kernel by an actor a guess. Checked when this file is built, with names and credentials
that are numbers; the gate in front of the deployed system passes the declaration on.
-/

namespace Ledger.Release

open Lanes

abbrev Sys := system Nat Nat { admin := 0 }

def guesses : Nat := 20000

/-- `guesses` log-ins, each for a name nobody has, and how many were refused. -/
def guessed : Kernel Sys × Nat :=
  (List.range guesses).foldl (init := ((Kernel.boot Sys).1, 0)) fun (k, refused) n =>
    match k.exec [.input (.logIn n (n + 1) 1 0), .batch 8] with
    | { kernel, outputs, .. } => (kernel, refused + outputs.countP (·.reply == .refused))

/-- Every guess is refused, and the kernel holds only the ledger. -/
def reclaimed : Bool := guessed.2 == guesses && guessed.1.cells.size == 1

#guard reclaimed

def answers (k : Kernel Sys) (requests : List (Request Nat Nat)) : List (Reply Nat) :=
  ((k.exec (requests.map (Kernel.Op.input (σ := sig Nat Nat)) ++ [.batch 40])).outputs).map (·.reply)

/-- A user who signed up is kept; a stranger asked again is refused as before; a released name
is still free to sign up. -/
def kept : Bool :=
  let k := (guessed.1.exec [.input (.signUp guesses 7 1), .input (.logIn (guesses + 1) 7 2 0),
    .batch 40]).kernel
  k.cells.size == 2
    && answers k [.logIn (guesses + 2) 5 1 0, .signUp (guesses + 3) 6 1] == [.refused, .signedUp]

#guard kept

/-- The gate passes the declaration on, so the deployed system releases strangers too. -/
example (config : Config Web.Name) (bridge : Http.Bridge (sig Web.Name Web.Digest))
    (gate : Http.GateConfig) (n : Web.Name) :
    ((Http.served (Web.Sys config) bridge gate).actor (.inr (.user n))).fresh none = true :=
  rfl

end Ledger.Release
