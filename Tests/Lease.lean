/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
A spec with a deadline: a lease is granted to one client at a time and is free again when it
lapses. The server's timer is the lapse, and the checker holds the server to it: a lease freed
before its timer fires is a second grant the spec refuses, and with the timer not named a
deadline the spec's lease never lapses.
-/

namespace Tests.Lease

open Lanes

inductive Msg where
  | acquire (client : Fin 2)
  | lapse
  deriving DecidableEq, Repr, Hashable

inductive Answer where
  | granted (client : Fin 2)
  | busy (client : Fin 2)
  deriving DecidableEq, Repr, Hashable

abbrev sig : Signature where
  Id := Unit
  Msg _ := Msg
  In := Fin 2
  Out := Answer

/-- The state is whether the lease is held. -/
def spec : Service (Fin 2) Answer Bool Unit where
  init := false
  step held c := (true, [if held then .busy c else .granted c])
  armed held _ := held
  fire _ _ := (false, [])

/-- `holds` false seeds a bug: the lease is free again as soon as it is granted. -/
abbrev server (holds : Bool := true) : System sig where
  State _ := Bool
  actor _ :=
    { init := false
      step := fun held msg =>
        match msg with
        | .acquire c =>
          if held then (true, [.emit (.busy c)])
          else (holds, [.emit (.granted c), .after 10 .lapse])
        | .lapse => (false, [])
      recover := fun held => (held, if held then [.after 10 .lapse] else []) }
  accept c := ⟨(), .acquire c⟩

def lapses : Deadlines sig Unit
  | _, .lapse => some ()
  | _, .acquire _ => none

instance : sig.Inspect := {}
instance (holds : Bool) : (server holds).Inspect := {}

def crashing : EnvModel sig where
  mayCrash _ := true

def check (holds : Bool) (deadlines : Deadlines sig Unit) (maxCrashes : Nat := 0) :=
  Check.system (server holds)
    { env := crashing, maxCrashes
      driver := spec.monitored (Driver.anyOrder [0, 1, 0]) deadlines }
    [ Check.refines "every answer is allowed by the lease",
      .sometimes "a lease lapses and is granted again" fun w =>
        (w.state.outbox.filter (· matches .granted _)).length == 2,
      .sometimes "a lease is held" fun w => w.state.outbox.any (· matches .busy _) ]

def violated {holds : Bool} {D : Type} (r : Check.Report (World (server holds) D) (Event sig)) :
    Bool :=
  match r.failure with
  | some (.violated "every answer is allowed by the lease" _) => true
  | _ => false

def tests : List (String × Bool) :=
  let honest := check true lapses 1
  [ ("lease: the server refines the lease, with the timer as its deadline and a crash",
      honest.ok && honest.complete),
    ("lease: the check is not vacuous: a lease lapses, and one is held",
      honest.witnesses.length == 2),
    ("lease: a lease freed before its timer fires is a grant the spec refuses",
      violated (check false lapses)),
    ("lease: with the timer not named a deadline, the spec's lease never lapses",
      violated (check true fun _ _ => none)),
    ("lease: a deadline that is not armed leaves the monitor no candidate",
      !(Check.Monitor.start spec |>.fire spec ()).ok) ]

end Tests.Lease
