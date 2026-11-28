/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
A server that queues requests and serves the whole queue when its timer fires. One step of it is
as many steps of its service as requests were waiting, and a request lost on the way, or in a
crash, stays pending in the service for ever.

Checked here against its service on a small instance, with requests lost and reordered and a
crash, and with a request handed over twice, which breaks it. `Tests/BatchProofs.lean` proves
the first for every service.
-/

namespace Tests.Batch

open Lanes

inductive Msg (In : Type) where
  | request (x : In)
  | flush
  deriving DecidableEq, Repr, Hashable

abbrev sig (In Out : Type) [DecidableEq In] [DecidableEq Out] : Signature where
  Id := Unit
  Msg _ := Msg In
  In := In
  Out := Out

variable {In Out S : Type} [DecidableEq In] [DecidableEq Out]

def serve (svc : Service In Out S) (s : S) : List In → S × List Out
  | [] => (s, [])
  | x :: xs =>
    ((serve svc (svc.step s x).1 xs).1, (svc.step s x).2 ++ (serve svc (svc.step s x).1 xs).2)

/-- The value and the queue are kept across a crash of the actor. -/
def actor (svc : Service In Out S) : (sig In Out).Actor () (S × List In) where
  init := (svc.init, [])
  step s
    | .request x => ((s.1, s.2 ++ [x]), [])
    | .flush =>
      (((serve svc s.1 s.2).1, []),
        (serve svc s.1 s.2).2.map (Effect.emit (σ := sig In Out)) ++ [.after 10 .flush])
  recover s := (s, [.after 10 .flush])

abbrev system (svc : Service In Out S) : System (sig In Out) where
  State _ := S × List In
  actor _ := actor svc
  accept x := ⟨(), .request x⟩
  boot := [()]

/-- Each request is answered with the requests before it, so the order they took effect in
shows. -/
def history : Service (Fin 2) (List (Fin 2)) (List (Fin 2)) where
  init := []
  step s x := (s ++ [x], [s])

instance : (sig (Fin 2) (List (Fin 2))).Inspect := {}
instance : (system history).Inspect := {}

def faulty : EnvModel (sig (Fin 2) (List (Fin 2))) where
  link _ _ := { ordered := false, lossy := true }
  mayCrash _ := true
  restarts _ := true

def repeating : EnvModel (sig (Fin 2) (List (Fin 2))) where
  link _ _ := { duplicating := true }

def check (env : EnvModel (sig (Fin 2) (List (Fin 2)))) (maxCrashes : Nat) :=
  Check.system (system history)
    { env, driver := history.monitored (Driver.anyOrder [0, 1]), maxCrashes }
    [ Check.refines "every answer is allowed by the service",
      .sometimes "two requests are answered" fun w =>
        w.state.outbox.length == 2 ]

def tests : List (String × Bool) :=
  let lost := check faulty 1
  let twice := check repeating 0
  [ ("batch: with requests lost and reordered and a crash, the server refines its service",
      lost.ok),
    ("batch: the check is not vacuous: two requests are answered",
      lost.witnesses.length == 1),
    ("batch: a request handed over twice breaks refinement",
      match twice.failure with
      | some (.violated "every answer is allowed by the service" _) => true
      | _ => false) ]

end Tests.Batch
