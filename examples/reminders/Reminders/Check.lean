/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Reminders.App

/-!
Model checks of the reminders with the scheduler beside them (Lanes rule 5.1): a browser that
asks for two reminders and cancels one, and a notification service that answers each delivery
`200`, `503` or `unknown`, late or never, every timer firing at any moment, the sweep among
them. A reminder the list calls sent was taken by the service; none is delivered more often
than its attempts allow; one is cancelled while its delivery is out; one is given up on.
-/

namespace Reminders.Check

open Lanes

abbrev fullSig := joinSig (Schedule.sig Key Task Answer) sig

instance : (Schedule.sig Key Task Answer).Inspect := {}
instance : sig.Inspect := {}
instance : fullSig.Inspect := .join

def config : Config :=
  { maxReminders := 2, maxText_bytes := 4
    retry := { maxAttempts := 2, deadline_ms := 1, base_ms := 1, cap_ms := 2 }
    sweep_ms := 4 }

abbrev checked := system config

instance : (reminders config).Inspect := {}
instance : (Schedule.system config.scheduler).Inspect := {}
instance : checked.Inspect := .join

/-- What the browser has still to send, the deliveries out at the service, the reminders it
took, and the deliveries it was sent, by reminder. -/
structure Seen where
  toSend : List In
  out : List (Key × Nat) := []
  took : List Nat := []
  delivered : List Nat := []
  deriving DecidableEq, Hashable

instance : BEq Seen := instBEqOfDecidableEq

def idOf : Key → Option Nat
  | .reminder id => some id
  | .sweep => none

def browser (toSend : List In) : Driver fullSig Seen where
  init := { toSend }
  inputs d :=
    d.toSend.map (fun x => (.inr x, { d with toSend := d.toSend.erase x }))
      ++ d.out.flatMap fun (key, attempt) =>
        let closed := { d with out := d.out.erase (key, attempt) }
        [(.inl (.reply key attempt (.answer 200)),
            { closed with took := (idOf key).toList ++ closed.took }),
          (.inl (.reply key attempt (.answer 503)), closed),
          (.inl (.reply key attempt .unknown), closed)]
  observe d
    | .inl (.call a) =>
      { d with out := (a.key, a.attempt) :: d.out, delivered := (idOf a.key).toList ++ d.delivered }
    | .inl (.abandon key attempt) => { d with out := d.out.erase (key, attempt) }
    | _ => d

abbrev W := World checked Seen

def app (w : W) : State := w.state.state (.inr ())

def jobs (w : W) : List (Schedule.Job Key Task) := (w.state.state (.inl ()) : Schedule.State Key Task).jobs

def stageOf (w : W) (id : Nat) : Option Stage :=
  ((app w).reminders.find? (·.id == id)).map (·.stage)

def sentWasTaken (w : W) : Bool :=
  (app w).reminders.all fun r => r.stage != .sent || w.driver.took.contains r.id

def attemptsBounded (w : W) : Bool :=
  (List.range 3).all fun id => w.driver.delivered.count id ≤ config.retry.maxAttempts

def bounded (w : W) : Bool :=
  (app w).reminders.length ≤ config.maxReminders && (jobs w).length ≤ config.maxReminders + 1

def check (toSend : List In) :=
  Check.system checked { driver := browser toSend }
    [ .always "a reminder the list calls sent was taken by the service" sentWasTaken,
      .always "no reminder is delivered more often than its attempts allow" attemptsBounded,
      .always "the reminders and the jobs stay within their bounds" bounded,
      .always "the sweep is one job, however often it is scheduled" fun w =>
        ((jobs w).filter (·.key == .sweep)).length ≤ 1,
      .sometimes "a reminder is sent after a retry" fun w =>
        stageOf w 0 == some .sent && w.driver.delivered.count 0 == 2,
      .sometimes "a reminder is given up on" fun w => stageOf w 0 == some .failed,
      .sometimes "a reminder is cancelled while its delivery is out" fun w =>
        stageOf w 0 == some .cancelled && w.driver.delivered.contains 0,
      .sometimes "the sweep takes a reminder that is over out of the list" fun w =>
        w.driver.toSend.isEmpty && (app w).reminders.isEmpty && w.driver.delivered.contains 0 ]
    { constraint := fun w => (w.state.state (.inl ()) : Schedule.State Key Task).now_ms ≤ 8 }

def scenario : List In := [.remind 0 0 "tea" 0, .cancel 1 0]

end Reminders.Check
