/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Reminders.App

/-!
Model checks of the reminders (Lanes rule 5.1): the worker beside the store's model, whose
answers may be lost and whose lost `COMMIT`s may take effect late, with the reminders'
transactions (remind, cancel) running on the same database at any moment, and a notification
service that honours idempotency keys and answers each delivery `200`, `503` or `unknown`, or
never; the worker crashes and restarts. A reminder is delivered only once it is in every
database the store may hold, at most once at the service, a reminder sent was taken, and no
more than `maxReminders` wait.
-/

namespace Reminders.Check

open Lanes Lanes.Db Lanes.Db.Jobs

def config : Config :=
  { maxReminders := 1, maxText_bytes := 4
    jobs := { batch_max := 2, attempts_max := 2, lease_ms := 100, backoff_ms := 10 } }

abbrev wsig := Worker.sig Action Answer String Nat

instance : wsig.Inspect := {}

abbrev worker : System wsig := Worker.system (Q := Action) (A := Answer) (W := String) (config.worker 50)

instance : worker.Inspect := {}

/-- A service that may answer any delivery with any status. -/
def inner : Rpc.Server Unit String Nat Unit where
  init := ()
  receive _ _ := ()
  answer _ _ _ := some ()

abbrev Service := Rpc.State (Idempotent.State Int64 String Nat Unit)

/-- The clock and the browser: the times still to tick, the requests still to send, and the
deliveries the worker made, which the service may answer. -/
structure Driver where
  ticks : List Int64
  requests : List Action
  attempts : List (Int64 × Int64) := []
  deriving DecidableEq, Hashable

instance : BEq Driver := instBEqOfDecidableEq

def driver (ticks : List Int64) (requests : List Action) : Outside wsig Driver where
  init := { ticks, requests }
  allow d
    | .tick t => if d.ticks.head? = some t then some { d with ticks := d.ticks.tail } else none
    | .submit r => if r ∈ d.requests then some { d with requests := d.requests.erase r } else none
    | _ => none
  observe d
    | .run id lease _ _ => if (id, lease) ∈ d.attempts then d else { d with attempts := d.attempts ++ [(id, lease)] }
    | _ => d

abbrev D := (Driver × Db.State (Action ⊕ Req) (Answer ⊕ Ans String)) × Service

def start : Db := Db.empty schema

def world (ticks : List Int64) (requests : List Action) : Outside wsig D :=
  Worker.world (driver ticks requests) {} (store config) start (Idempotent.server inner fun _ => false)

def samples (d : D) : List (Worker.In Action Answer String Nat) :=
  d.1.1.ticks.head?.toList.map .tick ++ d.1.1.requests.map .submit
    ++ Db.samples (store config) Worker.storePort false false d.1.2
    ++ d.1.1.attempts.flatMap fun (id, lease) =>
      [.ran id lease (.answer 200), .ran id lease (.answer 503), .ran id lease .unknown]

abbrev W := Lanes.World worker D

def jobsOf (db : Db) : List (Job String) := (db.rows queue.name).filterMap queue.ofRow

def slots (w : W) : List (Idempotent.Slot Int64 String Nat) := w.driver.2.server.slots

def committedOnly (w : W) : Bool :=
  (slots w).all fun slot => w.driver.1.2.worlds.all fun world =>
    (jobsOf world.db).any fun j => some j.id == slot.key && j.work == slot.request

def onceEach (w : W) : Bool :=
  let keys := (slots w).filterMap (·.key)
  keys.eraseDups.length == keys.length

def sentWasTaken (w : W) : Bool :=
  w.driver.1.2.worlds.all fun world => (jobsOf world.db).all fun j =>
    j.status != .done || (slots w).any fun slot => slot.key == some j.id && slot.result == some 200

def bounded (w : W) : Bool :=
  w.driver.1.2.worlds.all fun world =>
    ((jobsOf world.db).filter (·.status == .pending)).length ≤ config.maxReminders

def always : List (Check.Property W) :=
  [ .always "a reminder is delivered only once every database the store may hold has it" committedOnly,
    .always "no reminder takes effect twice at the service" onceEach,
    .always "a reminder sent was taken by the service" sentWasTaken,
    .always "no more reminders wait than maxReminders" bounded ]

def check (ticks : List Int64) (requests : List Action) (witness : String) (p : W → Bool) :=
  Check.system worker { driver := (world ticks requests).driver samples }
    (always ++ [.sometimes witness p]) {}

/-- A reminder due at once, refused, and sent on a retry. -/
def delivered := check [0, 50] [.remind "tea" 0] "a reminder is sent after a retry" fun w =>
  (slots w).any (·.result == some 200) && w.driver.1.1.attempts.any (·.2 ≥ 3)

/-- A reminder due later, and cancelled; then a second, refused while one waits. -/
def cancelled := check [0] [.remind "tea" 1000, .cancel 0, .remind "jam" 1000]
  "a reminder is cancelled, and a second takes its place" fun w => w.driver.1.2.worlds.any fun world =>
    (jobsOf world.db).any (·.status == .cancelled) && (jobsOf world.db).any (·.status == .pending)

end Reminders.Check
