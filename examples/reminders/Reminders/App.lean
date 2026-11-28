/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
# Reminders: work that is due later, through the scheduler

A reminder is a text and a time. The application keeps the reminders and leaves the rest to the
scheduler (`Lanes.Schedule`) beside it: each reminder is a job under its own id that, at its
time, calls a notification service with the text, retried with backoff until the service takes
it, the attempts run out or it is cancelled. A periodic job sweeps the reminders that are over
out of the list, which keeps it within `maxReminders`. The application schedules the sweep at
every start, and the scheduler, which holds jobs by id, makes the second and later of those one
job (`already`).
-/

namespace Reminders

open Lanes

lanes_data inductive Key where
  | reminder (id : Nat)
  | sweep
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Task where
  | deliver (id : Nat) (text : String)
  | sweep
  deriving DecidableEq, Repr, Hashable

/-- The service's answer to a delivery: its HTTP status. -/
abbrev Answer := Nat

lanes_data inductive Stage where
  | waiting
  | sent
  /-- Given up on: the scheduler's dead letter. -/
  | failed
  | cancelled
  deriving DecidableEq, Repr, Hashable

lanes_data structure Reminder where
  id : Nat
  text : String
  at_ms : Nat
  stage : Stage
  deriving DecidableEq, Repr, Hashable

/-- Durable: the reminders, and the next id. -/
lanes_data structure State where
  reminders : List Reminder := []
  nextId : Nat := 0
  deriving DecidableEq, Repr, Hashable

lanes_data inductive In where
  | remind (req : Nat) (now_ms : Nat) (text : String) (in_s : Nat)
  | cancel (req : Nat) (id : Nat)
  | list (req : Nat)
  | noticed (key : Key) (task : Task) (now_ms : Nat)
  | answered (key : Key) (outcome : Schedule.Outcome Task Answer)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Out where
  | reply (req : Nat) (reminders : List Reminder) (notice : String)
  | schedule (now_ms : Nat) (spec : Schedule.Spec Key Task)
  | cancel (key : Key)
  /-- A reminder given up on after `attempts`. -/
  | deadLetter (id : Nat) (text : String) (attempts : Nat)
  deriving DecidableEq, Repr, Hashable

def Task.size : Task → Nat
  | .deliver _ text => text.utf8ByteSize
  | .sweep => 0

/-- Every limit is explicit (Lanes rule 2.6). -/
structure Config where
  maxReminders : Nat := 100
  maxText_bytes : Nat := 280
  retry : Schedule.Retry :=
    { maxAttempts := 5, deadline_ms := 5000, base_ms := 1000, cap_ms := 60000, jitter_ms := 500 }
  sweep_ms : Nat := 60000

/-- The scheduler beside the reminders: one job for each reminder that waits, and the sweep. -/
def Config.scheduler (config : Config) : Schedule.Config Key Task Answer where
  maxJobs := config.maxReminders + 1
  maxPayload := config.maxText_bytes
  size := Task.size
  maxAttempts := config.retry.maxAttempts
  ok status := 200 ≤ status && status < 300
  jitter := Schedule.hashJitter

def sweepSpec (config : Config) : Schedule.Spec Key Task :=
  ⟨.sweep, .sweep, .every config.sweep_ms, 0⟩

abbrev sig : Signature where
  Id := Unit
  Msg _ := In
  In := In
  Out := Out

abbrev Eff := Effect sig ()

def setStage (s : State) (id : Nat) (stage : Stage) : State :=
  { s with reminders := s.reminders.map fun r => if r.id = id then { r with stage } else r }

def reply (s : State) (req : Nat) (notice : String) : Eff := .emit (.reply req s.reminders notice)

def remind (config : Config) (s : State) (req now_ms : Nat) (text : String) (in_s : Nat) :
    State × List Eff :=
  if text.isEmpty || config.maxText_bytes < text.utf8ByteSize then
    (s, [reply s req s!"A reminder is between 1 and {config.maxText_bytes} bytes."])
  else if config.maxReminders ≤ s.reminders.length then
    (s, [reply s req "Too many reminders: wait for the next sweep."])
  else
    let r : Reminder := ⟨s.nextId, text, now_ms + in_s * 1000, .waiting⟩
    let s' := { s with reminders := s.reminders ++ [r], nextId := s.nextId + 1 }
    (s', [.emit (.schedule now_ms ⟨.reminder r.id, .deliver r.id text, .call config.retry, r.at_ms⟩),
      reply s' req "Scheduled."])

def cancel (s : State) (req id : Nat) : State × List Eff :=
  if s.reminders.any fun r => r.id = id && r.stage = .waiting then
    (s, [.emit (.cancel (.reminder id)), reply s req "Cancelling."])
  else (s, [reply s req "No such reminder waits."])

/-- What the scheduler says of a reminder's job. -/
def answered (s : State) (id : Nat) : Schedule.Outcome Task Answer → State × List Eff
  | .succeeded _ => (setStage s id .sent, [])
  | .failed (.deliver _ text) attempts _ =>
    (setStage s id .failed, [.emit (.deadLetter id text attempts)])
  | .failed .sweep _ _ | .refused _ => (setStage s id .failed, [])
  | .cancelled => (setStage s id .cancelled, [])
  | .scheduled | .already => (s, [])

/-- The sweep: reminders that are over leave the list. -/
def sweep (s : State) : State :=
  { s with reminders := s.reminders.filter (·.stage = .waiting) }

def step (config : Config) (s : State) : In → State × List Eff
  | .remind req now_ms text in_s => remind config s req now_ms text in_s
  | .cancel req id => cancel s req id
  | .list req => (s, [reply s req ""])
  | .noticed .sweep _ _ => (sweep s, [])
  | .noticed (.reminder _) _ _ => (s, [])
  | .answered (.reminder id) outcome => answered s id outcome
  | .answered .sweep _ => (s, [])

def app (config : Config) : sig.Actor () State where
  init := {}
  step := step config
  recover s := (s, [.emit (.schedule 0 (sweepSpec config))])

abbrev reminders (config : Config) : System sig where
  State _ := State
  actor _ := app config
  accept x := ⟨(), x⟩
  boot := [()]

/-- How the reminders use the scheduler. -/
def use : Schedule.Use sig Key Task Answer where
  scheduled
    | .schedule now_ms spec => some (now_ms, spec)
    | _ => none
  cancelled
    | .cancel key => some key
    | _ => none
  notice := .noticed
  answer := .answered

/-- The reminders with the scheduler beside them. -/
abbrev system (config : Config) := Schedule.attach (reminders config) config.scheduler use

abbrev SchedIn := Schedule.Input Key Task Answer
abbrev SchedOut := Schedule.Output Key Task Answer

end Reminders
