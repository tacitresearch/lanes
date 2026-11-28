/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Model checks of the scheduler against a requester that schedules, schedules again and cancels,
and a service that answers an attempt with success or failure, `unknown`, late or never; with
crashes of the scheduler and links from outside that reorder. Timers fire at any moment in the
model, so every race between an answer, the end of an attempt's wait and a run time is explored.
What is checked of each attempt is what the requester sees: its stamp against the time it asked
for and the backoff, the number of attempts, and the attempts out at the service.

A scheduler that dispatches again, at a start, the attempt it had out at a crash, without
waiting for its end, has two attempts of an id out at once, and the checker finds it.
-/

namespace Tests.Schedule

open Lanes Lanes.Schedule

/-- Ids and payloads are numbers; an answer is whether the call succeeded. -/
abbrev schedSig := sig Nat Nat Bool

instance : schedSig.Inspect := {}

def retry : Retry := { maxAttempts := 2, deadline_ms := 1, base_ms := 2, cap_ms := 3, jitter_ms := 1 }

def config : Config Nat Nat Bool :=
  { maxJobs := 2, maxPayload := 9, size := id, maxAttempts := 3, grace_ms := 1, ok := id
    jitter := fun key n => key + n }

abbrev sched := system config

instance : sched.Inspect := {}

/-- The requester: what it has still to send, what it sent, the answers and notices it got, and
the attempts it saw: their ids, numbers and stamps. -/
structure Requester where
  toSend : List (Input Nat Nat Bool)
  sent : List (Input Nat Nat Bool) := []
  answers : List (Nat × Outcome Nat Bool) := []
  notices : List Nat := []
  starts : List (Nat × Nat × Nat) := []

instance : BEq Requester where
  beq a b := a.toSend == b.toSend && sameBag a.sent b.sent && sameBag a.answers b.answers
    && sameBag a.notices b.notices && sameBag a.starts b.starts

instance : Hashable Requester where
  hash d := mixHash (hash d.toSend) (mixHash (bagHash d.sent)
    (mixHash (bagHash d.answers) (mixHash (bagHash d.notices) (bagHash d.starts))))

/-- The time the requester asked a job to be run at, by its scheduling of the id. -/
def askedAt (sent : List (Input Nat Nat Bool)) (key : Nat) : Option Nat :=
  sent.findSome? fun
    | .schedule _ spec => if spec.key == key then some spec.at_ms else none
    | _ => none

def requester (toSend : List (Input Nat Nat Bool)) : Outside schedSig Requester where
  init := { toSend }
  allow d x :=
    match x with
    | .reply .. => none
    | x => if x ∈ d.toSend then some { d with toSend := d.toSend.erase x, sent := x :: d.sent }
      else none
  observe d out :=
    match out with
    | .answer key o => { d with answers := (key, o) :: d.answers }
    | .notice key _ _ => { d with notices := key :: d.notices }
    | .call a => { d with starts := (a.key, a.attempt, a.start_ms) :: d.starts }
    | .abandon .. => d

def world (toSend : List (Input Nat Nat Bool)) :=
  (requester toSend).both callee fun x => !(x matches .reply ..)

abbrev SchedWorld (sys : System schedSig) := World sys (Requester × Callee Nat)

def samples (d : Requester × Callee Nat) : List (Input Nat Nat Bool) :=
  d.1.toSend ++ d.2.out.flatMap fun (key, attempt) =>
    [.reply key attempt (.answer true), .reply key attempt (.answer false),
      .reply key attempt .unknown]

variable {sys : System schedSig}

/-- (i) No attempt starts before the time asked for, the first, or before the backoff after the
start of the attempt before it, a later one. Attempts are handed over in any order, so those
not yet handed over are counted too. -/
def neverEarly (w : SchedWorld sys) : Bool :=
  let all := w.driver.1.starts ++ w.state.outbox.filterMap fun
    | .call a => some (a.key, a.attempt, a.start_ms)
    | _ => none
  all.all fun (key, n, start) =>
    if n ≤ 1 then (askedAt w.driver.1.sent key).all (· ≤ start)
    else all.any fun (key', n', start') =>
      key' == key && n' + 1 == n && start' + config.backoff retry key (n - 1) ≤ start

/-- (ii) No id is called more often than `max 1 maxAttempts` times for each scheduling sent. -/
def attemptsBounded (w : SchedWorld sys) : Bool :=
  (List.range 4).all fun key =>
    w.driver.1.starts.countP (·.1 == key) ≤ 3 * w.driver.1.sent.countP fun
      | .schedule _ spec => spec.key == key
      | _ => false

/-- (iv) At most one attempt of each id is out at the service: called, not answered, and not
abandoned, an abandon still on its way included. -/
def oneOut (w : SchedWorld sys) : Bool :=
  (List.range 4).all fun key =>
    let out := w.driver.2.out.filter (·.1 == key)
    (out.filter fun (k, n) => !w.state.outbox.contains (.abandon k n)).length ≤ 1

def withinJobs (w : SchedWorld sched) : Bool :=
  (w.state.state ()).jobs.length ≤ config.maxJobs
    && ((w.state.state ()).jobs.map (·.key)).eraseDups.length == (w.state.state ()).jobs.length

def timersArmed (w : SchedWorld sched) : Bool :=
  !w.state.up () || (w.state.state ()).jobs.all fun j => (w.state.timers ()).contains (timer j)

def answered (p : Outcome Nat Bool → Bool) (w : SchedWorld sys) : Bool :=
  w.driver.1.answers.any (p ·.2)

def safety : List (Check.Property (SchedWorld sys)) :=
  [ .always "no attempt starts before its time" neverEarly,
    .always "no id is called more than maxAttempts times a scheduling" attemptsBounded,
    .always "at most one attempt of an id is out at once" oneOut ]

def call (key payload at_ms : Nat) : Input Nat Nat Bool :=
  .schedule 0 ⟨key, payload, .call retry, at_ms⟩

/-- A call that may need a retry, and a notice once. -/
def mixed : List (Input Nat Nat Bool) :=
  [call 0 5 2, .schedule 0 ⟨1, 6, .once, 1⟩]

/-- An id scheduled twice, a payload too large, and three jobs for two slots. -/
def crowded : List (Input Nat Nat Bool) :=
  [call 3 10 0, .schedule 0 ⟨0, 1, .once, 0⟩, .schedule 0 ⟨0, 1, .once, 0⟩,
    .schedule 0 ⟨1, 1, .once, 0⟩, .schedule 0 ⟨2, 1, .once, 0⟩]

def check (toSend : List (Input Nat Nat Bool)) (env : EnvModel schedSig := {})
    (maxCrashes : Nat := 0) (more : List (Check.Property (SchedWorld sched)) := []) :=
  Check.system sched { env, driver := (world toSend).driver samples, maxCrashes }
    (safety ++ [
      .always "no more jobs are held than maxJobs, and no id twice" withinJobs,
      .always "while the scheduler is up, the timer each job waits on is armed" timersArmed ]
      ++ more)
    { checkDeadlock := maxCrashes == 0
      terminal := fun w => w.driver.1.toSend.isEmpty && (w.state.state ()).jobs.isEmpty }

def mixedWitnesses : List (Check.Property (SchedWorld sched)) :=
  [ .sometimes "a call succeeds on its second attempt" fun w =>
      answered (· matches .succeeded true) w && w.driver.1.starts.any (·.2.1 == 2),
    .sometimes "a call gives up: the dead letter" (answered (· matches .failed 5 2 _)),
    .sometimes "a job runs once at its time" fun w => w.driver.1.notices.contains 1,
    .sometimes "an attempt is abandoned and retried" fun w =>
      w.state.outbox.any (· matches .abandon _ 1) ]

/-- The scheduler crashes and restarts, and what arrives from outside is reordered. A crash
loses the timers, and the start arms them again; with crashes only safety is checked, since
liveness is stated of runs in which the scheduler does not crash. -/
def crashing : EnvModel schedSig where
  link _ _ := .unordered
  mayCrash _ := true
  restarts _ := true

/-- A cancel while an attempt is out waits for its end. -/
def cancelling : List (Input Nat Nat Bool) := [call 0 5 0, .cancel 0]

/-- A sweep every four milliseconds, cancelled. Time grows with each notice, so the check is cut
off at a time. -/
def sweeping : List (Input Nat Nat Bool) := [.schedule 0 ⟨3, 7, .every 4, 0⟩, .cancel 3]

def checkSweep (_ : Unit) :=
  Check.system sched { driver := (world sweeping).driver samples }
    (safety ++ [
      .always "while the scheduler is up, the timer each job waits on is armed" timersArmed,
      .sometimes "a sweep is noticed three times" fun w => w.driver.1.notices.countP (· == 3) ≥ 3,
      .sometimes "a sweep is cancelled" (answered (· == .cancelled)) ])
    { constraint := fun w => (w.state.state ()).now_ms ≤ 12 }

/-! The seeded bug: a start that dispatches again the attempt out at a crash. -/

/-- At a start, every attempt out is started again at once, as the next attempt. -/
def hastyRecover (s : State Nat Nat) : State Nat Nat × List (Eff Nat Nat Bool) :=
  let bump (j : Job Nat Nat) : Job Nat Nat :=
    if j.phase = .running then { j with attempt := j.attempt + 1 } else j
  let s' : State Nat Nat := ⟨s.now_ms, s.jobs.map bump⟩
  (s', s.jobs.flatMap fun j =>
    if j.phase = .running then
      [.emit (.call ⟨j.key, j.attempt + 1, s.now_ms, retry.deadline_ms, j.payload⟩),
        .after (config.wait retry) (.expire j.key)]
    else [rearm s j])

abbrev hasty : System schedSig :=
  { sched with actor := fun _ => { actor config with recover := hastyRecover } }

instance : hasty.Inspect := {}

def checkHasty (_ : Unit) :=
  Check.system hasty { env := crashing, driver := (world [call 0 5 0]).driver samples, maxCrashes := 1 }
    [.always "at most one attempt of an id is out at once" oneOut]

def cancelWitness : List (Check.Property (SchedWorld sched)) :=
  [ .sometimes "a job cancelled while its attempt is out ends when the attempt does" fun w =>
      answered (· == .cancelled) w && !w.driver.1.starts.isEmpty ]

def crowdedWitnesses : List (Check.Property (SchedWorld sched)) :=
  [ .sometimes "an id scheduled twice is one job" (answered (· == .already)),
    .sometimes "a payload too large is refused" (answered (· == .refused .tooLarge)),
    .sometimes "a job is refused when maxJobs are held" (answered (· == .refused .full)) ]

/-- The seeded bug, found: the number of steps to it. -/
def hastyFound (_ : Unit) : Option Nat :=
  match (checkHasty ()).failure with
  | some (.violated "at most one attempt of an id is out at once" t) => some t.steps.length
  | _ => none

/-- The jitter differs between ids and between attempts, and is the same at every replay. -/
def jitterSpreads : Bool :=
  hashJitter 0 1 != hashJitter 1 1 && hashJitter 0 1 != hashJitter 0 2
    && hashJitter (7 : Nat) 3 == hashJitter (7 : Nat) 3

def tests : List (String × Bool) :=
  ("schedule: the hashed jitter differs between ids and attempts, the same at every replay",
    jitterSpreads) ::
  let main := check mixed (more := mixedWitnesses)
  let crowd := check crowded (more := crowdedWitnesses)
  let cancel := check cancelling (more := cancelWitness)
  let faulty := check mixed crashing (maxCrashes := 1)
  let sweep := checkSweep ()
  [ (s!"schedule: no attempt early, at most maxAttempts, one out per id, retries, "
        ++ s!"dead letters ({main.states} states)",
      main.ok && main.witnesses.length == 4),
    (s!"schedule: an id scheduled twice is one job; a payload too large and a job beyond maxJobs "
        ++ s!"are refused ({crowd.states} states)",
      crowd.ok && crowd.witnesses.length == 3),
    (s!"schedule: a cancel while an attempt is out ends with it ({cancel.states} states)",
      cancel.ok && cancel.witnesses.length == 1),
    (s!"schedule: the same when the scheduler crashes and restarts and inputs are reordered "
        ++ s!"({faulty.states} states)",
      faulty.ok),
    (s!"schedule: a periodic sweep is noticed again and again until cancelled ({sweep.states} states)",
      sweep.ok && sweep.witnesses.length == 2),
    (s!"schedule: a start that dispatches the attempt out again has two out at once "
        ++ s!"(found in {(hastyFound ()).getD 0} steps)", (hastyFound ()).isSome) ]

end Tests.Schedule
