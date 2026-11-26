/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Model checks of the jobs actor against a requester and a pool of workers that may answer an
attempt with success or a failure worth retrying, answer it after its deadline, or never; with
crashes of the actor and a link from outside that loses. Timers fire at any moment in the
model, so every race between a result, a deadline and a backoff is explored.
-/

namespace Tests.Jobs

open Lanes Lanes.Jobs

/-- Keys and work are numbers; a result is whether the attempt succeeded. -/
abbrev jobsSig := sig Nat Nat Bool

abbrev Active' := Active Nat Nat

instance : jobsSig.Inspect := {}

def policy (maxInFlight : Nat) : Config Bool :=
  { maxInFlight, maxAttempts := 2, retryable := (! ·) }

abbrev jobs (maxInFlight : Nat) : System jobsSig := system (policy maxInFlight)

instance (maxInFlight : Nat) : (jobs maxInFlight).Inspect := {}

/-- The requester: what it has still to submit, the answers it got, and every attempt it saw
dispatched. -/
structure Asker where
  toSubmit : List (Nat × Nat)
  answers : List (Nat × Outcome Bool)
  dispatched : List (Nat × Nat × Nat)
  deriving DecidableEq, Hashable

instance : BEq Asker := instBEqOfDecidableEq

def asker (submissions : List (Nat × Nat)) : Outside jobsSig Asker where
  init := { toSubmit := submissions, answers := [], dispatched := [] }
  allow d x :=
    match x with
    | .submit key job =>
      if (key, job) ∈ d.toSubmit then some { d with toSubmit := d.toSubmit.erase (key, job) }
      else none
    | .result .. => none
  observe d out :=
    match out with
    | .answer key outcome => { d with answers := (key, outcome) :: d.answers }
    | .dispatch key attempt job => { d with dispatched := (key, attempt, job) :: d.dispatched }

def world (submissions : List (Nat × Nat)) :=
  (asker submissions).both pool fun x => x matches .submit ..

abbrev JobsWorld (maxInFlight : Nat) := World (jobs maxInFlight) (Asker × List (Nat × Nat))

def samples (d : Asker × List (Nat × Nat)) : List (Input Nat Nat Bool) :=
  d.1.toSubmit.map (fun (key, job) => .submit key job)
    ++ d.2.flatMap fun (key, attempt) => [.result key attempt true, .result key attempt false]

def submissions : List (Nat × Nat) := [(0, 10), (1, 11)]

def answeredAtMostOnce (w : JobsWorld n) : Bool :=
  submissions.all fun (key, _) => w.driver.1.answers.countP (·.1 == key) ≤ 1

def dispatchesCarryTheirJob (w : JobsWorld n) : Bool :=
  w.driver.1.dispatched.all fun (key, attempt, job) =>
    submissions.lookup key == some job && 1 ≤ attempt && attempt ≤ 2

def withinSlots (w : JobsWorld n) : Bool :=
  (w.state.state ()).length ≤ max 1 n
    && ((w.state.state ()).map (·.key)).eraseDups.length == (w.state.state ()).length

def timersArmed (w : JobsWorld n) : Bool :=
  !w.state.up () || (w.state.state ()).all fun a =>
    (w.state.timers ()).contains (timer a)

/-- An ingredient of `Jobs.active_leaves` the checker can check: no delivery and no timer
arms again the timer an active job waits on. -/
def timersLeftAlone (w : JobsWorld n) : Bool :=
  let leaves (ev : Event jobsSig) : Bool :=
    (w.state.state ()).all fun a => !(w.state.arms ev).contains (.timeout () (timer a))
  !w.state.up () ||
    (w.state.net.all fun e => leaves (.deliver e))
      && (w.state.timers ()).all fun msg => leaves (.timeout () msg)

def answeredWith (p : Outcome Bool → Bool) (w : JobsWorld n) : Bool :=
  w.driver.1.answers.any (p ·.2)

def check (maxInFlight : Nat) (env : EnvModel jobsSig := {}) (maxCrashes : Nat := 0) :=
  Check.system (jobs maxInFlight)
    { env, driver := (world submissions).driver samples, maxCrashes }
    [ .always "no key is answered more than once" answeredAtMostOnce,
      .always "every attempt dispatched carries the job submitted under its key"
        dispatchesCarryTheirJob,
      .always "no more jobs are active than there are slots, and no key twice" withinSlots,
      .always "while the actor is up, the timer each active job waits on is armed" timersArmed,
      .always "no step arms again the timer an active job waits on" timersLeftAlone,
      .sometimes "a job succeeds on its second attempt" fun w =>
        answeredWith (· == .done true) w && w.driver.1.dispatched.any (·.2.1 == 2),
      .sometimes "a job fails after its last attempt" (answeredWith (· == .failed false)),
      .sometimes "a job times out" (answeredWith (· == .timedOut)),
      .sometimes "a job backs off while the actor is up" fun w =>
        w.state.up () && (w.state.state ()).any (·.phase == .backoff) ]
    { checkDeadlock := true
      terminal := fun w => w.driver.1.toSubmit.isEmpty
        && submissions.all fun (key, _) => w.driver.1.answers.any (·.1 == key) }

/-- The actor crashes and restarts, and results from outside may be lost. -/
def crashing : EnvModel jobsSig where
  link src _ := if src.isSome then .reliable else { ordered := false, lossy := true }
  mayCrash _ := true
  restarts _ := true

def tests : List (String × Bool) :=
  let two := check 2
  let one := check 1
  let faulty := check 2 crashing (maxCrashes := 1)
  [ ("jobs: every job is answered once, retried with its key and job, within the slots",
      two.ok && two.complete && two.witnesses.length == 5),
    ("jobs: beyond maxInFlight a job is refused, and still answered once",
      one.ok && one.complete
        && (Check.system (jobs 1) { driver := (world submissions).driver samples }
          [.sometimes "a job is refused" (answeredWith (· == .refused))]).witnesses.length == 1),
    ("jobs: the same when the actor crashes and restarts and results are lost",
      faulty.ok && faulty.complete && faulty.witnesses.length == 5) ]

end Tests.Jobs
