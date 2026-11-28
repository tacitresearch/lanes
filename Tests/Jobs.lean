/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.HttpClient

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

/-- The requester: what it has still to submit, the answers it got, whether an attempt it saw
dispatched carried other work than its key's or an attempt out of range, and whether one was
a retry. -/
structure Asker where
  toSubmit : List (Nat × Nat)
  answers : List (Nat × Outcome Bool)
  strayDispatch : Bool := false
  retried : Bool := false
  deriving DecidableEq, Hashable

instance : BEq Asker := instBEqOfDecidableEq

def asker (submissions : List (Nat × Nat)) : Outside jobsSig Asker where
  init := { toSubmit := submissions, answers := [] }
  allow d x :=
    match x with
    | .submit key job =>
      if (key, job) ∈ d.toSubmit then some { d with toSubmit := d.toSubmit.erase (key, job) }
      else none
    | .result .. => none
  observe d out :=
    match out with
    | .answer key outcome => { d with answers := (key, outcome) :: d.answers }
    | .dispatch key attempt job =>
      { d with
        strayDispatch := d.strayDispatch || submissions.lookup key != some job || attempt == 0
          || attempt > 2
        retried := d.retried || attempt == 2 }

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
  !w.driver.1.strayDispatch

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
        answeredWith (· == .done true) w && w.driver.1.retried,
      .sometimes "a job fails after its last attempt" (answeredWith (· == .failed false)),
      .sometimes "a job times out" (answeredWith (· == .timedOut)),
      .sometimes "a job backs off while the actor is up" fun w =>
        w.state.up () && (w.state.state ()).any (·.phase == .backoff) ]
    { checkDeadlock := maxCrashes == 0
      terminal := fun w => w.driver.1.toSubmit.isEmpty
        && submissions.all fun (key, _) => w.driver.1.answers.any (·.1 == key) }

/-- The actor crashes and restarts, and what arrives from outside is reordered. A result that
is lost is one the pool never gives, which the pool may always do. A crash loses what was
delivered to the actor and not yet handled, a submission among them, so with crashes only
safety is checked: liveness is stated of runs in which the actor does not crash. -/
def crashing : EnvModel jobsSig where
  link _ _ := .unordered
  mayCrash _ := true
  restarts _ := true

/-! Beside an application: an actor that asks for a job on each input and reports its answer. -/

inductive AppIn where
  | send (key job : Nat)
  | answered (key : Nat) (outcome : Outcome Bool)
  deriving DecidableEq, Repr, Hashable

inductive AppOut where
  | submit (key job : Nat)
  | reported (key : Nat) (outcome : Outcome Bool)
  deriving DecidableEq, Repr, Hashable

abbrev appSig : Signature where
  Id := Unit
  Msg _ := AppIn
  In := AppIn
  Out := AppOut

abbrev app : System appSig where
  State _ := Unit
  actor _ :=
    { init := ()
      step := fun _ msg =>
        ((), match msg with
          | .send key job => [.emit (.submit key job)]
          | .answered key outcome => [.emit (.reported key outcome)])
      recover := fun s => (s, []) }
  accept x := ⟨(), x⟩

def use : Use appSig Nat Nat Bool where
  submitted
    | .submit key job => some (key, job)
    | .reported .. => none
  answer := .answered

abbrev attached := attach app (policy 2) use

instance : appSig.Inspect := {}
instance : app.Inspect := {}
instance : (joinSig jobsSig appSig).Inspect := .join
instance : attached.Inspect := .join

/-- What is still to send, the attempts open, and the answers reported. -/
abbrev Beside := List (Nat × Nat) × List (Nat × Nat) × List (Nat × Outcome Bool)

def beside : Driver (joinSig jobsSig appSig) Beside where
  init := (submissions, [], [])
  inputs := fun (toSend, opened, reported) =>
    toSend.map (fun (key, job) => (.inr (.send key job), (toSend.erase (key, job), opened, reported)))
      ++ opened.flatMap fun (key, attempt) => [true, false].map fun ok =>
        (.inl (.result key attempt ok), (toSend, opened.erase (key, attempt), reported))
  observe := fun (toSend, opened, reported) out =>
    match out with
    | .inl (.dispatch key attempt _) => (toSend, (key, attempt) :: opened, reported)
    | .inr (.reported key outcome) => (toSend, opened, (key, outcome) :: reported)
    | _ => (toSend, opened, reported)

def checkBeside :=
  Check.system attached { driver := beside }
    [ .always "the application is told each answer once" fun w =>
        submissions.all fun (key, _) => w.driver.2.2.countP (·.1 == key) ≤ 1,
      .always "no more jobs are active than there are slots"
        fun w => (w.state.state (.inl ()) : List Active').length ≤ 2,
      .sometimes "the application is told of a success after a retry" fun w =>
        w.driver.2.2.any (·.2 == .done true)
          && (w.state.state (.inl ()) : List Active').isEmpty ]
    { checkDeadlock := true
      terminal := fun w => w.driver.1.isEmpty
        && submissions.all fun (key, _) => w.driver.2.2.any (·.1 == key) }

def withKey : Bool :=
  let request : Http.Request :=
    { method := .post, path := [], headers := [("idempotency-key", "x"), ("A", "1")] }
  let c : Http.Client.Call := { host := "127.0.0.1", port := 80, request }
  (withHeader "Idempotency-Key" "7" c).request.headers == [("Idempotency-Key", "7"), ("A", "1")]

def tests : List (String × Bool) :=
  ("jobs: the key goes with a call in place of any header of its name", withKey) ::
  let two := check 2
  let one := check 1
  let faulty := check 2 crashing (maxCrashes := 1)
  let besides := checkBeside
  [ (s!"jobs: every job is answered once, retried with its key and job, within the slots "
        ++ s!"({two.states} states)",
      two.ok && two.complete && two.witnesses.length == 4),
    (s!"jobs: beyond maxInFlight a job is refused, and still answered once ({one.states} states)",
      one.ok && one.complete
        && (Check.system (jobs 1) { driver := (world submissions).driver samples }
          [.sometimes "a job is refused" (answeredWith (· == .refused))]).witnesses.length == 1),
    (s!"jobs: the same when the actor crashes and restarts and results come late or never "
        ++ s!"({faulty.states} states)",
      faulty.ok && faulty.complete && faulty.witnesses.length == 4),
    (s!"jobs: beside an application, which is told each answer once ({besides.states} states)",
      besides.ok && besides.complete && besides.witnesses.length == 1) ]

/-! The pool, live: calls to a local service that fails twice before it succeeds, to a closed
port and to a service that never answers; and a pure worker. -/

open Std Std.Async Lanes.Http

/-- A service that answers `503` to the first two calls with a key and then says how many it
saw. -/
abbrev flakySig := Server.sig (ReqId × String) (ReqId × String × Nat)

def flaky : Service (ReqId × String) (ReqId × String × Nat) (List (String × Nat)) where
  init := []
  step seen := fun (id, key) =>
    let n := (seen.lookup key).getD 0 + 1
    ((key, n) :: seen.filter (·.1 != key), [(id, key, n)])

def flakyBridge : Bridge flakySig where
  decode id request :=
    .ok (id, ((request.headers.find? (·.1.toLower == "idempotency-key")).map (·.2)).getD "")
  encode := fun (id, key, n) =>
    some (id, if n ≤ 2 then .text "busy" 503 else .text s!"{key} after {n}")

abbrev callSig := sig Nat Client.Call (Option Response)

def calls (attempt_ms : Nat) : Config (Option Response) :=
  { maxInFlight := 4, maxAttempts := 3, attempt_ms, backoff_ms := 10, maxBackoff_ms := 40
    retryable := fun r => r.all (·.status ≥ 500) }

/-- Submits each call, waits for every answer or `patience_ms`, and returns the answers and the
events performed. -/
def runCalls (config : Config (Option Response)) (client : Client.Config)
    (submitted : List (Nat × Client.Call)) (patience_ms : Nat := 8000) :
    Async (List (Nat × Outcome (Option Response)) × List (Event callSig)) := do
  let answers ← IO.mkRef #[]
  let all ← IO.Promise.new
  let rt ← Runtime.startWith (system (K := Nat) (J := Client.Call) config) { record := true }
    fun rt _ out => do
      handler Port.alone (call client toString) (rt.tryInput ·) out
      if let .answer key outcome := out then
        if (← answers.modifyGet fun a => ((a.push (key, outcome)).size, a.push (key, outcome)))
            == submitted.length
        then all.resolve ()
  for (key, c) in submitted do rt.input (.submit key c)
  Async.race (discard <| await all.result?) (Async.sleep (.ofNat patience_ms))
  let events := (← rt.trace).toList
  rt.stop
  return ((← answers.get).toList, events)

def attempts (events : List (Event callSig)) (key : Nat) : List Nat :=
  events.filterMap fun
    | .output (.dispatch k attempt _) => if k == key then some attempt else none
    | _ => none

def bodyIs (outcome : Option (Outcome (Option Response))) (text : String) : Bool :=
  match outcome with
  | some (.done (some r)) => r.status == 200 && String.fromUTF8? r.body == some text
  | _ => false

def poolWorld : Outside callSig (Unit × List (Nat × Nat)) :=
  Outside.any.both pool fun x => x matches .submit ..

def live : Async (List (String × Bool)) := do
  let server ← serve (Server.system flaky) flakyBridge { port := 0 }
  let some tcpPort := server.port | return [("jobs: the test service reports its port", false)]
  let request : Request := { method := .post, path := ["send"] }
  let target : Client.Call := { host := "127.0.0.1", port := tcpPort, request }
  let (answers, events) ← runCalls (calls 2000) { timeout_ms := 2000 }
    [(7, target), (8, target), (9, { target with port := 1 })]
  server.stop
  let (silent, silentPort) ← Tests.HttpClient.holding .empty
  let start ← IO.monoMsNow
  let (late, lateEvents) ← runCalls (calls 150) { timeout_ms := 5000 }
    [(5, { target with port := silentPort })]
  let late_ms := (← IO.monoMsNow) - start
  silent.close
  let sums ← IO.mkRef #[]
  let done ← IO.Promise.new
  let rt ← Runtime.startWith (system (K := Nat) (J := Nat) (R := Nat) {}) {} fun rt _ out => do
    handler Port.alone (compute fun n => (List.range n).foldl (· + ·) 0) (rt.tryInput ·) out
      (prio := .dedicated)
    if let .answer key (.done r) := out then
      sums.modify (·.push (key, r))
      done.resolve ()
  rt.input (.submit 1 100000)
  Async.race (discard <| await done.result?) (Async.sleep 4000)
  rt.stop
  return [
    ("jobs: a call that fails twice succeeds on its third attempt, each with the job's key",
      bodyIs (answers.lookup 7) "7 after 3" && bodyIs (answers.lookup 8) "8 after 3"
        && attempts events 7 == [1, 2, 3] && attempts events 8 == [1, 2, 3]),
    ("jobs: a call that finds no service fails after its last attempt",
      answers.lookup 9 == some (.failed none) && attempts events 9 == [1, 2, 3]),
    (s!"jobs: a call that is never answered times out at its last deadline ({late_ms} ms)",
      late.lookup 5 == some .timedOut && attempts lateEvents 5 == [1, 2, 3]
        && 450 ≤ late_ms && late_ms < 4000),
    ("jobs: the real pool does only what its model allows",
      poolWorld.allows events && poolWorld.allows lateEvents),
    ("jobs: a pure worker computes off the shard and its result is the answer",
      (← sums.get).toList == [(1, 4999950000)]) ]

end Tests.Jobs
