/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The jobs table and its worker (`Lanes/Db/Jobs.lean`, `Lanes/Db/Worker.lean`) without a server:
what the transactions do on small tables, and model checks of the worker beside the store's
model (`Lanes/Db/Model.lean`), whose answers may be lost and whose lost `COMMIT`s may take
effect late, and beside a service that honours idempotency keys (`Idempotent.server`), which
may answer an attempt, fail it, or not answer. The application's transactions (`submit`, an
`enqueue`) run on the same database at any moment, and the worker crashes and restarts.
-/

namespace Tests.Worker

open Lanes Lanes.Db Lanes.Db.Jobs

def payload : Payload String := { encode := id, decode := some, decode_encode := fun _ => rfl }

def queue : Queue String := { name := "outbox", payload }

def start : Db := Db.empty [queue.table]

def jobsOf (db : Db) : List (Job String) := (db.rows queue.name).filterMap queue.ofRow

/-! ## The transactions -/

def transactionTests : List (String × Bool) :=
  let cfg : Jobs.Config := { batch_max := 2, attempts_max := 2, lease_ms := 100 }
  let enqueued := (do
    let a ← queue.enqueue "a" "mail a" 10
    let b ← queue.enqueue "b" "mail b" 5
    let c ← queue.enqueue "a" "mail again" 1
    pure [a, b, c]).run start
  let claimed := (do
    let _ ← queue.enqueue "a" "mail a" 10
    let _ ← queue.enqueue "b" "mail b" 5
    let _ ← queue.enqueue "c" "mail c" 50
    let first ← queue.claim cfg 20 10
    let ok ← queue.finish cfg 1 1 21 .ok
    let again ← queue.finish cfg 1 1 21 .ok
    let retry ← queue.finish cfg 0 1 22 (.retry "busy")
    let stale ← queue.finish cfg 0 1 23 .ok
    pure (first.map (fun (j : Job String) => j.id), ok, again, retry, stale)).run start
  let spent := (do
    let _ ← queue.enqueue "a" "mail a" 0
    let one ← queue.claim cfg 0 10
    let two ← queue.claim cfg 1000 10
    let three ← queue.claim cfg 2000 10
    pure (one.length, two.length, three.length)).run start
  let recurring := (do
    let _ ← queue.enqueue "tick" "sweep" 0 (every_ms := 500)
    let _ ← queue.claim cfg 0 10
    let _ ← queue.finish cfg 0 1 7 .ok
    queue.find "tick").run start
  let cancelled := (do
    let _ ← queue.enqueue "a" "mail a" 0
    let first ← queue.claim cfg 0 10
    let c ← queue.cancel "a"
    let late ← queue.finish cfg 0 1 5 .ok
    let next ← queue.claim cfg 10000 10
    pure (first.length, c, late, next.length)).run start
  [ ("jobs: a key already held makes an enqueue a no-op",
      match enqueued with
      | .ok (r, db) => r == [.added 0, .added 1, .already 0] && (jobsOf db).length == 2
      | .error _ => false),
    ("jobs: a claim takes the jobs due, earliest first; only the current attempt's answer counts",
      match claimed with
      | .ok ((ids, ok, again, retry, stale), db) =>
        ids == [1, 0] && ok && !again && retry && !stale
          && (jobsOf db).map (fun (j : Job String) => (j.id, j.status)) == [(0, .pending), (1, .done), (2, .pending)]
      | .error _ => false),
    ("jobs: a job whose attempts are spent is failed by the next claim",
      match spent with
      | .ok ((1, 1, 0), db) => (jobsOf db).map (·.status) == [.failed]
      | _ => false),
    ("jobs: a recurring job is due again after its period, its attempts counted afresh",
      match recurring with
      | .ok (some j, _) => j.status == .pending && j.due_ms == 507 && j.attempts == 0
      | _ => false),
    ("jobs: a cancelled job is not claimed, and its attempt's answer is not counted",
      match cancelled with
      | .ok ((1, true, false, 0), _) => true
      | _ => false) ]

/-! ## The worker beside the store and a service -/

/-- The application enqueues a job under the key it is given, its work the key. -/
def app : Handler String Queue.Enqueued := fun key => queue.enqueue key key 0

def config : Worker.Config Bool :=
  { jobs := { batch_max := 2, attempts_max := 2, lease_ms := 100, backoff_ms := 10 }
    attempt_ms := 50, claim_ms := 50
    classify := fun ok => if ok then .ok else .retry "refused" }

abbrev wsig := Worker.sig String Queue.Enqueued String Bool

instance : wsig.Inspect := {}
abbrev worker : System wsig := Worker.system (Q := String) (A := Queue.Enqueued) (W := String) config

instance : worker.Inspect := {}

abbrev Handled := Handler (String ⊕ Req) (Queue.Enqueued ⊕ Ans String)

def handler : Handled := beside app (queue.handler config.jobs)

/-- A service that may answer any attempt: `true` if it took it. -/
def inner : Rpc.Server Unit String Bool Unit where
  init := ()
  receive _ _ := ()
  answer _ _ _ := some ()

abbrev Service := Rpc.State (Idempotent.State Int64 String Bool Unit)

def service : Outside wsig Service :=
  Rpc.outside Worker.runPort (Idempotent.server inner fun _ => false)

/-- The clock and the application: the times still to tick, the keys still to enqueue, and the
attempts the worker made, which the service may answer. -/
structure Driver where
  ticks : List Int64
  keys : List String
  attempts : List (Int64 × Int64) := []
  deriving DecidableEq, Hashable

instance : BEq Driver := instBEqOfDecidableEq

def driver (ticks : List Int64) (keys : List String) : Outside wsig Driver where
  init := { ticks, keys }
  allow d
    | .tick t => if d.ticks.head? = some t then some { d with ticks := d.ticks.tail } else none
    | .submit k => if k ∈ d.keys then some { d with keys := d.keys.erase k } else none
    | _ => none
  observe d
    | .run id lease _ _ => if (id, lease) ∈ d.attempts then d else { d with attempts := d.attempts ++ [(id, lease)] }
    | _ => d

abbrev D := (Driver × Db.State (String ⊕ Req) (Queue.Enqueued ⊕ Ans String)) × Service

def world (ticks : List Int64) (keys : List String) : Outside wsig D :=
  ((driver ticks keys).both (Db.outside {} handler start Worker.storePort)
    fun x => x matches .tick _ | .submit _).both service fun x => !(x matches .ran ..)

def samples (losses : Bool) (d : D) : List (Worker.In String Queue.Enqueued String Bool) :=
  d.1.1.ticks.head?.toList.map .tick ++ d.1.1.keys.map .submit
    ++ Db.samples handler Worker.storePort false losses d.1.2
    ++ d.1.1.attempts.flatMap fun (id, lease) =>
      [.ran id lease (.answer true), .ran id lease (.answer false), .ran id lease .unknown]

abbrev W := Lanes.World worker D

def slots (w : W) : List (Idempotent.Slot Int64 String Bool) := w.driver.2.server.slots

/-- Every attempt the service may have had is of a job, its work that job's, in every database
the store may hold: no effect is sent for a transaction that did not commit. -/
def committedOnly (w : W) : Bool :=
  (slots w).all fun slot => w.driver.1.2.worlds.all fun world =>
    (jobsOf world.db).any fun j => some j.id == slot.key && j.work == slot.request

/-- No two effects the service may have had are under one job's key. -/
def onceEach (w : W) : Bool :=
  let keys := (slots w).filterMap (·.key)
  keys.eraseDups.length == keys.length

/-- A job done in some database the store may hold had an attempt the service took. -/
def doneTaken (w : W) : Bool :=
  w.driver.1.2.worlds.all fun world => (jobsOf world.db).all fun j =>
    j.status != .done || (slots w).any fun slot => slot.key == some j.id && slot.result == some true

def bounded (w : W) : Bool := (w.state.state ()).running.length ≤ config.jobs.batch_max

def check (ticks : List Int64) (keys : List String) (losses : Bool) (maxCrashes : Nat) :=
  Check.system worker
    { env := { mayCrash := fun _ => true }, driver := (world ticks keys).driver (samples losses), maxCrashes }
    [ .always "every attempt is of a job of every database the store may hold" committedOnly,
      .always "no two effects under one job's key" onceEach,
      .always "a job done had an attempt the service took" doneTaken,
      .always "no more attempts out than a claim takes" bounded,
      .sometimes "a job is done" fun w => w.driver.1.2.worlds.any fun world =>
        (jobsOf world.db).any (·.status == .done),
      .sometimes "a job is attempted again under its key" fun w =>
        w.driver.1.1.attempts.any fun (_, lease) => lease ≥ 3 ]
    {}

def report (name : String) (r : Check.Report W (Event wsig)) : String :=
  match r.failure with
  | none => s!"{name}: PASS ({if r.ok then "complete" else "bounded"}, {r.states} states)"
  | some (.violated p t) =>
    s!"{name}: FAIL \"{p}\" after {t.steps.length} steps:\n" ++
      "\n".intercalate (t.steps.map fun (e, _) => "  " ++ Event.render e)
  | some (.unreached ps) => s!"{name}: FAIL never reached {ps}"
  | some (.deadlock _) => s!"{name}: FAIL deadlock"

end Tests.Worker
