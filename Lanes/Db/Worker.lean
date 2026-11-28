/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Jobs
public import Lanes.Db.Model
public import Lanes.Outside.Idempotent
public import Lanes.Core.Join

/-!
# The worker: jobs out of the table, through an adapter, and their answers back in

The worker is an actor whose step is pure: it decides, and the runtime and the adapters only
carry out what it emits (rule 3.9). At each `tick` it claims the jobs due (`Jobs.Req.claim`),
one claim at a time, with as many as it has room for. Each job a committed claim gives it is an
attempt: an output `run`, which the job's adapter performs (the HTTP client, SES, S3, a payment
service) with the job's id as the idempotency key, and whose answer, or `unknown`, comes back
as `ran`. The worker then records it (`Jobs.Req.finish`), with what `classify` makes of it.

It keeps nothing that a restart may not lose. A claim whose answer is lost, an attempt whose
answer never comes, a `finish` that fails: the lease of the job runs out, and the next claim
takes it again, for another attempt under the same key. That is why a job is performed at
least once, and why the key is what makes it take effect at most once.

An attempt is named by its job and lease (`runPort`): never by a counter the worker keeps,
which starts again at a restart, so that an answer to an attempt before a restart is never
taken for one after it.

`submit` stands, in the model, for the transactions of the application, which run on the same
database at any moment; in production nothing sends it. Theorems: `Lanes/Db/WorkerSound.lean`.
-/

@[expose] public section

namespace Lanes.Db.Worker

open Jobs

/-- Every limit is explicit (rule 2.6). -/
structure Config (R : Type) where
  jobs : Jobs.Config := {}
  /-- How long the adapter waits for an attempt's answer before it says `unknown`; less than
  `jobs.lease_ms`, so that a job is not due again while its attempt may still be answered. -/
  attempt_ms : Nat := 30000
  /-- A claim not answered in this long is given up on, and the next tick claims again. -/
  claim_ms : Nat := 30000
  /-- What an answer of the adapter means. -/
  classify : R → Verdict

/-- An attempt out: its job, its lease, and when it was claimed. -/
structure Attempt where
  id : Int64
  lease : Int64
  since_ms : Int64
  deriving DecidableEq, Repr, Hashable

structure State where
  /-- The latest time a tick gave. -/
  now_ms : Int64 := 0
  /-- The claim out, if any: its call and when it was sent. -/
  claim : Option (Nat × Int64) := none
  running : List Attempt := []
  nextCall : Nat := 0
  deriving DecidableEq, Repr, Hashable

inductive In (Q A W R : Type) where
  | tick (now_ms : Int64)
  | store (reply : Db.Reply (A ⊕ Ans W))
  | ran (id lease : Int64) (reply : Rpc.Reply R)
  /-- A transaction of the application, in the model only. -/
  | submit (q : Q)
  deriving DecidableEq, Repr, Hashable

inductive Out (Q W : Type) where
  | store (call : Db.Call (Q ⊕ Req))
  /-- An attempt at job `id` under lease `lease`, to be answered by `deadline_ms`. -/
  | run (id lease : Int64) (deadline_ms : Nat) (work : W)
  deriving DecidableEq, Repr, Hashable

variable {Q A W R : Type}

abbrev sig (Q A W R : Type) [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R] :
    Signature where
  Id := Unit
  Msg _ := In Q A W R
  In := In Q A W R
  Out := Out Q W

variable [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R]

abbrev Eff (Q A W R : Type) [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R] :=
  Effect (sig Q A W R) ()

variable (cfg : Config R)

def call (s : State) (r : Q ⊕ Req) : State × Eff Q A W R :=
  ({ s with nextCall := s.nextCall + 1 }, .emit (.store ⟨s.nextCall, r⟩))

/-- Attempts claimed longer ago than a lease are over: their jobs are due again. -/
def expire (s : State) (now_ms : Int64) : List Attempt :=
  s.running.filter fun a => now_ms < a.since_ms + Int64.ofNat cfg.jobs.lease_ms

def free (s : State) : Nat := cfg.jobs.batch_max - s.running.length

/-- Whether a claim is out, sent less than `claim_ms` ago. -/
def waiting (s : State) (now_ms : Int64) : Bool :=
  match s.claim with
  | some (_, sent) => now_ms < sent + Int64.ofNat cfg.claim_ms
  | none => false

def tick (s : State) (now_ms : Int64) : State × List (Eff Q A W R) :=
  let s := { s with now_ms, running := expire cfg s now_ms }
  if waiting cfg s now_ms || free cfg s = 0 then (s, [])
  else
    let (s', e) := call s (.inr (.claim now_ms (free cfg s)))
    ({ s' with claim := some (s.nextCall, now_ms) }, [e])

def attempt (j : Job W) : Eff Q A W R := .emit (.run j.id j.lease cfg.attempt_ms j.work)

/-- The answer to a call to the store: a committed claim starts an attempt at each job it
gives, as many as there is room for; any other answer needs nothing. -/
def stored (s : State) (r : Db.Reply (A ⊕ Ans W)) : State × List (Eff Q A W R) :=
  let s := if s.claim.map (·.1) = some r.id then { s with claim := none } else s
  match r.result with
  | .committed (.inr (.claimed jobs)) =>
    let taken := jobs.take (free cfg s)
    ({ s with running := s.running ++ taken.map fun j => ⟨j.id, j.lease, s.now_ms⟩ },
      taken.map (attempt cfg))
  | _ => (s, [])

/-- An attempt's answer, recorded. An answer to an attempt the worker does not hold (one from
before a restart) is recorded too: the lease says whether it still counts. -/
def ran (s : State) (id lease : Int64) (reply : Rpc.Reply R) : State × List (Eff Q A W R) :=
  let verdict := match reply with
    | .answer r => cfg.classify r
    | .unknown => .retry "no answer by the deadline"
  let s := { s with running := s.running.filter fun a => !(a.id = id ∧ a.lease = lease) }
  let (s, e) := call s (.inr (.finish id lease s.now_ms verdict))
  (s, [e])

def step (s : State) : In Q A W R → State × List (Eff Q A W R)
  | .tick now_ms => tick cfg s now_ms
  | .store r => stored cfg s r
  | .ran id lease reply => ran cfg s id lease reply
  | .submit q => let (s, e) := call s (.inl q); (s, [e])

def actor : (sig Q A W R).Actor () State where
  init := {}
  step := step cfg

abbrev system : System (sig Q A W R) where
  State _ := State
  actor _ := actor cfg
  accept x := ⟨(), x⟩
  boot := [()]

/-! ## The worker's two outsides -/

/-- How the store sees the worker: its calls, and the inputs that answer them. -/
def storePort : Db.Port (sig Q A W R) (Q ⊕ Req) (A ⊕ Ans W) where
  call
    | .store c => some c
    | _ => none
  reply r := .store r
  replied
    | .store r => some r
    | _ => none

/-- The number of an attempt, as the adapter's model counts calls: one for each job and lease,
whatever the worker's own counters were when it was made. -/
def attemptNumber (id lease : Int64) : Nat := id.toBitVec.toNat * 2 ^ 64 + lease.toBitVec.toNat

/-- How the adapter sees the worker: an attempt is a call under the job's id as its key. -/
def runPort {E : Type} : Rpc.Port (sig Q A W R) (Idempotent.Keyed Int64 W) R E where
  called
    | .run id lease deadline_ms work => some ⟨attemptNumber id lease, deadline_ms, ⟨some id, work⟩⟩
    | _ => none
  replied
    | .ran id lease reply => some (attemptNumber id lease, reply)
    | _ => none

/-- The inputs the clients of the worker's model send: ticks, and the application's
transactions. -/
def isClient : In Q A W R → Bool
  | .tick _ | .submit _ => true
  | _ => false

def isStored : In Q A W R → Bool
  | .ran .. => false
  | _ => true

/-- The worker's outsides: its clients (any clock, and the application), the store, with the
application's transactions beside the worker's, and the service the attempts go to. -/
def world {D S E : Type} (clients : Outside (sig Q A W R) D) (dbcfg : Db.Config)
    (h : Handler (Q ⊕ Req) (A ⊕ Ans W)) (start : Db) (svc : Rpc.Server S (Idempotent.Keyed Int64 W) R E) :
    Outside (sig Q A W R) ((D × Db.State (Q ⊕ Req) (A ⊕ Ans W)) × Rpc.State S) :=
  (clients.both (Db.outside dbcfg h start storePort) isClient).both (Rpc.outside runPort svc) isStored

end Lanes.Db.Worker
