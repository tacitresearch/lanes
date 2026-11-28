/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Db.Txn

/-!
# Jobs: work in a table, due at a time

A job is a row of a table (`Queue`): its work, the time it is due, a key its requester chose,
and how far it has got. Everything that must outlive the process is in the row, so a restart
loses nothing (`docs/decisions/D110-volatile-actors.md`). The outbox is a jobs table whose jobs
are effects (an HTTP call, an email, a payment), written in the transaction that causes them and
due at once (`Lanes/Db/Outbox.lean`); a schedule is a job that runs again `every_ms` after each
success.

The transactions:

- `enqueue` adds a job in the requester's transaction. A key already in the table makes it a
  no-op, which answers the job that holds it: a request that enqueues twice enqueues once.
- `claim` takes the jobs due by `now_ms`, earliest first, at most `limit`: each is leased, so
  that it is due again `lease_ms` later if no answer comes, and its attempts are counted. A job
  whose attempts are all used is failed instead of being taken again.
- `finish` records the answer to one attempt: done, failed, or due again after a backoff. The
  attempt is named by the job's `lease`, which every claim and every finish changes, so an answer
  to an older attempt, or a second answer to this one, changes nothing.
- `cancel` stops a job that has not ended.

Each decision is a pure function of the job (`Config.claimed`, `Config.finished`); the
transactions only read and write rows, and the worker (`Lanes/Db/Worker.lean`) only carries
them. Every limit is in `Config` (rule 2.6).
-/

@[expose] public section

namespace Lanes.Db.Jobs

inductive Status where
  | pending
  | done
  | failed
  | cancelled
  deriving DecidableEq, Repr, Hashable

def Status.code : Status → Int64
  | .pending => 0
  | .done => 1
  | .failed => 2
  | .cancelled => 3

def Status.ofCode (i : Int64) : Option Status :=
  if i = 0 then some .pending else if i = 1 then some .done
  else if i = 2 then some .failed else if i = 3 then some .cancelled else none

theorem Status.ofCode_code (s : Status) : Status.ofCode s.code = some s := by
  cases s <;> decide

/-- How a job's work is written in its row, and read back. -/
structure Payload (W : Type) where
  encode : W → String
  decode : String → Option W
  decode_encode : ∀ w, decode (encode w) = some w

namespace Payload

def text : Payload String := { encode := id, decode := some, decode_encode := fun _ => rfl }

def int64 : Payload Int64 where
  encode i := toString i.toInt
  decode s := s.toInt?.map Int64.ofInt
  decode_encode i := by simp only [Int.toString_eq_repr, Int.toInt?_repr, Option.map_some, Int64.ofInt_toInt]

/-- Another type, through a map each way that gets each value back. -/
def iso {A B : Type} (p : Payload A) (to : B → A) (of : A → B) (h : ∀ b, of (to b) = b) : Payload B where
  encode b := p.encode (to b)
  decode s := (p.decode s).map of
  decode_encode b := by simp [p.decode_encode, h]

/-- Two values, the first written without `:`, then `:`, then the second. -/
def pair {A B : Type} (p : Payload A) (q : Payload B) (hp : ∀ a, ∀ c ∈ (p.encode a).toList, c ≠ ':') :
    Payload (A × B) where
  encode ab := p.encode ab.1 ++ ":" ++ q.encode ab.2
  decode s :=
    match s.toList.dropWhile (· != ':') with
    | ':' :: rest => do
      let a ← p.decode (String.ofList (s.toList.takeWhile (· != ':')))
      let b ← q.decode (String.ofList rest)
      pure (a, b)
    | _ => none
  decode_encode ab := by
    obtain ⟨a, b⟩ := ab
    have hl : (p.encode a ++ ":" ++ q.encode b).toList = (p.encode a).toList ++ ':' :: (q.encode b).toList := by
      simp
    have hpos : ∀ c ∈ (p.encode a).toList, (c != ':') = true := fun c hc => by simpa using hp a c hc
    simp only [hl, List.dropWhile_append_of_pos hpos, List.takeWhile_append_of_pos hpos]
    simp [List.dropWhile, List.takeWhile, String.ofList_toList, p.decode_encode, q.decode_encode]

theorem nat_colon (n : Nat) : ∀ c ∈ n.repr.toList, c ≠ ':' := by
  intro c hc heq
  subst heq
  rw [Nat.toList_repr] at hc
  have := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hc
  revert this; decide

theorem int64_colon (i : Int64) : ∀ c ∈ (int64.encode i).toList, c ≠ ':' := by
  intro c hc
  simp only [int64, Int.toString_eq_repr, Int.repr_eq_ite] at hc
  split at hc
  · exact nat_colon _ c hc
  · simp only [String.toList_append, List.mem_append] at hc
    rcases hc with hc | hc
    · simp at hc; subst hc; decide
    · exact nat_colon _ c hc

end Payload

structure Job (W : Type) where
  id : Int64
  /-- The requester's name for the job, unique in its table. -/
  key : String
  work : W
  due_ms : Int64
  status : Status
  /-- The attempts of this run: claims since it was enqueued or last succeeded. -/
  attempts : Int64
  /-- Names the current attempt: every claim and every finish changes it. -/
  lease : Int64
  /-- 0 for a job that runs once; otherwise it runs again this long after each success. -/
  every_ms : Int64 := 0
  /-- Why the last attempt failed, if it did. -/
  note : String := ""
  deriving DecidableEq, Repr, Hashable

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  /-- The most jobs one claim takes. -/
  batch_max : Nat := 16
  /-- Attempts of one run, at least one. -/
  attempts_max : Nat := 5
  /-- How long a claimed job is held: it is due again after this if no answer is recorded.
  Longer than an attempt's deadline (`Worker.Config.attempt_ms`). -/
  lease_ms : Nat := 60000
  /-- The wait after the first failed attempt; it doubles after each, up to `backoff_max_ms`. -/
  backoff_ms : Nat := 1000
  backoff_max_ms : Nat := 60000
  /-- The longest note kept, in characters. -/
  note_max : Nat := 200
  deriving Repr

/-- What the worker made of an attempt's answer. -/
inductive Verdict where
  | ok
  /-- A failure worth another attempt, or no answer. -/
  | retry (why : String)
  /-- A failure no attempt will mend. -/
  | fatal (why : String)
  deriving DecidableEq, Repr, Hashable

namespace Config

variable (cfg : Config)

def backoff (attempts : Int64) : Int64 :=
  Int64.ofNat (min cfg.backoff_max_ms (cfg.backoff_ms * 2 ^ (attempts.toInt.toNat - 1)))

/-- A note, without `NUL` (which text may not hold) and within `note_max`. -/
def clean (why : String) : String :=
  String.ofList ((why.toList.filter (· != '\x00')).take cfg.note_max)

/-- Whether the job's attempts of this run are all used. -/
def spent {W : Type} (j : Job W) : Bool := decide (cfg.attempts_max ≤ j.attempts.toInt.toNat)

/-- A due job, as a claim at `now_ms` leaves it: leased for another attempt, or failed if its
attempts are spent (the last one's lease ran out with no answer recorded). -/
def claimed {W : Type} (now_ms : Int64) (j : Job W) : Job W :=
  if cfg.spent j then { j with status := .failed, lease := j.lease + 1, note := "no answer to the last attempt" }
  else { j with attempts := j.attempts + 1, lease := j.lease + 1, due_ms := now_ms + Int64.ofNat cfg.lease_ms }

/-- A leased job, as the answer to its attempt leaves it. -/
def finished {W : Type} (now_ms : Int64) (j : Job W) : Verdict → Job W
  | .ok =>
    if 0 < j.every_ms then { j with lease := j.lease + 1, due_ms := now_ms + j.every_ms, attempts := 0, note := "" }
    else { j with lease := j.lease + 1, status := .done, note := "" }
  | .fatal why => { j with lease := j.lease + 1, status := .failed, note := cfg.clean why }
  | .retry why =>
    if cfg.spent j then { j with lease := j.lease + 1, status := .failed, note := cfg.clean why }
    else { j with lease := j.lease + 1, due_ms := now_ms + cfg.backoff j.attempts, note := cfg.clean why }

end Config

/-! ## The table -/

/-- A jobs table: its name, and how its work is written. -/
structure Queue (W : Type) where
  /-- A PostgreSQL identifier of at most 56 bytes, so that its indexes' names are too. -/
  name : String
  payload : Payload W

/-- The key is unique: a second job under one key is refused by the index itself. -/
def byKey : Index := { name := "by_key", columns := [1], unique := true }

/-- Pending jobs by the time they are due. -/
def byDue : Index := { name := "by_due", columns := [4, 3] }

def columns : List Column :=
  [{ name := "id", ty := .int }, { name := "key", ty := .text }, { name := "work", ty := .text },
   { name := "due_ms", ty := .int }, { name := "status", ty := .int }, { name := "attempts", ty := .int },
   { name := "lease", ty := .int }, { name := "every_ms", ty := .int }, { name := "note", ty := .text }]

namespace Queue

variable {W : Type} (q : Queue W)

def table : Table := { name := q.name, key := 1, columns, indexes := [byKey, byDue] }

def toRow (j : Job W) : Row :=
  [.int j.id, .text j.key, .text (q.payload.encode j.work), .int j.due_ms, .int j.status.code,
   .int j.attempts, .int j.lease, .int j.every_ms, .text j.note]

def ofRow : Row → Option (Job W)
  | [.int id, .text key, .text work, .int due_ms, .int status, .int attempts, .int lease,
     .int every_ms, .text note] => do
    some { id, key, work := ← q.payload.decode work, due_ms, status := ← Status.ofCode status,
           attempts, lease, every_ms, note }
  | _ => none

theorem ofRow_toRow (j : Job W) : q.ofRow (q.toRow j) = some j := by
  simp [ofRow, toRow, q.payload.decode_encode, Status.ofCode_code]

def rows : TableOf (Job W) where
  table := q.table
  toRow := q.toRow
  ofRow := q.ofRow
  ofRow_toRow := q.ofRow_toRow

/-- The pending jobs due by `now_ms`, earliest first, at most `limit`. -/
def due (now_ms : Int64) (limit : Nat) : Scan :=
  { table := q.table, index := some byDue, eq := [.int Status.pending.code],
    upper := some { value := .int now_ms }, limit }

/-- One more than the largest id, or 0. -/
def nextId : Txn Int64 := do
  match ← q.rows.scan { table := q.table, order := .desc, limit := 1 } with
  | j :: _ => pure (j.id + 1)
  | [] => pure 0

inductive Enqueued where
  | added (id : Int64)
  /-- A job holds the key already: nothing was added. -/
  | already (id : Int64)
  deriving DecidableEq, Repr, Hashable

/-- Add a job under `key`, due at `due_ms`, unless a job holds the key. -/
def enqueue (key : String) (work : W) (due_ms : Int64) (every_ms : Int64 := 0) : Txn Enqueued := do
  match ← q.rows.lookup byKey [.text key] 1 with
  | j :: _ => pure (.already j.id)
  | [] =>
    let id ← q.nextId
    let job : Job W := { id, key, work, due_ms, status := .pending, attempts := 0, lease := 0, every_ms }
    if ← q.rows.insert job then pure (.added id) else .abort "the next id is taken"

/-- Lease each job, and answer those leased for an attempt. -/
def claimAll (cfg : Config) (now_ms : Int64) : List (Job W) → Txn (List (Job W))
  | [] => pure []
  | j :: js => do
    let j' := cfg.claimed now_ms j
    let _ ← q.rows.update j'
    let rest ← claimAll cfg now_ms js
    pure (if j'.status = .pending then j' :: rest else rest)

def claim (cfg : Config) (now_ms : Int64) (limit : Nat) : Txn (List (Job W)) := do
  q.claimAll cfg now_ms (← q.rows.scan (q.due now_ms (min limit (min cfg.batch_max Scan.limit_max))))

/-- Record the answer to the attempt `lease` of job `id`: whether it was that job's current
attempt, and so counted. -/
def finish (cfg : Config) (id lease now_ms : Int64) (v : Verdict) : Txn Bool := do
  match ← q.rows.get [.int id] with
  | some j =>
    if j.status = .pending ∧ j.lease = lease then q.rows.update (cfg.finished now_ms j v)
    else pure false
  | none => pure false

/-- Stop the job under `key` if it has not ended: whether there was one. An attempt out when it
is cancelled may still take effect; its answer is not counted. -/
def cancel (key : String) : Txn Bool := do
  match ← q.rows.lookup byKey [.text key] 1 with
  | j :: _ =>
    if j.status = .pending then q.rows.update { j with status := .cancelled, lease := j.lease + 1 }
    else pure false
  | [] => pure false

/-- The job under `key`, if any. -/
def find (key : String) : Txn (Option (Job W)) := do
  return (← q.rows.lookup byKey [.text key] 1).head?

end Queue

/-! ## The worker's transactions -/

inductive Req where
  | claim (now_ms : Int64) (limit : Nat)
  | finish (id lease now_ms : Int64) (verdict : Verdict)
  deriving DecidableEq, Repr, Hashable

inductive Ans (W : Type) where
  | claimed (jobs : List (Job W))
  | finished (counted : Bool)
  deriving DecidableEq, Repr, Hashable

/-- The worker's requests, as transactions on the queue. -/
def Queue.handler {W : Type} (q : Queue W) (cfg : Config) : Handler Req (Ans W)
  | .claim now_ms limit => .claimed <$> q.claim cfg now_ms limit
  | .finish id lease now_ms v => .finished <$> q.finish cfg id lease now_ms v

/-- An application's handler and the worker's, on one database. -/
def beside {Q A R B : Type} (app : Handler Q A) (worker : Handler R B) : Handler (Q ⊕ R) (A ⊕ B)
  | .inl q => .inl <$> app q
  | .inr r => .inr <$> worker r

end Lanes.Db.Jobs
