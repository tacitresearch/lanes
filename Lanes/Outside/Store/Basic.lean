/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Basic

/-!
# A transactional store

What a transactional key-value store may do (`docs/decisions/D61-models-of-external-systems.md`),
with the isolation level a parameter: read committed or serializable. A system sends requests
(`Store.Request`): each names its transaction and carries one operation; the store answers each
(`Store.Reply`), or the answer is lost (`unknown`).

The model is an `Outside`: the checker explores a system against it, and a recorded run of a
real store is checked against it with `Outside.allows`. Its state is every database the answers
so far are consistent with (`Store.World`), as a checker of linearizability keeps them, which is
what lets it answer the fault that matters: a `COMMIT` whose answer is lost has an unknown
outcome, and its effect may appear at any later moment or never. A commit takes effect at some
moment between its request and its answer; a read at read committed sees the database at some
moment between its request and its answer.

- **Read committed.** A read sees the latest committed state, or the transaction's own write; a
  commit applies the transaction's writes on top of the latest state, the later commit winning,
  and fails if a key the transaction inserted has been inserted by another since.
- **Serializable.** The committed transactions are equivalent to running them one at a time, in
  an order in which a transaction comes after every one whose commit was answered before it
  began. A transaction's reads are all of one state in that order; a commit fails when no place
  in the order is consistent with what it read and with what the transactions after it read.

Every statement may also fail, as a deadlock, a serialization failure, a timeout or an
administrator may make it; a transaction that failed answers every later request `failed`, and
its commit does nothing. Each model allows more than PostgreSQL does at the same level: it is
an over-approximation, so that a store that behaves like PostgreSQL behaves like the model.

Bounds (rule 2.6): at most `txns_max` transactions open, `commits_max` commits outstanding or
lost, `history_max` transactions kept in the serial order while one is open. A run beyond them is
outside the model: a request that would exceed them is answered only `failed`.
-/

@[expose] public section

namespace Lanes.Store

inductive Isolation where
  | readCommitted
  | serializable
  deriving DecidableEq, Repr, Hashable

inductive Op (K V : Type) where
  | begin
  | read (key : K)
  /-- Every row, by key. -/
  | scan
  /-- Insert or replace. -/
  | write (key : K) (value : V)
  /-- Insert, failing if the key is there, as a unique constraint does. -/
  | insert (key : K) (value : V)
  /-- Insert under a key the store chooses, as a `serial` column does. -/
  | append (value : V)
  | delete (key : K)
  | commit
  | rollback
  deriving DecidableEq, Repr, Hashable

structure Request (K V : Type) where
  /-- The request's number, which its reply carries. -/
  id : Nat
  /-- Its transaction's number. A transaction is begun once and used for one request at a
  time; a retry is a new transaction. -/
  txn : Nat
  op : Op K V
  deriving DecidableEq, Repr, Hashable

inductive Answer (K V : Type) where
  /-- `begin`, `write`, `insert`, `delete`, `rollback`. -/
  | ok
  | value (value : Option V)
  | rows (rows : List (K × V))
  /-- The key `append` chose. -/
  | key (key : K)
  | committed
  /-- The request did not take effect, and its transaction is over. -/
  | failed
  /-- No answer came: whether the request took effect is unknown. -/
  | unknown
  deriving DecidableEq, Repr, Hashable

structure Reply (K V : Type) where
  id : Nat
  answer : Answer K V
  deriving DecidableEq, Repr, Hashable

/-- Which outputs are requests to the store and which inputs answer them. -/
structure Port (σ : Signature) (K V : Type) where
  request : σ.Out → Option (Request K V)
  reply : Reply K V → σ.In
  replied : σ.In → Option (Reply K V)

/-- Every limit is explicit (rule 2.6). -/
structure Config (K : Type) where
  isolation : Isolation
  /-- The key `append` is sampled with, from the keys there: one that is not among them. Any
  key not there is allowed. -/
  nextKey : List K → K
  txns_max : Nat := 4
  commits_max : Nat := 4
  history_max : Nat := 8

variable {K V : Type} [DecidableEq K] [DecidableEq V] [Ord K]

/-- A database: rows sorted by key, one per key. -/
abbrev Db (K V : Type) := List (K × V)

def Db.get (db : Db K V) (k : K) : Option V := (db.find? (·.1 == k)).map (·.2)

def Db.insertSorted : Db K V → K × V → Db K V
  | [], kv => [kv]
  | (k', v') :: rest, (k, v) =>
    if compare k k' == .lt then (k, v) :: (k', v') :: rest else (k', v') :: insertSorted rest (k, v)

def Db.set (db : Db K V) (k : K) : Option V → Db K V
  | none => db.filter (·.1 != k)
  | some v => Db.insertSorted (db.filter (·.1 != k)) (k, v)

/-- Writes, newest first, applied oldest first. -/
def Db.apply (db : Db K V) (writes : List (K × Option V)) : Db K V :=
  writes.foldr (fun (k, v) db => db.set k v) db

/-- What a transaction read from the store: one key, or every row but those of the keys it had
written itself, `own`, which it saw as it wrote them. -/
inductive Read (K V : Type) where
  | key (key : K) (value : Option V)
  | all (rows : Db K V) (own : List K)
  deriving DecidableEq, Repr, Hashable

def Read.holds (db : Db K V) : Read K V → Bool
  | .key k v => db.get k == v
  | .all rows own => db.filter (fun (k, _) => !own.contains k) == rows

structure Txn (K V : Type) where
  id : Nat
  /-- The transactions whose commits were answered before it began: it comes after them. -/
  after : List Nat := []
  reads : List (Read K V) := []
  /-- Newest first. -/
  writes : List (K × Option V) := []
  /-- Keys it inserted, which must still be free when it commits at read committed. -/
  inserted : List K := []
  failed : Bool := false
  deriving DecidableEq, Repr, Hashable

def Txn.own (t : Txn K V) (k : K) : Option (Option V) := (t.writes.find? (·.1 == k)).map (·.2)

/-- The rows a transaction sees: the store's, with its own writes over them. -/
def Txn.view (t : Txn K V) (db : Db K V) : Db K V := db.apply t.writes

/-- A commit requested, whose answer has not come or was lost. -/
structure Commit (K V : Type) where
  txn : Txn K V
  /-- The request's number; `none` once its answer was lost. -/
  request : Option Nat
  applied : Bool := false
  deriving DecidableEq, Repr, Hashable

/-- A request outstanding that is not a commit, with the answers it may get, at read
committed: one for each state the store has been in since it was sent. -/
structure Waiting (K V : Type) where
  request : Request K V
  seen : List (Answer K V) := []
  /-- Sent while another request of its transaction was outstanding, which the model does not
  cover: it may only fail. -/
  doomed : Bool := false
  deriving DecidableEq, Repr, Hashable

/-- One database the answers so far are consistent with. At serializable, `history` is the
order of the committed transactions after `base`, and `db` the state after them. -/
structure World (K V : Type) where
  db : Db K V := []
  base : Db K V := []
  history : List (Txn K V) := []
  txns : List (Txn K V) := []
  commits : List (Commit K V) := []
  waiting : List (Waiting K V) := []
  /-- Transactions whose commits were answered, which those begun after come after. -/
  acknowledged : List Nat := []
  deriving DecidableEq, Repr, Hashable

structure State (K V : Type) where
  worlds : List (World K V) := [{}]
  deriving DecidableEq, Repr, Hashable

variable (cfg : Config K)

namespace World

def txn? (w : World K V) (id : Nat) : Option (Txn K V) := w.txns.find? (·.id == id)

def setTxn (w : World K V) (t : Txn K V) : World K V :=
  { w with txns := w.txns.map fun u => if u.id == t.id then t else u }

def dropTxn (w : World K V) (id : Nat) : World K V :=
  { w with txns := w.txns.filter (·.id != id) }

/-! ## Serializable: places in the order -/

def stateAt (w : World K V) (p : Nat) : Db K V :=
  (w.history.take p).foldl (fun db t => db.apply t.writes) w.base

def readsAll (t : Txn K V) : Bool := t.reads.any fun | .all .. => true | _ => false

/-- Whether `t`, read at `stateAt p`, writes what a transaction after `p` read. -/
def clashes (t : Txn K V) (later : Txn K V) : Bool :=
  !t.writes.isEmpty && (readsAll later || t.writes.any fun (k, _) =>
    later.reads.any fun | .key k' _ => k' == k | _ => false)

/-- The places `t` may take in the order: after every transaction it must follow, at a state
consistent with what it read. -/
def places (w : World K V) (t : Txn K V) : List Nat :=
  (List.range (w.history.length + 1)).filter fun p =>
    (w.history.drop p).all (fun u => !t.after.contains u.id)
      && t.reads.all (·.holds (w.stateAt p))

/-- The places `t` may commit at: those, where no transaction after it read what it writes. -/
def commitPlaces (w : World K V) (t : Txn K V) : List Nat :=
  (w.places t).filter fun p => (w.history.drop p).all fun u => !clashes t u

def placeAt (w : World K V) (t : Txn K V) (p : Nat) : World K V :=
  let history := w.history.take p ++ [t] ++ w.history.drop p
  let w := { w with history }
  { w with db := w.stateAt history.length }

/-- With no transaction open and no commit outstanding, the order so far is one state. -/
def settle (w : World K V) : World K V :=
  if w.txns.isEmpty && w.commits.isEmpty then
    { w with base := w.db, history := [], acknowledged := [] }
  else w

/-! ## Answers -/

/-- What a request may be answered now in this world, other than `failed`: one answer for a
read at read committed, one for each place in the order at serializable. -/
def answersNow (w : World K V) (r : Request K V) : List (Answer K V) :=
  match w.txn? r.txn with
  | none => []
  | some t =>
    if t.failed then []
    else
      match r.op with
      | .read k =>
        match t.own k with
        | some v => [.value v]
        | none =>
          match cfg.isolation with
          | .readCommitted => [.value (w.db.get k)]
          | .serializable => (w.places t).map fun p => .value ((w.stateAt p).get k)
      | .scan =>
        match cfg.isolation with
        | .readCommitted => [.rows (t.view w.db)]
        | .serializable => (w.places t).map fun p => .rows (t.view (w.stateAt p))
      | .insert k _ =>
        match cfg.isolation with
        | .readCommitted => if ((t.view w.db).get k).isNone then [.ok] else []
        | .serializable =>
          if (w.places t).any fun p => ((t.view (w.stateAt p)).get k).isNone then [.ok] else []
      | .append _ => [.key (cfg.nextKey ((t.view w.db).map (·.1)))]
      | .write .. | .delete _ | .rollback => [.ok]
      | .begin | .commit => []

/-- A commit takes effect in this world: the worlds it may lead to, none if it cannot. -/
def applyCommit (w : World K V) (c : Commit K V) : List (World K V) :=
  let rest := w.commits.map fun d => if d == c then { d with applied := true } else d
  match cfg.isolation with
  | .readCommitted =>
    if c.txn.inserted.all fun k => (w.db.get k).isNone then
      let w := { w with db := w.db.apply c.txn.writes, commits := rest }
      [{ w with waiting := w.waiting.map fun x =>
          { x with seen := (w.answersNow cfg x.request).foldl (fun s a => if s.contains a then s else s ++ [a]) x.seen } }]
    else []
  | .serializable =>
    if cfg.history_max ≤ w.history.length then []
    else (w.commitPlaces c.txn).map fun p => { w.placeAt c.txn p with commits := rest }

/-- Every world reachable by letting commits not yet applied take effect, in any order. -/
def expand (fuel : Nat) (w : World K V) : List (World K V) :=
  match fuel with
  | 0 => [w]
  | fuel + 1 =>
    w :: (w.commits.filter (!·.applied)).flatMap fun c => (applyCommit cfg w c).flatMap (expand fuel)

end World

def dedup [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

namespace World

/-- The worlds this one becomes when request `r` is sent. -/
def send (w : World K V) (r : Request K V) : List (World K V) :=
  match r.op with
  | .commit =>
    match w.txn? r.txn with
    | some t =>
      if t.failed || cfg.commits_max ≤ w.commits.length then
        [{ w.dropTxn r.txn with waiting := w.waiting ++ [{ request := r }] }]
      else [{ w.dropTxn r.txn with commits := w.commits ++ [{ txn := t, request := some r.id }] }]
    | none => [{ w with waiting := w.waiting ++ [{ request := r }] }]
  | _ => [{ w with waiting := w.waiting ++ [{ request := r, seen := w.answersNow cfg r }] }]

/-- The worlds in which request `r`, of the waiting ones, gets `a`. -/
def answer (w : World K V) (r : Request K V) (a : Answer K V) : List (World K V) :=
  let w' := { w with waiting := w.waiting.filter (·.request.id != r.id) }
  let doomed := (w.waiting.find? (·.request.id == r.id)).any (·.doomed)
  if doomed && a != .failed && a != .unknown then [] else
  match r.op, a with
  | .begin, .ok =>
    if (w.txn? r.txn).isSome || cfg.txns_max ≤ w.txns.length then []
    else [{ w' with txns := w.txns ++ [{ id := r.txn, after := w.acknowledged }] }]
  | .begin, .failed | .begin, .unknown => [w']
  | _, .failed | _, .unknown =>
    match w.txn? r.txn with
    | some t =>
      match a with
      | .failed => [w'.setTxn { t with failed := true }]
      | _ => [w'.dropTxn r.txn]
    | none => [w']
  | .rollback, .ok => [w'.dropTxn r.txn]
  | op, a =>
    match w.txn? r.txn with
    | none => []
    | some t =>
      let now := w.answersNow cfg r
      let seen := ((w.waiting.find? (·.request.id == r.id)).map (·.seen)).getD []
      let possible := match cfg.isolation with
        | .readCommitted => seen.contains a || now.contains a
        | .serializable => now.contains a
      match op, a with
      | .read k, .value v =>
        if !possible then []
        else if (t.own k).isSome then [w']
        else [w'.setTxn { t with reads := t.reads ++ [.key k v] }]
      | .scan, .rows rows =>
        if !possible then []
        else [w'.setTxn { t with reads := t.reads ++
          [.all (rows.filter fun (k, _) => (t.own k).isNone) (t.writes.map (·.1))] }]
      | .write k v, .ok => [w'.setTxn { t with writes := (k, some v) :: t.writes }]
      | .delete k, .ok => [w'.setTxn { t with writes := (k, none) :: t.writes }]
      | .insert k v, .ok =>
        if !possible then []
        else [w'.setTxn { t with writes := (k, some v) :: t.writes, inserted := k :: t.inserted
                                 reads := if (t.own k).isSome then t.reads else t.reads ++ [.key k none] }]
      | .append v, .key k =>
        if (t.view w.db).any (·.1 == k) then []
        else [w'.setTxn { t with writes := (k, some v) :: t.writes, inserted := k :: t.inserted }]
      | _, _ => []

/-- The worlds in which the commit numbered `id` gets `a`. -/
def answerCommit (w : World K V) (id : Nat) (a : Answer K V) : List (World K V) :=
  match w.commits.find? (·.request == some id) with
  | none =>
    -- the commit of a transaction that had failed, was unknown or over: it did nothing
    if a == .committed then [] else [w]
  | some c =>
    let others := w.commits.filter (· != c)
    match a with
    | .committed =>
      let ws := if c.applied then [w] else applyCommit cfg w c
      ws.map fun w => { w with commits := w.commits.filter (·.request != some id)
                               acknowledged := w.acknowledged ++ [c.txn.id] }
    | .failed => if c.applied then [] else [{ w with commits := others }]
    | .unknown =>
      if c.applied then [{ w with commits := others }]
      else [{ w with commits := others ++ [{ c with request := none }] }]
    | _ => []

end World

/-- The request numbered `id` among those outstanding. -/
def outstanding (w : World K V) (id : Nat) : Option (Request K V) :=
  (w.waiting.find? (·.request.id == id)).map (·.request)

/-- The state after the store answered `reply`, or `none` if no world allows it. -/
def State.allow (s : State K V) (reply : Reply K V) : Option (State K V) :=
  let worlds := dedup (s.worlds.flatMap fun w =>
    (w.expand cfg w.commits.length).flatMap fun w =>
      let ws := match outstanding w reply.id with
        | some r => w.answer cfg r reply.answer
        | none =>
          if w.commits.any (·.request == some reply.id) then w.answerCommit cfg reply.id reply.answer
          else []
      ws.map World.settle)
  if worlds.isEmpty then none else some { worlds }

/-- The state after the system sent `r`. -/
def State.observe (s : State K V) (r : Request K V) : State K V :=
  let isCommit := match r.op with | .commit => true | _ => false
  { worlds := dedup (s.worlds.flatMap fun w =>
      if isCommit then w.send cfg r
      else if (w.waiting.any (·.request.txn == r.txn)) then
        [{ w with waiting := w.waiting ++ [{ request := r, doomed := true }] }]
      else w.send cfg r) }

/-- What a run of requests (`.inl`) and replies (`.inr`) leaves, or `none` if a reply is one no
world allows. -/
def State.run (s : State K V) : List (Request K V ⊕ Reply K V) → Option (State K V)
  | [] => some s
  | .inl r :: rest => (s.observe cfg r).run rest
  | .inr reply :: rest =>
    match s.allow cfg reply with
    | some s => s.run rest
    | none => none

/-- The store as an `Outside`: it may answer each request outstanding, once, with what one of
the worlds allows, or lose the answer. -/
def outside {σ : Signature} (port : Port σ K V) : Outside σ (State K V) where
  init := {}
  allow s x := (port.replied x).bind (s.allow cfg)
  observe s out := match port.request out with
    | some r => s.observe cfg r
    | none => s

/-- The answers the store may give now to each outstanding request, as the checker samples them;
`failures` adds `failed` to each, `losses` adds `unknown`. -/
def samples {σ : Signature} (port : Port σ K V) (failures losses : Bool) (s : State K V) :
    List σ.In :=
  dedup (s.worlds.flatMap fun w => (w.expand cfg w.commits.length).flatMap fun w =>
    let waiting := w.waiting.flatMap fun x =>
      let base := match x.request.op with
        | _ => if x.doomed then []
          else match x.request.op with
            | .begin => [Answer.ok]
            | .commit => []
            | _ => dedup (x.seen ++ w.answersNow cfg x.request)
      (base ++ (if failures then [Answer.failed] else []) ++ (if losses then [Answer.unknown] else [])).map
        fun a => port.reply { id := x.request.id, answer := a }
    let commits := w.commits.filterMap fun c => c.request.map fun id =>
      ([Answer.committed] ++ (if failures then [Answer.failed] else []) ++ (if losses then [Answer.unknown] else [])).map
        fun a => port.reply { id, answer := a }
    waiting ++ commits.flatten)

end Lanes.Store
