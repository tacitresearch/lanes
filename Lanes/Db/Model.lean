/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Basic
public import Lanes.Db.Retry

/-!
# The typed store as an outside

What a system may see of the typed store at `SERIALIZABLE`: it sends calls (`Call`), each a
request to the store's handler; each call is answered (`Reply`) committed with the handler's
answer, failed, or unknown. The model is an `Outside`, so the checker explores a system against
it and a recorded run is checked with `Outside.allows`, as for the key-value store
(`Lanes/Outside/Store/Basic.lean`), whose way of keeping every database the answers allow it
follows (`State.worlds`).

A call takes effect at one moment between its request and its reply, as one run of its handler's
transaction on the database of that moment (`Txn.run`). That is serializable execution in an
order that follows real time: the driver runs the whole transaction inside the call, and a
transaction begun after another's commit was answered sees it. Retries after serialization
failures are inside the call and invisible here (`Retry.loop_committed`). The faults:

- **A failure.** A call answered failed did not take effect: every attempt conflicted, the
  connection was lost before `COMMIT`, the handler aborted, or the server refused a statement.
- **A lost `COMMIT`.** A call answered unknown may have taken effect before its answer, or may
  take effect at any later moment, or never.

Bounds (rule 2.6): at most `calls_max` calls outstanding or lost; a call beyond them is answered
only failed.
-/

@[expose] public section

namespace Lanes.Db

structure Call (Q : Type) where
  /-- The call's number, which its reply carries. -/
  id : Nat
  request : Q
  deriving DecidableEq, Repr, Hashable

structure Reply (A : Type) where
  id : Nat
  result : Result A
  deriving DecidableEq, Repr, Hashable

/-- Which outputs are calls to the store and which inputs answer them. -/
structure Port (σ : Signature) (Q A : Type) where
  call : σ.Out → Option (Call Q)
  reply : Reply A → σ.In
  replied : σ.In → Option (Reply A)

/-- Every limit is explicit (rule 2.6). -/
structure Config where
  calls_max : Nat := 4

/-- One database the answers so far are consistent with, and the calls not yet answered. -/
structure World (Q A : Type) where
  db : Db
  /-- Sent, not taken effect, answer to come. -/
  pending : List (Call Q) := []
  /-- Taken effect, answer to come. -/
  done : List (Nat × A) := []
  /-- Answered unknown before taking effect: may take effect at any later moment, or never. -/
  lost : List Q := []
  /-- Sent beyond `calls_max`: answered only failed. -/
  refused : List Nat := []
  deriving DecidableEq, Hashable

structure State (Q A : Type) where
  worlds : List (World Q A)
  deriving DecidableEq, Hashable

variable {Q A : Type} [DecidableEq Q] [DecidableEq A]

def dedup {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

namespace World

variable (h : Handler Q A)

/-- The worlds after one call, pending or lost, takes effect; none for a call that aborts on
this database (it stays, to be answered failed, or to take effect on a later one). -/
def effects (w : World Q A) : List (World Q A) :=
  (w.pending.filterMap fun c => ((h c.request).run w.db).toOption.map fun (a, db) =>
      { w with db, pending := w.pending.erase c, done := w.done ++ [(c.id, a)] })
    ++ w.lost.filterMap fun q => ((h q).run w.db).toOption.map fun (_, db) =>
      { w with db, lost := w.lost.erase q }

/-- Every world reachable by letting calls take effect, in any order. -/
def expand : Nat → World Q A → List (World Q A)
  | 0, w => [w]
  | fuel + 1, w => w :: (w.effects h).flatMap (expand fuel)

def fuel (w : World Q A) : Nat := w.pending.length + w.lost.length

/-- The worlds in which the reply `r` comes now, from this one, before any call takes effect. -/
def answer (w : World Q A) (r : Reply A) : List (World Q A) :=
  let pending := w.pending.find? (·.id == r.id)
  match r.result with
  | .committed a => if w.done.contains (r.id, a) then [{ w with done := w.done.erase (r.id, a) }] else []
  | .failed _ =>
    if w.refused.contains r.id then [{ w with refused := w.refused.erase r.id }]
    else match pending with
      | some c => [{ w with pending := w.pending.erase c }]
      | none => []
  | .unknown =>
    match pending, w.done.find? (·.1 == r.id) with
    | some c, _ => [{ w with pending := w.pending.erase c, lost := w.lost ++ [c.request] }]
    | none, some d => [{ w with done := w.done.erase d }]
    | none, none => if w.refused.contains r.id then [{ w with refused := w.refused.erase r.id }] else []

def send (cfg : Config) (w : World Q A) (c : Call Q) : World Q A :=
  if w.pending.length + w.lost.length < cfg.calls_max then { w with pending := w.pending ++ [c] }
  else { w with refused := w.refused ++ [c.id] }

end World

variable (cfg : Config) (h : Handler Q A)

def State.allow (s : State Q A) (r : Reply A) : Option (State Q A) :=
  let worlds := dedup (s.worlds.flatMap fun w => (w.expand h w.fuel).flatMap (·.answer r))
  if worlds.isEmpty then none else some { worlds }

def State.observe (s : State Q A) (c : Call Q) : State Q A :=
  { worlds := s.worlds.map (·.send cfg c) }

/-- What a run of calls (`.inl`) and replies (`.inr`) leaves, or `none` if a reply is one no world
allows. -/
def State.run (s : State Q A) : List (Call Q ⊕ Reply A) → Option (State Q A)
  | [] => some s
  | .inl c :: rest => (s.observe cfg c).run rest
  | .inr r :: rest =>
    match s.allow h r with
    | some s => s.run rest
    | none => none

/-- The typed store, from the database `start`, with the handler `h`. -/
def outside {σ : Signature} (start : Db) (port : Port σ Q A) : Outside σ (State Q A) where
  init := { worlds := [{ db := start }] }
  allow s x := (port.replied x).bind (s.allow h)
  observe s out := match port.call out with
    | some c => s.observe cfg c
    | none => s

/-- The replies the store may give now, as the checker samples them; `failures` adds a failure
to each call not taken effect, `losses` an unknown to each call outstanding. -/
def samples {σ : Signature} (port : Port σ Q A) (failures losses : Bool) (s : State Q A) :
    List σ.In :=
  dedup (s.worlds.flatMap fun w => (w.expand h w.fuel).flatMap fun w =>
    let done := w.done.flatMap fun (id, a) =>
      ([Result.committed a] ++ (if losses then [Result.unknown] else [])).map fun result => (id, result)
    let pending := w.pending.flatMap fun c =>
      ((if failures then [Result.failed .conflict] else []) ++ (if losses then [Result.unknown] else [])).map
        fun result => (c.id, result)
    let refused := w.refused.map fun id => (id, Result.failed .unavailable)
    (done ++ pending ++ refused).map fun (id, result) => port.reply { id, result })

end Lanes.Db
