/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Store.Basic

/-!
What the store model allows and refuses, on the runs that tell isolation levels and faults apart:
a `COMMIT` whose answer is lost may or may not have taken effect, and may take effect later;
a transaction that failed never commits; a unique key is refused twice; write skew and lost
updates are allowed at read committed and refused at serializable; serializable still allows a
transaction to come before one that committed while it ran, as PostgreSQL's does; and a
transaction begun after a commit was answered sees it. Each is decided by evaluation
(`decide`), on keys and values that are numbers.
-/

@[expose] public section

namespace Lanes.Store

def nat (isolation : Isolation) : Config Nat := { isolation, nextKey := fun ks => ks.foldl max 0 + 1 }

abbrev Run := List (Request Nat Nat ⊕ Reply Nat Nat)

def ask (id txn : Nat) (op : Op Nat Nat) : Request Nat Nat ⊕ Reply Nat Nat := .inl { id, txn, op }

def say (id : Nat) (a : Answer Nat Nat) : Request Nat Nat ⊕ Reply Nat Nat := .inr { id, answer := a }

/-- Whether the model allows the run, from an empty store. -/
def allows (isolation : Isolation) (run : Run) : Bool := ((State.run (nat isolation) {} run)).isSome

/-- A transaction writes `1 ↦ 5` and its `COMMIT` is answered `unknown`; then another reads key 1
and is answered `v`. -/
def lostCommit (v : Option Nat) : Run :=
  [ask 0 1 .begin, say 0 .ok, ask 1 1 (.write 1 5), say 1 .ok, ask 2 1 .commit, say 2 .unknown,
   ask 3 2 .begin, say 3 .ok, ask 4 2 (.read 1), say 4 (.value v)]

/-- A lost `COMMIT` may have taken effect or not, at either level. -/
theorem lost_commit_either :
    (allows .readCommitted (lostCommit (some 5)) && allows .readCommitted (lostCommit none)
      && allows .serializable (lostCommit (some 5)) && allows .serializable (lostCommit none)
      && !allows .readCommitted (lostCommit (some 6))) = true := by
  decide

/-- Its effect may still appear after a read did not see it. -/
theorem lost_commit_later :
    (allows .readCommitted (lostCommit none ++ [ask 5 2 (.read 1), say 5 (.value (some 5))])
      && allows .serializable (lostCommit none ++
        [ask 5 2 .commit, say 5 .committed, ask 6 3 .begin, say 6 .ok, ask 7 3 (.read 1),
         say 7 (.value (some 5))])) = true := by
  decide

/-- A transaction one of whose statements failed is never answered committed. -/
theorem failed_never_committed :
    (allows .readCommitted [ask 0 1 .begin, say 0 .ok, ask 1 1 (.write 1 5), say 1 .failed,
        ask 2 1 .commit, say 2 .committed]
      || allows .serializable [ask 0 1 .begin, say 0 .ok, ask 1 1 (.write 1 5), say 1 .failed,
        ask 2 1 .commit, say 2 .committed]) = false := by
  decide

/-- A key inserted and committed is not inserted again. -/
theorem insert_unique :
    (allows .readCommitted [ask 0 1 .begin, say 0 .ok, ask 1 1 (.insert 1 5), say 1 .ok,
        ask 2 1 .commit, say 2 .committed, ask 3 2 .begin, say 3 .ok, ask 4 2 (.insert 1 6), say 4 .ok]
      || allows .serializable [ask 0 1 .begin, say 0 .ok, ask 1 1 (.insert 1 5), say 1 .ok,
        ask 2 1 .commit, say 2 .committed, ask 3 2 .begin, say 3 .ok, ask 4 2 (.insert 1 6), say 4 .ok])
      = false := by
  decide

/-- Two transactions each read what the other writes, and both commit. -/
def writeSkew : Run :=
  [ask 0 1 .begin, say 0 .ok, ask 1 2 .begin, say 1 .ok,
   ask 2 1 (.read 1), say 2 (.value none), ask 3 2 (.read 2), say 3 (.value none),
   ask 4 1 (.write 2 1), say 4 .ok, ask 5 2 (.write 1 1), say 5 .ok,
   ask 6 1 .commit, say 6 .committed, ask 7 2 .commit, say 7 .committed]

theorem write_skew : (allows .readCommitted writeSkew && !allows .serializable writeSkew) = true := by
  decide

/-- Two transactions read a key, each writes it, and both commit: one update is lost. -/
def lostUpdate : Run :=
  [ask 0 1 .begin, say 0 .ok, ask 1 2 .begin, say 1 .ok,
   ask 2 1 (.read 1), say 2 (.value none), ask 3 2 (.read 1), say 3 (.value none),
   ask 4 1 (.write 1 1), say 4 .ok, ask 5 2 (.write 1 2), say 5 .ok,
   ask 6 1 .commit, say 6 .committed, ask 7 2 .commit, say 7 .committed]

theorem lost_update : (allows .readCommitted lostUpdate && !allows .serializable lostUpdate) = true := by
  decide

/-- One transaction reads key 1; another writes it and commits; the first writes key 2 and
commits. It comes first in the order, which serializable allows. -/
def earlier : Run :=
  [ask 0 1 .begin, say 0 .ok, ask 1 1 (.read 1), say 1 (.value none),
   ask 2 2 .begin, say 2 .ok, ask 3 2 (.write 1 1), say 3 .ok, ask 4 2 .commit, say 4 .committed,
   ask 5 1 (.write 2 1), say 5 .ok, ask 6 1 .commit, say 6 .committed]

theorem serializable_earlier : allows .serializable earlier = true := by
  decide

/-- A transaction begun after a commit was answered reads what it wrote. -/
theorem sees_acknowledged :
    (allows .serializable [ask 0 1 .begin, say 0 .ok, ask 1 1 (.write 1 5), say 1 .ok,
        ask 2 1 .commit, say 2 .committed, ask 3 2 .begin, say 3 .ok, ask 4 2 (.read 1), say 4 (.value none)]
      || allows .readCommitted [ask 0 1 .begin, say 0 .ok, ask 1 1 (.write 1 5), say 1 .ok,
        ask 2 1 .commit, say 2 .committed, ask 3 2 .begin, say 3 .ok, ask 4 2 (.read 1), say 4 (.value none)])
      = false := by
  decide

end Lanes.Store
