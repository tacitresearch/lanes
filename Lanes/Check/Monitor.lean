/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Service
public import Lanes.Actors.Scheduler
public import Lanes.Check.Search

/-!
# Checking a system against a service spec

`Service.monitored` wraps a driver so that the model checker also checks refinement to a
`Service`: on every explored run, the inputs sent, the outputs seen and the deadlines passed so
far must be explainable by the spec. No refinement mapping is needed.

The monitor keeps every state the spec could be in given what has been observed. An input adds
itself to `pending` in each candidate, and then any pending inputs may take effect in any order.
An output keeps only the candidates that were waiting to deliver it. A timer that is a deadline
of the spec, or a message handed to an actor that is one, keeps, when it fires, the candidates
in which that deadline is armed, passes it in each, and closes them again, since inputs pending
may take effect after it. If no candidate is
left, the system has done something the spec does not allow, and the checker reports the trace.
This is the subset construction on the spec, the same idea as the linearizability checkers
Porcupine and Jepsen's Knossos, run inside the search instead of on recorded histories.

A monitor's candidates are a set kept as a list. The list never holds two states that are the
same up to `Service.State.equiv`, and the type says so (`Monitor.distinct`): that is what makes
comparing two monitors by length and one-way inclusion an equivalence, and their hash agree
with it (`Lanes.Check.MonitorEquiv`).
-/

@[expose] public section

namespace Lanes

variable {In Out S T : Type}

namespace Service.State

variable [BEq S] [DecidableEq In] [DecidableEq Out]

def equiv (a b : State In Out S) : Bool :=
  a.value == b.value && a.pending.isPerm b.pending && a.outbox.isPerm b.outbox

/-- A hash that agrees with `equiv`. -/
def hash [Hashable S] [Hashable In] [Hashable Out] (a : State In Out S) : UInt64 :=
  mixHash (Hashable.hash a.value)
    (mixHash (a.pending.foldl (fun h x => h + mixHash 3 (Hashable.hash x)) 0)
      (a.outbox.foldl (fun h o => h + mixHash 5 (Hashable.hash o)) 0))

/-- No state is `equiv` to one before it. Stated in this direction it needs nothing of `==` on
`S`: it is what `insertAll` tests before adding a state. -/
def Distinct (states : List (State In Out S)) : Prop :=
  states.Pairwise fun earlier later => later.equiv earlier = false

end Service.State

namespace Check

open Service (State)

namespace Monitor

variable [BEq S] [DecidableEq In] [DecidableEq Out]

def insertAll (known new : List (State In Out S)) : List (State In Out S) :=
  new.foldl (fun acc s => if acc.any (s.equiv ·) then acc else acc ++ [s]) known

/-- The states reached from `frontier` by one pending input taking effect. -/
def expand (svc : Service In Out S T) (frontier : List (State In Out S)) : List (State In Out S) :=
  frontier.flatMap fun s => s.pending.eraseDups.map (svc.apply s)

/-- `acc`, then the states of `next` that are in neither `known` nor what precedes them. -/
def freshFrom (known acc next : List (State In Out S)) : List (State In Out S) :=
  next.foldl (fun fresh s => if (known ++ fresh).any (s.equiv ·) then fresh else fresh ++ [s]) acc

/-- One round of `close` on the known states and the frontier, the states found last. -/
def closeStep (svc : Service In Out S T) (acc : List (State In Out S) × List (State In Out S)) :
    List (State In Out S) × List (State In Out S) :=
  let fresh := freshFrom acc.1 [] (expand svc acc.2)
  (acc.1 ++ fresh, fresh)

def rounds (states : List (State In Out S)) : Nat :=
  states.foldl (fun n s => max n s.pending.length) 0

/--
Close a set of candidates under pending inputs taking effect. Each application removes one
pending input, so as many rounds as the longest pending list reach everything.
-/
def close (svc : Service In Out S T) (states : List (State In Out S)) : List (State In Out S) :=
  let seed := insertAll [] states
  ((List.range (rounds states)).foldl (fun acc _ => closeStep svc acc) (seed, seed)).1

theorem distinct_insertAll {known : List (State In Out S)} (new : List (State In Out S))
    (h : State.Distinct known) : State.Distinct (insertAll known new) := by
  induction new generalizing known with
  | nil => exact h
  | cons s new ih =>
    refine ih (known := if known.any (s.equiv ·) then known else known ++ [s]) ?_
    split
    · exact h
    · next hany =>
      refine List.pairwise_append.mpr ⟨h, List.pairwise_singleton _ _, fun t ht u hu => ?_⟩
      obtain rfl := List.mem_singleton.mp hu
      exact Bool.eq_false_iff.mpr fun hequiv => hany (List.any_eq_true.mpr ⟨t, ht, hequiv⟩)

theorem append_freshFrom (known acc next : List (State In Out S)) :
    known ++ freshFrom known acc next = insertAll (known ++ acc) next := by
  induction next generalizing acc with
  | nil => rfl
  | cons s next ih =>
    have hfresh : freshFrom known acc (s :: next) = freshFrom known
        (if (known ++ acc).any (s.equiv ·) then acc else acc ++ [s]) next := rfl
    have hinsert : insertAll (known ++ acc) (s :: next) = insertAll
        (if (known ++ acc).any (s.equiv ·) then known ++ acc else known ++ acc ++ [s]) next := rfl
    rw [hfresh, hinsert, ih]
    split
    · rfl
    · rw [List.append_assoc]

theorem distinct_close (svc : Service In Out S T) (states : List (State In Out S)) :
    State.Distinct (close svc states) := by
  suffices h : ∀ (l : List Nat) (acc : List (State In Out S) × List (State In Out S)),
      State.Distinct acc.1 → State.Distinct (l.foldl (fun acc _ => closeStep svc acc) acc).1 from
    h _ _ (distinct_insertAll _ .nil)
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons _ l ih =>
    refine fun acc h => ih (closeStep svc acc) ?_
    rw [show (closeStep svc acc).1 = insertAll (acc.1 ++ []) (expand svc acc.2) from
      append_freshFrom ..]
    exact distinct_insertAll _ (by simpa using h)

end Monitor

structure Monitor (In Out S : Type) [BEq S] [DecidableEq In] [DecidableEq Out] where
  candidates : List (State In Out S)
  distinct : State.Distinct candidates

namespace Monitor

variable [BEq S] [DecidableEq In] [DecidableEq Out]

def ok (m : Monitor In Out S) : Bool :=
  !m.candidates.isEmpty

instance : BEq (Monitor In Out S) where
  beq a b := a.candidates.length == b.candidates.length
    && a.candidates.all fun s => b.candidates.any (s.equiv ·)

instance [Hashable S] [Hashable In] [Hashable Out] : Hashable (Monitor In Out S) where
  hash m := m.candidates.foldl (fun h s => h + mixHash 7 s.hash) 0

def start (svc : Service In Out S T) : Monitor In Out S :=
  ⟨[svc.start], List.pairwise_singleton _ _⟩

def input (svc : Service In Out S T) (m : Monitor In Out S) (x : In) : Monitor In Out S :=
  ⟨close svc (m.candidates.map (·.call x)), distinct_close ..⟩

def output (m : Monitor In Out S) (out : Out) : Monitor In Out S :=
  ⟨insertAll [] (m.candidates.filterMap (·.ret out)), distinct_insertAll _ .nil⟩

def fire (svc : Service In Out S T) (m : Monitor In Out S) (t : T) : Monitor In Out S :=
  ⟨close svc (m.candidates.filterMap (·.fire svc t)), distinct_close ..⟩

end Monitor

end Check

variable {σ : Signature}

/-- `driver`, with the monitor of `svc` beside it. The timers `deadlines` names and the
deliveries `delivered` names are the spec's deadlines passing; without them the spec has none. -/
def Service.monitored [BEq S] {D : Type} (svc : Service σ.In σ.Out S T) (driver : Driver σ D)
    (deadlines : Deadlines σ T := fun _ _ => none)
    (delivered : Deadlines σ T := fun _ _ => none) :
    Driver σ (D × Check.Monitor σ.In σ.Out S) where
  init := (driver.init, Check.Monitor.start svc)
  inputs s := (driver.inputs s.1).map fun (x, d) => (x, (d, s.2.input svc x))
  observe s out := (driver.observe s.1 out, s.2.output out)
  timeout s i msg := (driver.timeout s.1 i msg, (deadlines i msg).elim s.2 (s.2.fire svc))
  deliver s e := (driver.deliver s.1 e, (delivered e.dst e.msg).elim s.2 (s.2.fire svc))

def Check.refines [BEq S] {sys : System σ} {D : Type} (name : String) :
    Check.Property (World sys (D × Check.Monitor σ.In σ.Out S)) :=
  .always name fun w => w.driver.2.ok

end Lanes
