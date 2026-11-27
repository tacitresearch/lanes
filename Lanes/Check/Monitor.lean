/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Service
public import Lanes.Core.Scheduler
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

The cost is in the candidates. With `n` inputs in flight a monitor can hold a state for every
order in which some of them have taken effect: 92 for the five of the tutorial's shelf. Closing
them compares each new state with those known, in time quadratic in the candidates, so the shelf
takes 15 to 30 times as long to check with the monitor as without it (`Tests/MonitorSpeed.lean`,
which `lake exe lanesCheck` runs). Comparing two monitors reached by the same observations is linear,
since they hold their candidates in the same order, and the checker compares them last.
-/

@[expose] public section

namespace Lanes

variable {In Out S T : Type}

namespace Service.State

variable [BEq S] [DecidableEq In] [DecidableEq Out]

def equiv (a b : State In Out S) : Bool :=
  a.pending.length == b.pending.length && a.outbox.length == b.outbox.length &&
  a.value == b.value && a.pending.isPerm b.pending && a.outbox.isPerm b.outbox

/-- `equiv` is equal values and lists that are permutations of each other. The lengths it
compares first only make it fail sooner. -/
theorem equiv_iff {a b : State In Out S} : a.equiv b = true ↔
    (a.value == b.value) = true ∧ a.pending.Perm b.pending ∧ a.outbox.Perm b.outbox := by
  simp only [equiv, Bool.and_eq_true, beq_iff_eq, List.isPerm_iff]
  constructor
  · rintro ⟨⟨⟨_, hvalue⟩, hpending⟩, houtbox⟩
    exact ⟨hvalue, hpending, houtbox⟩
  · rintro ⟨hvalue, hpending, houtbox⟩
    exact ⟨⟨⟨⟨hpending.length_eq, houtbox.length_eq⟩, hvalue⟩, hpending⟩, houtbox⟩

/-- Two states that agree once the same output is delivered in each agreed before. -/
theorem equiv_of_ret {a b a' b' : State In Out S} {out : Out} (ha : a.ret out = some a')
    (hb : b.ret out = some b') (h : a'.equiv b' = true) : a.equiv b = true := by
  unfold ret at ha hb
  split at ha <;> split at hb <;> try contradiction
  rename_i hina hinb
  obtain rfl := Option.some.inj ha
  obtain rfl := Option.some.inj hb
  obtain ⟨hvalue, hpending, houtbox⟩ := equiv_iff.mp h
  refine equiv_iff.mpr ⟨hvalue, hpending, ?_⟩
  exact (List.perm_cons_erase (List.elem_iff.mp hina)).trans
    ((houtbox.cons out).trans (List.perm_cons_erase (List.elem_iff.mp hinb)).symm)

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
  next.foldl (fun fresh s => if known.any (s.equiv ·) || fresh.any (s.equiv ·) then fresh
    else fresh ++ [s]) acc

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
        (if (known ++ acc).any (s.equiv ·) then acc else acc ++ [s]) next := by
      rw [List.any_append]
      rfl
    have hinsert : insertAll (known ++ acc) (s :: next) = insertAll
        (if (known ++ acc).any (s.equiv ·) then known ++ acc else known ++ acc ++ [s]) next := rfl
    rw [hfresh, hinsert, ih]
    split
    · rfl
    · rw [List.append_assoc]

/-- Delivering an output keeps candidates apart (`State.equiv_of_ret`). -/
theorem distinct_filterMap_ret {states : List (State In Out S)} (h : State.Distinct states)
    (out : Out) : State.Distinct (states.filterMap (·.ret out)) := by
  refine List.pairwise_filterMap.mpr (h.imp fun {earlier later} hne b hb b' hb' => ?_)
  refine Bool.eq_false_iff.mpr fun hequiv => ?_
  simp [State.equiv_of_ret hb' hb hequiv] at hne

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

/-- Whether each state of the second list is `equiv` to one of `all`, trying first the state at
the same place in the third. -/
def withinFrom (all : List (State In Out S)) : List (State In Out S) → List (State In Out S) → Bool
  | [], _ => true
  | s :: rest, t :: others => (s.equiv t || all.any (s.equiv ·)) && withinFrom all rest others
  | s :: rest, [] => all.any (s.equiv ·) && withinFrom all rest []

theorem withinFrom_eq (all : List (State In Out S)) :
    ∀ (a others : List (State In Out S)), (∀ t ∈ others, t ∈ all) →
      withinFrom all a others = a.all fun s => all.any (s.equiv ·)
  | [], _, _ => rfl
  | s :: rest, t :: others, h => by
    have ht : (s.equiv t || all.any (s.equiv ·)) = all.any (s.equiv ·) := by
      cases hst : s.equiv t
      · rfl
      · exact (List.any_eq_true.mpr ⟨t, h t (.head _), hst⟩).symm
    rw [withinFrom, ht, withinFrom_eq all rest others fun u hu => h u (.tail _ hu), List.all_cons]
  | s :: rest, [], _ => by
    rw [withinFrom, withinFrom_eq all rest [] (fun _ hu => by cases hu), List.all_cons]

/-- Monitors reached by the same observations hold their candidates in the same order, so each
candidate is looked for first at its own place: that makes comparing two such monitors linear
instead of quadratic in their candidates. -/
instance : BEq (Monitor In Out S) where
  beq a b := a.candidates.length == b.candidates.length
    && withinFrom b.candidates a.candidates b.candidates

instance [Hashable S] [Hashable In] [Hashable Out] : Hashable (Monitor In Out S) where
  hash m := m.candidates.foldl (fun h s => h + mixHash 7 s.hash) 0

def start (svc : Service In Out S T) : Monitor In Out S :=
  ⟨[svc.start], List.pairwise_singleton _ _⟩

def input (svc : Service In Out S T) (m : Monitor In Out S) (x : In) : Monitor In Out S :=
  ⟨close svc (m.candidates.map (·.call x)), distinct_close ..⟩

def output (m : Monitor In Out S) (out : Out) : Monitor In Out S :=
  ⟨m.candidates.filterMap (·.ret out), distinct_filterMap_ret m.distinct out⟩

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
  deliver s i msg := (driver.deliver s.1 i msg, (delivered i msg).elim s.2 (s.2.fire svc))

def Check.refines [BEq S] {sys : System σ} {D : Type} (name : String) :
    Check.Property (World sys (D × Check.Monitor σ.In σ.Out S)) :=
  .always name fun w => w.driver.2.ok

end Lanes
