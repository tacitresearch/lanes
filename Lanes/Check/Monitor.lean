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
`Service`: on every explored run, the inputs sent and outputs seen so far must be explainable by
the spec. No refinement mapping is needed.

The monitor keeps every state the spec could be in given what has been observed. An input adds
itself to `pending` in each candidate, and then any pending inputs may take effect in any order.
An output keeps only the candidates that were waiting to deliver it. If no candidate is left,
the system has done something the spec does not allow, and the checker reports the trace. This
is the subset construction on the spec, the same idea as the linearizability checkers Porcupine
and Jepsen's Knossos, run inside the search instead of on recorded histories.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {S : Type}

namespace Service.State

variable [BEq S]

def equiv (a b : State σ S) : Bool :=
  a.value == b.value && a.pending.isPerm b.pending && a.outbox.isPerm b.outbox

/-- A hash that agrees with `equiv`. -/
def hash [Hashable S] [Hashable σ.In] [Hashable σ.Out] (a : State σ S) : UInt64 :=
  mixHash (Hashable.hash a.value)
    (mixHash (a.pending.foldl (fun h x => h + mixHash 3 (Hashable.hash x)) 0)
      (a.outbox.foldl (fun h o => h + mixHash 5 (Hashable.hash o)) 0))

end Service.State

namespace Check

structure Monitor (σ : Signature) (S : Type) where
  /-- The candidate states, without repetition. -/
  candidates : List (Service.State σ S)

namespace Monitor

variable [BEq S]

def ok (m : Monitor σ S) : Bool :=
  !m.candidates.isEmpty

instance : BEq (Monitor σ S) where
  beq a b := a.candidates.length == b.candidates.length
    && a.candidates.all fun s => b.candidates.any (s.equiv ·)

instance [Hashable S] [Hashable σ.In] [Hashable σ.Out] : Hashable (Monitor σ S) where
  hash m := m.candidates.foldl (fun h s => h + mixHash 7 s.hash) 0

def insertAll (known new : List (Service.State σ S)) : List (Service.State σ S) :=
  new.foldl (fun acc s => if acc.any (s.equiv ·) then acc else acc ++ [s]) known

/--
Close a set of candidates under pending inputs taking effect. Each application removes one
pending input, so as many rounds as the longest pending list reach everything.
-/
def close (svc : Service σ S) (states : List (Service.State σ S)) : List (Service.State σ S) :=
  let rounds := states.foldl (fun n s => max n s.pending.length) 0
  let step := fun (acc : List (Service.State σ S) × List (Service.State σ S)) _ =>
    let next := acc.2.flatMap fun s => s.pending.eraseDups.map (svc.apply s)
    let fresh := next.foldl
      (fun fresh s => if (acc.1 ++ fresh).any (s.equiv ·) then fresh else fresh ++ [s]) []
    (acc.1 ++ fresh, fresh)
  ((List.range rounds).foldl step (insertAll [] states, insertAll [] states)).1

def start (svc : Service σ S) : Monitor σ S :=
  ⟨[svc.start]⟩

def input (svc : Service σ S) (m : Monitor σ S) (x : σ.In) : Monitor σ S :=
  ⟨close svc (m.candidates.map (·.call x))⟩

def output (m : Monitor σ S) (out : σ.Out) : Monitor σ S :=
  ⟨insertAll [] (m.candidates.filterMap (·.ret out))⟩

end Monitor

end Check

def Service.monitored [BEq S] {D : Type} (svc : Service σ S) (driver : Driver σ D) :
    Driver σ (D × Check.Monitor σ S) where
  init := (driver.init, Check.Monitor.start svc)
  inputs s := (driver.inputs s.1).map fun (x, d) => (x, (d, s.2.input svc x))
  observe s out := (driver.observe s.1 out, s.2.output out)

def Check.refines [BEq S] {sys : System σ} {D : Type} (name : String) :
    Check.Property (World sys (D × Check.Monitor σ S)) :=
  .always name fun w => w.driver.2.ok

end Lanes
