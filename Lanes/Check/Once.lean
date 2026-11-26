/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Service
public import Lanes.Actors.Scheduler
public import Lanes.Check.Search

/-!
# Checking a system against a service its clients name requests to

`Service.onceMonitored svc key` is `Service.monitored` for `Service.once` of
`Lanes.Semantics.Once`: a request whose key has taken effect does not take effect again, and an
answer once given may be handed over any number of times. Inputs that have arrived are a set
shared by every candidate, the keys taken and the answers given are sets of each. A candidate
takes at most one step per distinct key, so as many rounds as inputs have arrived close it.
-/

@[expose] public section

namespace Lanes.Check

variable {In Out S K : Type}

structure OnceState (In Out S K : Type) where
  value : S
  taken : List K
  answered : List Out

def insertNew {α : Type} [BEq α] (l : List α) (a : α) : List α :=
  if l.contains a then l else l ++ [a]

def sameSet {α : Type} [BEq α] (a b : List α) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

/-- A hash that does not depend on the order of `l`, for a list without repeats. -/
def setHash {α : Type} [Hashable α] (salt : UInt64) (l : List α) : UInt64 :=
  l.foldl (fun h a => h + mixHash salt (hash a)) 0

namespace OnceState

variable [BEq S] [DecidableEq K] [DecidableEq In] [DecidableEq Out]

def equiv (a b : OnceState In Out S K) : Bool :=
  a.value == b.value && sameSet a.taken b.taken && sameSet a.answered b.answered

def take (svc : Service In Out S) (key : In → K) (a : OnceState In Out S K) (x : In) :
    OnceState In Out S K :=
  let (value, outs) := svc.step a.value x
  ⟨value, insertNew a.taken (key x), outs.foldl insertNew a.answered⟩

def hash [Hashable S] [Hashable K] [Hashable Out] (a : OnceState In Out S K) : UInt64 :=
  mixHash (Hashable.hash a.value) (mixHash (setHash 3 a.taken) (setHash 5 a.answered))

end OnceState

structure OnceMonitor (In Out S K : Type) where
  arrived : List In
  candidates : List (OnceState In Out S K)

namespace OnceMonitor

variable [BEq S] [DecidableEq K] [DecidableEq In] [DecidableEq Out]

def insertAll (known new : List (OnceState In Out S K)) : List (OnceState In Out S K) :=
  new.foldl (fun acc s => if acc.any (s.equiv ·) then acc else acc ++ [s]) known

def expand (svc : Service In Out S) (key : In → K) (arrived : List In)
    (states : List (OnceState In Out S K)) : List (OnceState In Out S K) :=
  states.flatMap fun a =>
    (arrived.filter fun x => !a.taken.contains (key x)).map (a.take svc key)

def close (svc : Service In Out S) (key : In → K) (arrived : List In)
    (states : List (OnceState In Out S K)) : List (OnceState In Out S K) :=
  (List.range arrived.length).foldl (fun acc _ => insertAll acc (expand svc key arrived acc))
    (insertAll [] states)

def ok (m : OnceMonitor In Out S K) : Bool :=
  !m.candidates.isEmpty

instance : BEq (OnceMonitor In Out S K) where
  beq a b := sameSet a.arrived b.arrived && a.candidates.length == b.candidates.length
    && a.candidates.all fun s => b.candidates.any (s.equiv ·)

instance [Hashable S] [Hashable K] [Hashable In] [Hashable Out] :
    Hashable (OnceMonitor In Out S K) where
  hash m := mixHash (setHash 11 m.arrived) (m.candidates.foldl (fun h s => h + mixHash 7 s.hash) 0)

def start (svc : Service In Out S) : OnceMonitor In Out S K :=
  ⟨[], [⟨svc.init, [], []⟩]⟩

def input (svc : Service In Out S) (key : In → K) (m : OnceMonitor In Out S K) (x : In) :
    OnceMonitor In Out S K :=
  let arrived := insertNew m.arrived x
  ⟨arrived, close svc key arrived m.candidates⟩

def output (m : OnceMonitor In Out S K) (out : Out) : OnceMonitor In Out S K :=
  { m with candidates := m.candidates.filter (·.answered.contains out) }

end OnceMonitor

def refinesOnce {σ : Signature} [BEq S] [DecidableEq K] {sys : System σ} {D : Type}
    (name : String) : Property (World sys (D × OnceMonitor σ.In σ.Out S K)) :=
  .always name fun w => w.driver.2.ok

end Check

def Service.onceMonitored {σ : Signature} [BEq S] {D : Type} [DecidableEq K]
    (svc : Service σ.In σ.Out S) (key : σ.In → K) (driver : Driver σ D) :
    Driver σ (D × Check.OnceMonitor σ.In σ.Out S K) where
  init := (driver.init, Check.OnceMonitor.start svc)
  inputs s := (driver.inputs s.1).map fun (x, d) => (x, (d, s.2.input svc key x))
  observe s out := (driver.observe s.1 out, s.2.output out)

end Lanes
