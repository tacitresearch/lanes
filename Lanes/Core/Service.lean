/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.System

/-!
# Service specs

A `Service` is the smallest useful spec of a system: a state, and a function saying what one
input does to it and which outputs it produces, as if inputs were handled one at a time with
nothing else going on. It is the artifact people review (rule 1.2). It names the inputs and
outputs and nothing of the actors, so it is written before them.

A running system is concurrent, so "one at a time" needs a precise meaning. `Service.State` is
that meaning: inputs that have arrived wait in `pending`, each one takes effect atomically at
some later moment (`Service.apply`), and its outputs wait in `outbox` until they are handed
over. A system implements the service if everything observable about it can be explained this
way. For a service of operations and responses this is linearizability.

A service may have deadlines (`T`): which are armed is read from the state, and one passing
takes effect at that moment (`Service.State.fire`). The system's timers that are those
deadlines fire them (`Deadlines`). With no deadlines, `T` is `Empty`.

`Lanes.Check.Monitor` checks this on small instances and `Lanes.Semantics.Service` states it as
a refinement.
-/

@[expose] public section

namespace Lanes

variable {In Out S T : Type}

structure Service (In Out S : Type) (T : Type := Empty) where
  init : S
  step : S → In → S × List Out
  armed : S → T → Bool := fun _ _ => false
  fire : S → T → S × List Out := fun s _ => (s, [])

namespace Service

structure State (In Out S : Type) where
  value : S
  pending : List In
  outbox : List Out

def start (svc : Service In Out S T) : State In Out S :=
  ⟨svc.init, [], []⟩

def State.call (st : State In Out S) (x : In) : State In Out S :=
  { st with pending := st.pending ++ [x] }

variable [DecidableEq In] [DecidableEq Out]

def apply (svc : Service In Out S T) (st : State In Out S) (x : In) : State In Out S :=
  let r := svc.step st.value x
  { value := r.1, pending := st.pending.erase x, outbox := st.outbox ++ r.2 }

def State.ret (st : State In Out S) (out : Out) : Option (State In Out S) :=
  if st.outbox.contains out then some { st with outbox := st.outbox.erase out } else none

def State.fire (svc : Service In Out S T) (st : State In Out S) (t : T) :
    Option (State In Out S) :=
  if svc.armed st.value t then
    let r := svc.fire st.value t
    some { st with value := r.1, outbox := st.outbox ++ r.2 }
  else none

end Service

end Lanes
