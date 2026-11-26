/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.System

/-!
# Service specs

A `Service` is the smallest useful spec of a system: a state, and a function saying what one
input does to it and which outputs it produces, as if inputs were handled one at a time with
nothing else going on. It is the artifact people review (rule 1.2).

A running system is concurrent, so "one at a time" needs a precise meaning. `Service.State` is
that meaning: inputs that have arrived wait in `pending`, each one takes effect atomically at
some later moment (`Service.apply`), and its outputs wait in `outbox` until they are handed
over. A system implements the service if everything observable about it can be explained this
way. For a service of operations and responses this is linearizability.

`Lanes.Check.Monitor` checks this on small instances and `Lanes.Semantics.Service` states it as
a refinement.

## Main definitions

- `Service σ S`: a sequential spec over the inputs and outputs of signature `σ`.
- `Service.State σ S`: the spec state together with inputs not yet applied and outputs not yet
  delivered.
- `Service.State.call`, `Service.apply`, `Service.State.ret`: an input arrives, an input takes
  effect, an output is delivered.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature} {S : Type}

/-- A sequential spec: what each input does and answers, one input at a time. -/
structure Service (σ : Signature) (S : Type) where
  /-- The initial state. -/
  init : S
  /-- Apply one input: the next state and the outputs it produces. -/
  step : S → σ.In → S × List σ.Out

namespace Service

/-- The state of a service used concurrently. -/
structure State (σ : Signature) (S : Type) where
  /-- The state of the sequential spec. -/
  value : S
  /-- Inputs that have arrived and not yet taken effect. -/
  pending : List σ.In
  /-- Outputs produced and not yet delivered. -/
  outbox : List σ.Out

/-- The state before any input. -/
def start (svc : Service σ S) : State σ S :=
  ⟨svc.init, [], []⟩

/-- An input arrives. -/
def State.call (st : State σ S) (x : σ.In) : State σ S :=
  { st with pending := st.pending ++ [x] }

/-- The pending input `x` takes effect. -/
def apply (svc : Service σ S) (st : State σ S) (x : σ.In) : State σ S :=
  let r := svc.step st.value x
  { value := r.1, pending := st.pending.erase x, outbox := st.outbox ++ r.2 }

/-- The output `out` is delivered, if it is waiting. -/
def State.ret (st : State σ S) (out : σ.Out) : Option (State σ S) :=
  if st.outbox.contains out then some { st with outbox := st.outbox.erase out } else none

end Service

end Lanes
