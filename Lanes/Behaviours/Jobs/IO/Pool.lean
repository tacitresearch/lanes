/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Lanes.Runtime.IO.Shell
public import Lanes.Behaviours.Jobs.Basic

/-!
The pool of workers behind the jobs actor (`Lanes.Behaviours.Jobs.Basic`). Each attempt the actor
dispatches is performed on a task of its own and its result handed back as an input. What to
do, when to try again, how long to wait and how many at once are the actor's; `Jobs.pool` is
what the workers may do, which the checker explores. A worker is a pure function
(`Jobs.compute`) or a call to another service through the HTTP client (`Jobs.call`, in
`Lanes/Web/IO/Jobs.lean`).
-/

public section

namespace Lanes.Jobs

open Std Std.Async

variable {σ : Signature} {K J R : Type}

/-- Which outputs of a system are attempts to make, and how a result goes back in. -/
structure Port (σ : Signature) (K J R : Type) where
  dispatched : σ.Out → Option (K × Nat × J)
  result : K → Nat → R → σ.In

/-- The port of the jobs actor alone. -/
def Port.alone [DecidableEq K] [DecidableEq J] [DecidableEq R] : Port (sig K J R) K J R where
  dispatched
    | .dispatch key attempt job => some (key, attempt, job)
    | .answer .. => none
  result := .result

/-- Performs an attempt on a task of its own, so the shard does not wait for it, and hands the
result to `deliver`, normally `Runtime.tryInput`. An attempt that throws gives no result, and
one whose result finds the inbox full is dropped: in both its deadline brings the next. -/
def handler (port : Port σ K J R) (perform : K → Nat → J → Async R)
    (deliver : σ.In → Async Bool) (out : σ.Out) (prio : Task.Priority := .default) :
    Async Unit := do
  if let some (key, attempt, job) := port.dispatched out then
    background (prio := prio) do
      try
        let r ← perform key attempt job
        discard <| deliver (port.result key attempt r)
      catch _ => pure ()

/-- A worker that computes `f`. -/
def compute (f : J → R) : K → Nat → J → Async R :=
  fun _ _ job => pure (f job)

end Lanes.Jobs
