/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Postgres.IO.Db
public import Lanes.Db.Worker
public import Lanes.Outside.IO.Clock

/-!
The worker of a jobs table (`Lanes/Db/Worker.lean`) on PostgreSQL. It runs the worker's system on
a runtime of its own and does what it emits, deciding nothing (rule 3.9): a call to the store
goes to the typed store's driver (`Postgres.Typed.handler`), an attempt to `perform`, the job's
adapter, on a task of its own, whose answer, or `unknown` when it throws or gives none, is handed
back as an input. A clock ticks every `poll_ms` with the wall clock's time (`Clock.Wall`). An
input that finds the inbox full is dropped: a tick comes again, and an attempt whose answer is
lost is attempted again when its lease runs out.
-/

public section

namespace Lanes.Postgres.Typed

open Std Std.Async Lanes.Db Lanes.Db.Jobs

structure Worker {Q A W R : Type} [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R]
    (cfg : Db.Worker.Config R) where
  runtime : Runtime (Db.Worker.system (Q := Q) (A := A) (W := W) cfg)
  private stopping : IO.Ref Bool

variable {Q A W R : Type} [DecidableEq Q] [DecidableEq A] [DecidableEq W] [DecidableEq R]
  [Hashable Q] [Hashable A] [Hashable W] [Hashable R]

/-- Start the worker. `perform id deadline_ms work` does one attempt of job `id` through its
adapter, with `id` as the idempotency key, and answers by `deadline_ms`, or with `none`. -/
def Worker.start (cfg : Db.Worker.Config R) (store : Store (Q ⊕ Req) (A ⊕ Ans W))
    (perform : Int64 → Nat → W → Async (Option R)) (poll_ms : Nat := 1000) :
    Async (Worker (Q := Q) (A := A) (W := W) cfg) := do
  let clock ← Clock.Wall.start
  let stopping ← IO.mkRef false
  let rt ← Runtime.startWith (Db.Worker.system (Q := Q) (A := A) (W := W) cfg) {} fun rt _ out => do
    match out with
    | .store _ => handler Db.Worker.storePort store rt out
    | .run id lease deadline_ms work =>
      background do
        let answer ← try perform id deadline_ms work catch _ => pure none
        discard <| rt.tryInput (.ran id lease (match answer with
          | some r => .answer r
          | none => .unknown))
  background do
    repeat
      if ← stopping.get then break
      discard <| rt.tryInput (.tick (Int64.ofNat (← clock.now)))
      Std.Async.sleep (.ofNat poll_ms)
  return { runtime := rt, stopping }

def Worker.stop {cfg : Db.Worker.Config R} (w : Worker (Q := Q) (A := A) (W := W) cfg) : Async Unit := do
  w.stopping.set true
  w.runtime.stop

end Lanes.Postgres.Typed
