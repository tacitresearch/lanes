/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.IO.Shell

/-!
SIGTERM and SIGINT, through `Std.Async`'s signal waiters: what a supervisor (systemd,
Kubernetes, a shell's Ctrl-C) sends a process it wants to stop. Caught, they start a stop that
loses nothing taken; once the first has come, the waiters are let go, so a second ends the
process at once, as the first would have without them. SIGKILL and a loss of power cannot be
caught: they are the semantics' restart (D110), which every proof under `EnvModel.mayRestart`
already covers.
-/

@[expose] public section

namespace Lanes

open Std.Async

/-- Wait for SIGTERM or SIGINT, or for `ended` to finish first: `none` at a signal, else what
`ended` gave. `caught` runs once the signals are caught, before anything else is waited for. -/
def awaitStopSignal {α : Type} (ended : Async α) (caught : IO Unit := pure ()) :
    Async (Option α) := do
  let signals ← [Signal.sigterm, .sigint].mapM fun s => Signal.Waiter.mk s false
  let woken : IO.Promise (Except IO.Error (Option α)) ← IO.Promise.new
  for signal in signals do
    discard <| BaseIO.mapTask (t := ← signal.wait) fun
      | .ok _ => woken.resolve (.ok none)
      | .error _ => pure ()
  discard <| async do
    try woken.resolve (.ok (some (← ended))) catch e => woken.resolve (.error e)
  caught
  let got ← await woken.result?
  for signal in signals do signal.stop
  match got with
  | some (.ok got) => return got
  | some (.error e) => throw e
  | none => throw (IO.userError "lanes: the wait for a signal was dropped")

/-- Run until the runtime ends, or until SIGTERM or SIGINT, then `stop` it: it takes no more
inputs, and every input it took is taken by its actor before it returns. Returns then, so a
`main` that ends here exits with status 0; throws if an error ended the runtime, so that a
supervisor starts it again. -/
def Runtime.stopOnSignal {σ : Signature} {sys : System σ} [Hashable σ.Id] (rt : Runtime sys)
    (caught : IO Unit := pure ()) : Async Unit := do
  match ← awaitStopSignal rt.ended caught with
  | none => rt.stop
  | some none => pure ()
  | some (some e) => throw e

end Lanes
