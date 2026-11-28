/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Time
public import Lanes.Runtime.IO.Shell
public import Lanes.Outside.Clock

/-!
The clock as an adapter, and the shape every adapter has. A system asks the time with an output
and is told with an input, so `step` stays pure and the checker can give it any time the model
allows. The adapter is two things that must agree: `Clock.outside`, what a clock may do
(`Lanes/Outside/Clock.lean`), which the checker explores; and `Clock.handler`, what this clock
does, in IO. A test records a real run and checks it against the model (`Outside.allows`).
-/

@[expose] public section

namespace Lanes.Clock

open Std.Async

variable {σ : Signature}

/-- Remembers the last time given: the wall clock may be set back, and this clock may not go
back. -/
structure Wall where
  private mk ::
  private last : IO.Ref Nat

@[no_expose] def Wall.start (floor_ms : Nat := 0) : BaseIO Wall :=
  return { last := ← IO.mkRef floor_ms }

/-- Milliseconds since the Unix epoch, and never less than was given before. -/
@[no_expose] def Wall.now (clock : Wall) : IO Nat := do
  let wall := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat
  clock.last.modifyGet fun last => (max last wall, max last wall)

/-- An answer that finds the inbox full is dropped, which the model allows: whoever asks must
be able to do without. -/
def handler {sys : System σ} [Hashable σ.Id] (clock : Wall) (port : Port σ) (rt : Runtime sys)
    (out : σ.Out) : Async Unit := do
  if let some question := port.asked out then
    discard <| rt.tryInput (port.tell question (← clock.now))

end Lanes.Clock
