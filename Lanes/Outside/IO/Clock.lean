/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Time
public import Lanes.Runtime.IO.Shell
public import Lanes.Outside.Basic

/-!
The clock as an adapter, and the shape every adapter has. A system asks the time with an output
and is told with an input, so `step` stays pure and the answer is in the journal when the shard
is replayed. The adapter is two things that must agree: `Clock.outside`, what a clock may do,
which the checker explores; and `Clock.handler`, what this clock does, in IO. A test records a
real run and checks it against the model (`Outside.allows`).
-/

@[expose] public section

namespace Lanes.Clock

open Std.Async

variable {σ : Signature}

/-- Which outputs ask the time and which inputs tell it. `told` reads back what `tell` made. -/
structure Port (σ : Signature) where
  asked : σ.Out → Option Nat
  tell : (question time_ms : Nat) → σ.In
  told : σ.In → Option (Nat × Nat)

/-- What a clock may do: answer a question that was asked and not yet answered, with a time no
earlier than any it has given. It may also not answer. It remembers the open questions and the
last time it gave. -/
def outside (port : Port σ) : Outside σ (List Nat × Nat) where
  init := ([], 0)
  allow d x :=
    match port.told x with
    | some (question, time_ms) =>
      if question ∈ d.1 ∧ d.2 ≤ time_ms then some (d.1.erase question, time_ms) else none
    | none => none
  observe d out :=
    match port.asked out with
    | some question => (question :: d.1, d.2)
    | none => d

/-- The latest time a journal says the clock gave. A clock that starts on a journal starts no
earlier, so that the times in a replayed run and those given after it are still in order. -/
def latest (port : Port σ) (past : List (Journal.Entry σ)) : Nat :=
  past.foldl (init := 0) fun latest entry =>
    match entry with
    | .input x => (port.told x).elim latest fun (_, time_ms) => max latest time_ms
    | _ => latest

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
