/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async

/-!
A thread's sleep that Lean's task manager does not see (`native/lanes.c`). A thread blocked on a
task (`IO.wait`, `Task.get`, `Async.block`) sleeps on the task manager's one condition, which
every task that finishes signals to all: under load it wakes once a task, takes the manager's
lock and sleeps again. A thread parked here wakes when it is unparked or its time is up.
-/

@[expose] public section

namespace Lanes

opaque ParkerImpl : NonemptyType

def Parker : Type := ParkerImpl.type

instance : Nonempty Parker := ParkerImpl.property

@[extern "lanes_parker_new"]
opaque Parker.new : BaseIO Parker

@[extern "lanes_park"]
opaque Parker.parkFor (p : @& Parker) (timed : Bool) (ms : UInt32) : BaseIO Unit

/-- Sleep until `unpark`, or return at once if it was called since the last `park`. It may
return early, so a caller checks what it waits for and parks again. -/
def Parker.park (p : Parker) : BaseIO Unit :=
  Parker.parkFor p false 0

/-- `park`, for at most `ms` milliseconds. -/
def Parker.parkAtMost (p : Parker) (ms : Nat) : BaseIO Unit :=
  Parker.parkFor p true (min ms 3600000).toUInt32

@[extern "lanes_unpark"]
opaque Parker.unpark (p : @& Parker) : BaseIO Unit

/-- Wait for `t` on a parker, which a continuation of `t` unparks. -/
def Parker.wait (t : Task α) : BaseIO α := do
  unless ← IO.hasFinished t do
    let p ← Parker.new
    discard <| BaseIO.mapTask (t := t) fun _ => Parker.unpark p
    while !(← IO.hasFinished t) do Parker.park p
  return t.get

/-- `x.block` without blocking on a task: `x` runs on the calling thread until it waits, and the
thread then parks until `x` is done. For a `main` that waits for a server. -/
def block (x : Std.Async.Async α) : IO α := do
  match ← Parker.wait (← x.toBaseIO) with
  | .ok a => return a
  | .error e => throw e

end Lanes
