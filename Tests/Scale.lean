/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The cost of a message must not grow with the number of actors a shard holds, nor with the size
of the state of the actor that takes it. A shell that keeps a second reference to the kernel
makes every step copy the actor table, and a kernel that steps a state its table still holds
makes every step copy the state. No functional test notices either: it only shows as time. So
these measure time, with a wide margin.
-/

namespace Tests.Scale

open Lanes Std.Async

abbrev sig : Signature where
  Id := Nat
  Msg _ := Unit
  In := Nat

abbrev counters : System sig where
  State _ := Nat
  actor _ := { init := 0, step := fun s _ => (s + 1, []), recover := fun s => (s, []) }
  accept x := ⟨x, ()⟩

def messages : Nat := 20000

/-- Milliseconds to send `messages` messages to one actor of a shard that holds `actors`. -/
def cost (actors : Nat) : Async Nat := do
  let rt ← Runtime.start counters
  for i in [0:actors] do rt.input (i + 1)
  rt.idle
  let t0 ← IO.monoMsNow
  for _ in [0:messages] do rt.input 0
  rt.idle
  let elapsed := (← IO.monoMsNow) - t0
  let handled := (← rt.state 0) == messages
  rt.stop
  return if handled then elapsed else 1000000

/-- Inputs a second through one shard with `producers` senders that do not wait for each other,
each input one message to an actor. -/
def flood (producers each : Nat) : Async Nat := do
  let rt ← Runtime.start counters { inboxCapacity := 4096 }
  let t0 ← IO.monoNanosNow
  discard <| Async.concurrentlyAll ((List.range producers).toArray.map fun p => do
    for _ in [0:each] do rt.input p)
  rt.idle
  let elapsed := (← IO.monoNanosNow) - t0
  rt.stop
  return producers * each * 1000000000 / max 1 elapsed

/-- Turns a second of the kernel alone, one input each: what a shard could do if nothing else
cost anything. -/
def kernelAlone (turns : Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut k := (Kernel.boot counters).1
  for i in [0:turns] do
    match Journal.turn k i (some 0) 64 with
    | { kernel, .. } => k := kernel
  let elapsed := (← IO.monoNanosNow) - t0
  return if (k.cell 0).state == turns then turns * 1000000000 / max 1 elapsed else 0

abbrev arraySig : Signature where
  Id := Unit
  Msg _ := Nat
  In := Nat

/-- One actor whose state is `initial`; message `n` writes `n` at `n` modulo the size. -/
abbrev array (initial : Array Nat) : System arraySig where
  State _ := Array Nat
  actor _ :=
    { init := initial, step := fun s n => (s.set! (n % s.size) n, []), recover := fun s => (s, []) }
  accept n := ⟨(), n⟩

def writes : Nat := 1000

/-- Nanoseconds for `writes` messages to the actor of `array` with `size` numbers, after a
first message, which copies `initial`. A run whose writes are not all there at the end counts as
a thousand seconds. -/
def kernelWrites (size : Nat) : IO Nat := do
  let sys := array (Array.replicate size 0)
  let mut k := (Kernel.boot sys).1
  match Journal.turn k 0 (some 0) 64 with
  | { kernel, .. } => k := kernel
  let t0 ← IO.monoNanosNow
  for n in [1:writes + 1] do
    match Journal.turn k 0 (some n) 64 with
    | { kernel, .. } => k := kernel
  let elapsed := (← IO.monoNanosNow) - t0
  return if (k.cell ()).state[writes % size]! == writes then elapsed else 1000000000000

/-- `kernelWrites` on a shard. -/
def shardWrites (size : Nat) : IO Nat := (do
  let rt ← Runtime.start (array (Array.replicate size 0))
  rt.input 0
  rt.idle
  let t0 ← IO.monoNanosNow
  for n in [1:writes + 1] do rt.input n
  rt.idle
  let elapsed := (← IO.monoNanosNow) - t0
  let written := (← rt.state ())[writes % size]! == writes
  rt.stop
  return if written then elapsed else 1000000000000 : Async Nat).block

def fastest (run : IO Nat) : IO Nat :=
  return min (← run) (min (← run) (← run))

def tests : IO (List (String × Bool)) := do
  let small ← (cost 1000).block
  let large ← (cost 100000).block
  IO.println s!"scale: {messages} messages take {small} ms with 1000 actors, {large} ms with 100000"
  IO.println s!"flood: {← (flood 1 200000).block} inputs a second from one sender, {← (flood 4 100000).block} from four; the kernel alone does {← kernelAlone 200000} turns a second"
  let aloneSmall ← fastest (kernelWrites 10000)
  let aloneLarge ← fastest (kernelWrites 1000000)
  let shardSmall ← fastest (shardWrites 10000)
  let shardLarge ← fastest (shardWrites 1000000)
  let us (ns : Nat) := s!"{ns / writes / 1000}.{ns / writes / 100 % 10} µs"
  IO.println s!"in place: a write to a state of 10^4 numbers takes {us aloneSmall} in the kernel and {us shardSmall} on a shard, to one of 10^6 {us aloneLarge} and {us shardLarge}"
  return [("scale: a message costs the same whatever the number of actors",
      large ≤ 4 * small + 50),
    ("scale: a step updates its actor's state in place, whatever its size, in the kernel",
      aloneLarge ≤ 10 * aloneSmall + 50000000),
    ("scale: and on a shard", shardLarge ≤ 10 * shardSmall + 50000000)]

end Tests.Scale
