/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The cost of a message must not grow with the number of actors a runtime holds, nor with the size
of the state of the actor that takes it. A shell that keeps a second reference to the kernel
makes every step copy the actor table, and a kernel that steps a state its table still holds
makes every step copy the state. No functional test notices either: it only shows as time. So
these measure time, with a wide margin.

On the runtime, a state crosses threads: between two turns of its actor it lives in the actor's
slot, which every worker can reach, and Lean never updates in place an object another thread may
see. A worker keeps the state in its own hands while it steps the actor, so the steps of one turn
update it in place, and the first step of a turn copies it. These tests send one message at a
time, so each is a turn and each write a copy and the walk that shares it again; the bound is a
few copies, so that a copy at every step of a turn would be caught.

Nor must an effect of a step cost more for the effects before it in the same step: a list that
an output is appended to makes a step with many outputs quadratic.
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

/-- Milliseconds to send `messages` messages to one actor of a runtime that holds `actors`. -/
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

/-- Inputs a second through one runtime with `producers` senders that do not wait for each other,
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

/-- Turns a second of the kernel alone, one input each: what a runtime could do if nothing else
cost anything. -/
def kernelAlone (turns : Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut k := (Kernel.boot counters).1
  for i in [0:turns] do
    match k.exec [.advance i, .input 0, .batch 64] with
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
  match k.exec [.input 0, .batch 64] with
  | { kernel, .. } => k := kernel
  let t0 ← IO.monoNanosNow
  for n in [1:writes + 1] do
    match k.exec [.input n, .batch 64] with
    | { kernel, .. } => k := kernel
  let elapsed := (← IO.monoNanosNow) - t0
  return if (k.cell ()).state[writes % size]! == writes then elapsed else 1000000000000

/-- `kernelWrites` on the runtime. -/
def runtimeWrites (size : Nat) : IO Nat := (do
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

abbrev pairSig : Signature where
  Id := Fin 2
  Msg _ := Nat
  In := Nat

/-- Two actors whose states are `initial`; input `n` writes `n` at `n` modulo the size in the
state of actor `n` modulo 2. -/
abbrev pair (initial : Array Nat) : System pairSig where
  State _ := Array Nat
  actor _ :=
    { init := initial, step := fun s n => (s.set! (n % s.size) n, []), recover := fun s => (s, []) }
  accept n := ⟨Fin.ofNat 2 n, n⟩

/-- `runtimeWrites` with the writes shared by two busy actors, on four workers. -/
def pairWrites (size : Nat) : IO Nat := (do
  let rt ← Runtime.start (pair (Array.replicate size 0)) { workers := 4 }
  rt.input 0
  rt.input 1
  rt.idle
  let t0 ← IO.monoNanosNow
  for n in [2:writes + 2] do rt.input n
  rt.idle
  let elapsed := (← IO.monoNanosNow) - t0
  let last := writes + 1
  let written := (← rt.state (Fin.ofNat 2 last))[last % size]! == last
  rt.stop
  return if written then elapsed else 1000000000000 : Async Nat).block

/-- Nanoseconds to copy an array of `size` numbers. -/
def copyNs (size : Nat) : IO Nat := do
  let a ← IO.lazyPure fun _ => Array.replicate size 0
  let t0 ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ => a.set! 0 1
  let elapsed := (← IO.monoNanosNow) - t0
  return if a[0]! + b[0]! == 1 then elapsed else 0

abbrev burstSig : Signature where
  Id := Fin 2
  Msg _ := Nat
  In := Nat
  Out := Nat

/-- On input `n`, actor 0 puts out `n` outputs and sends `n` messages to actor 1, which counts
them. -/
abbrev burst : System burstSig where
  State _ := Nat
  actor i := {
    init := 0
    step := fun s n =>
      if i = 0 then (s, (List.range n).flatMap fun k => [.emit k, .send 1 k]) else (s + 1, []) }
  accept n := ⟨0, n⟩

/-- Nanoseconds for the scheduler to write back a step with `n` outputs and `n` sends
(`Sched.Slot.put`). -/
def putNs (n : Nat) : IO Nat := do
  let effects ← IO.lazyPure fun _ => (List.range n).flatMap fun k =>
    [(.emit k : Effect burstSig 0), .send 1 k]
  let slot : Sched.Slot burst 0 := { Sched.Slot.fresh burst 0 with cell := { state := 0, up := true } }
  let t0 ← IO.monoNanosNow
  let c ← IO.lazyPure fun _ => (slot.put 0 ((0 : Nat), effects)).2
  let elapsed := (← IO.monoNanosNow) - t0
  return if c.outputs.length == n && c.sends.length == n then elapsed else 1000000000000

/-- Nanoseconds for the kernel to take the input, start actor 0 and step it on it. -/
def kernelNs (n : Nat) : IO Nat := do
  let k := (Kernel.boot burst).1
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => k.exec [.input n, .batch 2]
  let elapsed := (← IO.monoNanosNow) - t0
  return if r.outputs.length == n && r.kernel.queue.length == n then elapsed else 1000000000000

/-- Nanoseconds on the runtime from the input until actor 1 has taken every message and every
output is handed over. -/
def runtimeNs (n : Nat) : IO Nat := (do
  let outputs ← IO.mkRef 0
  let rt ← Runtime.start burst { workers := 2 } fun _ => outputs.modify (· + 1)
  rt.idle
  let t0 ← IO.monoNanosNow
  rt.input n
  rt.idle
  let elapsed := (← IO.monoNanosNow) - t0
  let ok := (← rt.state 1) == n && (← outputs.get) == n
  rt.stop
  return if ok then elapsed else 1000000000000 : Async Nat).block

def fastest (run : IO Nat) : IO Nat :=
  return min (← run) (min (← run) (← run))

def tests : IO (List (String × Bool)) := do
  let small ← (cost 1000).block
  let large ← (cost 100000).block
  IO.eprintln s!"scale: {messages} messages take {small} ms with 1000 actors, {large} ms with 100000"
  IO.eprintln s!"flood: {← (flood 1 200000).block} inputs a second from one sender, {← (flood 4 100000).block} from four; the kernel alone does {← kernelAlone 200000} turns a second"
  let aloneSmall ← fastest (kernelWrites 10000)
  let aloneLarge ← fastest (kernelWrites 1000000)
  let runtimeSmall ← fastest (runtimeWrites 10000)
  let runtimeLarge ← fastest (runtimeWrites 1000000)
  let us (ns : Nat) := s!"{ns / writes / 1000}.{ns / writes / 100 % 10} µs"
  IO.eprintln s!"in place: a write to a state of 10^4 numbers takes {us aloneSmall} in the kernel and {us runtimeSmall} on the runtime, to one of 10^6 {us aloneLarge} and {us runtimeLarge}"
  let pairSmall ← fastest (pairWrites 10000)
  let pairLarge ← fastest (pairWrites 1000000)
  let copy ← fastest (copyNs 1000000)
  IO.eprintln s!"two busy actors on four workers: a write to a state of 10^4 numbers takes {us pairSmall}, to one of 10^6 {us pairLarge}; a copy of 10^6 numbers takes {copy / 1000} µs"
  let sizes := [1000, 10000, 100000]
  let burstTimes ← [putNs, kernelNs, runtimeNs].mapM fun run => sizes.mapM (fastest ∘ run)
  let ms (ns : Nat) := s!"{ns / 1000000}.{ns / 100000 % 10} ms"
  IO.eprintln s!"a step with 10^3, 10^4, 10^5 outputs and as many sends: written back in {(burstTimes[0]!).map ms}, through the kernel in {(burstTimes[1]!).map ms}, on the runtime until all are handled in {(burstTimes[2]!).map ms}"
  -- Ten times the effects: linear is ten times the time, quadratic a hundred.
  let linear (ts : List Nat) := (ts.zip ts.tail).all fun (a, b) => b ≤ 25 * a + 50000000
  return [("scale: a step's outputs and sends cost time linear in their number",
      burstTimes.all linear),
    ("scale: a message costs the same whatever the number of actors",
      large ≤ 4 * small + 50),
    ("scale: a step updates its actor's state in place, whatever its size, in the kernel",
      aloneLarge ≤ 10 * aloneSmall + 50000000),
    ("scale: on the runtime, a write costs at most a few copies of the state",
      runtimeLarge ≤ 6 * writes * copy + 50000000 && runtimeSmall < 1000000000000),
    ("scale: and on two busy actors on four workers",
      pairLarge ≤ 6 * writes * copy + 50000000 && pairSmall < 1000000000000)]

end Tests.Scale
