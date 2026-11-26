/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Lanes.Actors.KernelSound

/-!
The runtime is a shell around the kernel: one task that takes commands from an inbox, tells the
kernel the time, lets it work, and hands its outputs on. Which message is next, which timers
are due, how long to sleep and when the shard is idle are the kernel's answers
(`Lanes.Kernel`), not decisions made here.

By `Kernel.exec_reachable` nothing this loop does can take the system outside the semantics.
What is trusted is that it hands outputs on as the kernel gave them. Actors do not run in
parallel with each other; parallelism comes from running more shards.

The inbox is bounded, which is the system's back-pressure: `input` waits for room and
`tryInput` refuses (rule 3.8).
-/

public section

namespace Lanes

open Std Std.Async

variable {σ : Signature}

structure Runtime.Config where
  /-- Inputs wait here for the shard. When it is full, `tryInput` refuses. -/
  inboxCapacity : Nat := 1024
  /-- Units of kernel work between two looks at the inbox, so that a busy shard still admits
  inputs. At least one is done. -/
  batch : Nat := 64
  /-- Keep the events performed, for tests. By `Kernel.exec_reachable` they are a run of the
  semantics. -/
  record : Bool := false

private inductive Cmd (sys : System σ) where
  | input (x : σ.In)
  | idle (timers : Bool) (done : IO.Promise Bool)
  | peek (i : σ.Id) (reply : IO.Promise (sys.State i))

private inductive Taken (sys : System σ) where
  | command (c : Cmd sys)
  | nothing
  | closed

structure Runtime (sys : System σ) [Hashable σ.Id] where
  private mk ::
  private config : Runtime.Config
  private inbox : CloseableChannel (Cmd sys)
  private log : IO.Ref (Array (Event σ))
  private epoch_ms : Nat
  private finished : IO.Promise Unit

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

private def stopped : IO.Error := IO.userError "lanes: the runtime has stopped"

private def record (rt : Runtime sys) (events : List (Event σ)) : BaseIO Unit := do
  if rt.config.record then rt.log.modify (· ++ events.toArray)

private def handOver (onOutput : σ.Out → Async Unit) (outputs : List σ.Out) : Async Unit := do
  for out in outputs do
    try onOutput out
    catch e => IO.eprintln s!"lanes: output handler failed: {e}"

private def now (rt : Runtime sys) : BaseIO Nat :=
  return (← IO.monoMsNow) - rt.epoch_ms

/-- Blocks the calling thread, which is the shard's own. -/
private def take (rt : Runtime sys) : Kernel.Wait → IO (Taken sys)
  | .none => do
    match ← rt.inbox.tryRecv with
    | some c => return .command c
    | none => return if ← rt.inbox.isClosed then .closed else .nothing
  | .forever => return match ← IO.wait (← rt.inbox.recv) with
    | some c => .command c
    | none => .closed
  | .for_ms ms => Async.block do
    Selectable.one #[
      .case rt.inbox.recvSelector fun
        | some c => pure (.command c)
        | none => pure .closed,
      .case (← Selector.sleep (.ofNat ms)) fun _ => pure .nothing]

/--
The shard's loop, on a thread of its own. It is not an `Async` task, for a reason that no test
of behaviour shows: Lean never updates an object in place once another thread may see it, and
state held across an `await` is handed to the task system. A kernel kept that way is copied,
actor table and all, on every step (`Tests/Scale.lean`). Here it is created on this thread and
never leaves it; only commands, events and outputs cross.
-/
private def loop (rt : Runtime sys) (onOutput : σ.Out → Async Unit)
    (waiting : IO.Ref (Array (Bool × IO.Promise Bool))) : IO Unit := do
  let (start, outputs) := Kernel.boot sys
  rt.record (outputs.map .output)
  (handOver onOutput outputs).block
  let kernel ← IO.mkRef start
  repeat
    let now ← rt.now
    let wait ← kernel.modifyGet fun k => let k := k.advance now; (k.wait, k)
    match ← rt.take wait with
    | .closed => break
    | .nothing => pure ()
    | .command (.input x) =>
      rt.record (← kernel.modifyGet fun k => let r := k.accept x; (r.events, r.kernel))
    | .command (.idle timers done) => waiting.modify (·.push (timers, done))
    | .command (.peek i reply) => reply.resolve (← kernel.modifyGet fun k => ((k.cell i).state, k))
    let now ← rt.now
    let batch := max 1 rt.config.batch
    let (events, outputs, quiet, still) ← kernel.modifyGet fun k =>
      match (k.advance now).runBatch batch with
      | { kernel, events, outputs } =>
        ((events, outputs, kernel.quiet false, kernel.quiet true), kernel)
    rt.record events
    (handOver onOutput outputs).block
    let reached := fun (timers : Bool) => if timers then still else quiet
    for (timers, done) in ← waiting.get do
      if reached timers then done.resolve true
    waiting.modify (·.filter fun (timers, _) => !reached timers)

/-- However the loop ends, nobody is left waiting on it. -/
private def run (rt : Runtime sys) (onOutput : σ.Out → Async Unit) : IO Unit := do
  let waiting ← IO.mkRef #[]
  try rt.loop onOutput waiting
  catch e => discard (IO.eprintln s!"lanes: the shard stopped on an error: {e}").toBaseIO
  discard <| (rt.inbox.close : EIO _ Unit).toBaseIO
  for (_, done) in ← waiting.get do done.resolve false
  rt.finished.resolve ()

/-- Boot a system on one shard, which runs on a thread of its own until `stop`. A program whose
`main` returns without stopping its runtimes does not exit.

Each output goes to `onOutput`, and the shard waits for it: a slow handler holds every actor up,
and a handler must not call `input`, `idle`, `state` or `stop`, which wait for the shard.
`tryInput` is safe.

A timer counts from the clock reading at the start of the batch of work that armed it, so it
can fire early by as long as that batch took. Steps are pure and short, so this is small, but
nothing may depend on a timer not firing early: the semantics lets one fire at any moment. -/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ()) : Async (Runtime sys) := do
  let rt : Runtime sys := {
    config
    inbox := ← CloseableChannel.new (some config.inboxCapacity)
    log := ← IO.mkRef #[]
    epoch_ms := ← IO.monoMsNow
    finished := ← IO.Promise.new }
  discard <| IO.asTask (prio := .dedicated) (rt.run onOutput)
  return rt

private def send (rt : Runtime sys) (c : Cmd sys) : Async Unit := do
  match ← await (← rt.inbox.send c) with
  | .ok () => pure ()
  | .error _ => throw stopped

/-- Hand over an input, waiting while the inbox is full. Throws once the runtime has stopped. -/
def input (rt : Runtime sys) (x : σ.In) : Async Unit :=
  rt.send (.input x)

/-- Hand over an input if the inbox has room. `false` means nothing was accepted: the system is
busy or has stopped. -/
def tryInput (rt : Runtime sys) (x : σ.In) : Async Bool :=
  rt.inbox.trySend (.input x)

/-- Wait until everything handed over so far is handled and no message is queued. With
`timers`, also until no timer is pending. Throws if the runtime stops first. -/
def idle (rt : Runtime sys) (timers : Bool := false) : Async Unit := do
  let done ← IO.Promise.new
  rt.send (.idle timers done)
  unless (← await done.result?) == some true do throw stopped

/-- The events performed so far. Empty unless `Config.record` is on. -/
def trace (rt : Runtime sys) : BaseIO (Array (Event σ)) :=
  rt.log.get

/-- The current state of actor `i`. For tests; an application sends the actor a message. -/
def state (rt : Runtime sys) (i : σ.Id) : Async (sys.State i) := do
  have : Nonempty (sys.State i) := ⟨(sys.actor i).init⟩
  let reply ← IO.Promise.new
  rt.send (.peek i reply)
  let some state ← await reply.result? | throw stopped
  return state

/-- Stop, and return when the shard has ended. It takes no more commands, finishes those already
handed over and at most one more batch of work, then ends. Messages still queued between actors
are abandoned and pending timers never fire. -/
def stop (rt : Runtime sys) : Async Unit := do
  discard <| (rt.inbox.close : EIO _ Unit).toBaseIO
  discard <| await rt.finished.result?

end Runtime

end Lanes
