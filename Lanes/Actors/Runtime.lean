/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Lanes.Actors.KernelSound

/-!
The runtime is a shell around the kernel: one task that takes commands from an inbox, calls the
kernel, and carries out what the kernel asks. It decides nothing. Every decision is in
`Lanes.Kernel`, which is proved to follow `SysState.step`.

What is trusted here is small and stated: the inbox hands over each command once, the timer
wakes no earlier than asked, and this loop passes the kernel's results on unchanged. Actors do
not run in parallel with each other; parallelism comes from running more shards.

The inbox is bounded, which is the system's back-pressure: `input` waits for room and
`tryInput` refuses (rule 3.8).
-/

public section

namespace Lanes

open Std Std.Async

variable {σ : Signature}

structure Runtime.Config where
  /-- Inputs and fired timers wait here for the shard. When it is full, `tryInput` refuses. -/
  inboxCapacity : Nat := 1024
  /-- Kernel steps between two looks at the inbox, so that a busy shard still admits inputs. -/
  batch : Nat := 64
  /-- Keep the events performed, for tests. By `Kernel.run1_sound` they are a run of the
  semantics. -/
  record : Bool := false

private inductive Cmd (sys : System σ) where
  | input (x : σ.In)
  | timer (i : σ.Id) (msg : σ.Msg i) (token : Nat)
  | idle (timers : Bool) (done : IO.Promise Unit)
  | peek (i : σ.Id) (reply : IO.Promise (sys.State i))

structure Runtime (sys : System σ) [Hashable σ.Id] where
  private mk ::
  private config : Runtime.Config
  private inbox : CloseableChannel (Cmd sys)
  private log : IO.Ref (Array (Event σ))

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

private def record (rt : Runtime sys) (events : List (Event σ)) : BaseIO Unit := do
  if rt.config.record then rt.log.modify (· ++ events.toArray)

/-- Returns how many timers were armed. -/
private def carryOut (rt : Runtime sys) (onOutput : σ.Out → Async Unit)
    (commands : List (Kernel.Command σ)) : Async Nat := do
  let mut armed := 0
  for command in commands do
    match command with
    | .emit out =>
      try onOutput out
      catch e => IO.eprintln s!"lanes: output handler failed: {e}"
    | .arm i msg token delay_ms =>
      armed := armed + 1
      background do
        Async.sleep (.ofNat delay_ms)
        discard <| await (← rt.inbox.send (.timer i msg token))
  return armed

private def loop (rt : Runtime sys) (onOutput : σ.Out → Async Unit) (start : Kernel sys)
    (armedAtBoot : Nat) : Async Unit := do
  let mut k := start
  let mut armed := armedAtBoot
  let mut waiting : Array (Bool × IO.Promise Unit) := #[]
  repeat
    let command ← match ← rt.inbox.tryRecv with
      | some command => pure (some command)
      | none => if k.queue.isEmpty then await (← rt.inbox.recv) else pure none
    match command with
    | some (.input x) =>
      let r := k.accept x
      k := r.kernel
      rt.record r.events
    | some (.timer i msg token) =>
      armed := armed - 1
      let r := k.fire i msg token
      k := r.kernel
      rt.record r.events
      armed := armed + (← rt.carryOut onOutput r.commands)
    | some (.idle timers done) => waiting := waiting.push (timers, done)
    | some (.peek i reply) => reply.resolve (k.cell i).state
    | none => if k.queue.isEmpty then break
    for _ in [0:rt.config.batch] do
      let some r := k.run1 | break
      k := r.kernel
      rt.record r.events
      armed := armed + (← rt.carryOut onOutput r.commands)
    if k.queue.isEmpty then
      let quiet := armed == 0
      for (timers, done) in waiting do
        if !timers || quiet then done.resolve ()
      waiting := waiting.filter fun (timers, _) => timers && !quiet

/-- Boot a system on one shard. Each output goes to `onOutput`. -/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ()) : Async (Runtime sys) := do
  let rt : Runtime sys := {
    config
    inbox := ← CloseableChannel.new (some config.inboxCapacity)
    log := ← IO.mkRef #[] }
  let (kernel, commands) := Kernel.boot sys
  rt.record ((Kernel.outputs commands).map .output)
  let armed ← rt.carryOut onOutput commands
  background (rt.loop onOutput kernel armed)
  return rt

/-- Hand over an input, waiting while the inbox is full. -/
def input (rt : Runtime sys) (x : σ.In) : Async Unit := do
  discard <| await (← rt.inbox.send (.input x))

/-- Hand over an input if the inbox has room. `false` means the system is busy and nothing was
accepted. -/
def tryInput (rt : Runtime sys) (x : σ.In) : Async Bool :=
  rt.inbox.trySend (.input x)

/-- Wait until everything handed over so far is handled and no message is queued. With
`timers`, also until every armed timer has fired. -/
def idle (rt : Runtime sys) (timers : Bool := false) : Async Unit := do
  let done ← IO.Promise.new
  discard <| await (← rt.inbox.send (.idle timers done))
  await done

/-- The events performed so far. Empty unless `Config.record` is on. -/
def trace (rt : Runtime sys) : BaseIO (Array (Event σ)) :=
  rt.log.get

/-- The current state of actor `i`. For tests; an application sends the actor a message. -/
def state (rt : Runtime sys) (i : σ.Id) : Async (sys.State i) := do
  have : Nonempty (sys.State i) := ⟨(sys.actor i).init⟩
  let reply ← IO.Promise.new
  discard <| await (← rt.inbox.send (.peek i reply))
  await reply

/-- Stop taking commands. The shard finishes what is queued and ends. -/
def stop (rt : Runtime sys) : Async Unit := do
  discard <| (rt.inbox.close : EIO _ Unit).toBaseIO

end Runtime

end Lanes
