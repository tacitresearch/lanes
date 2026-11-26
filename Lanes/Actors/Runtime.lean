/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Lanes.Actors.Journal

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
  /-- With a journal that can save the kernel: how many entries to write between two saves.
  After a save the journal is cut, so this bounds how much a restart replays. -/
  snapshotEvery : Nat := 65536
  /-- Whether the shard is one of several (`Lanes.Cluster`). It then also takes inputs from the
  other shards, on a lane that is never full, so that two shards cannot block each other. -/
  clustered : Bool := false

/-- What a durable shard needs of its journal's storage. `Lanes.Journal.Store.open` gives one
backed by a file. -/
structure Journal.Log (sys : System σ) where
  /-- The entries in the journal at this start. -/
  past : List (Journal.Entry σ)
  /-- The kernel last saved, with the index of its mark in the journal. -/
  saved : Option (Nat × Kernel.Image sys) := none
  /-- How many entries the shard's history has at this start, counting those a cut journal no
  longer holds. It never goes down, and goes up with every entry written. -/
  index : Nat := past.length
  /-- Returns once the entries will survive the process. -/
  append : List (Journal.Entry σ) → IO Unit
  /-- Writes entries that may be lost with the process. -/
  note : List (Journal.Entry σ) → IO Unit
  /-- Save this image of the kernel as it is after everything appended so far, mark the journal
  and cut it. `none` if this journal cannot save. -/
  save : Option (Kernel.Image sys → IO Unit) := none
  close : IO Unit

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
  private peers : CloseableChannel (Cmd sys)
  private log : IO.Ref (Array (Event σ))
  private finished : IO.Promise (Option IO.Error)

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

private def stopped : IO.Error := IO.userError "lanes: the runtime has stopped"

private def record (rt : Runtime sys) (events : List (Event σ)) : BaseIO Unit := do
  if rt.config.record then rt.log.modify (· ++ events.toArray)

private def handOver (onOutput : σ.Out → Async Unit) (outputs : List σ.Out) : Async Unit := do
  for out in outputs do
    try onOutput out
    catch e => IO.eprintln s!"lanes: output handler failed: {e}"

/-- Blocks the calling thread, which is the shard's own. -/
private def take (rt : Runtime sys) (wait : Kernel.Wait) : IO (Taken sys) := do
  if rt.config.clustered then
    if let some c ← rt.peers.tryRecv then return .command c
  let taken := fun (c : Option (Cmd sys)) => match c with
    | some c => Taken.command c
    | none => .closed
  let command := fun (c : Option (Cmd sys)) => (pure (taken c) : Async (Taken sys))
  match wait with
  | .none =>
    match ← rt.inbox.tryRecv with
    | some c => return .command c
    | none => return if ← rt.inbox.isClosed then .closed else .nothing
  | .forever =>
    if rt.config.clustered then
      Async.block (Selectable.one #[
        .case rt.peers.recvSelector command, .case rt.inbox.recvSelector command])
    else return taken (← IO.wait (← rt.inbox.recv))
  | .for_ms ms => Async.block do
    let sources := #[.case rt.inbox.recvSelector command,
      .case (← Selector.sleep (.ofNat ms)) fun _ => pure .nothing]
    Selectable.one (if rt.config.clustered then sources.push (.case rt.peers.recvSelector command)
      else sources)

/--
The shard's loop, on a thread of its own. It is not an `Async` task, for a reason that no test
of behaviour shows: Lean never updates an object in place once another thread may see it, and
state held across an `await` is handed to the task system. A kernel kept that way is copied,
actor table and all, on every step (`Tests/Scale.lean`). Here it is created on this thread and
never leaves it; only commands, events and outputs cross.

What to ask of the kernel in one turn, and what to write in the journal for it, is
`Journal.turn`, a pure function proved to leave the kernel its journal entries describe
(`Journal.turns_kernel`). This loop reads the clock, takes a command, calls it, appends the
entries, and only then hands the outputs over. With a journal the kernel starts as the journal
describes (`Journal.resume`).

Saving the kernel is the kernel operation `snapshot`: the shard goes on with the kernel its
image restores, which is the kernel a restart from that image would have
(`Journal.resume_eq_recover`). It is done after a turn's outputs are handed over, because the
mark it leaves in the journal says they were.
-/
private def loop (rt : Runtime sys) (onOutput : σ.Out → Async Unit)
    (waiting : IO.Ref (Array (Bool × IO.Promise Bool))) (journal : Option (Journal.Log sys)) :
    IO Unit := do
  let (start, outputs) ← match journal with
    | some log =>
      match Journal.resume sys log.saved log.past with
      | some found => pure found
      | none => throw (IO.userError "lanes: the journal does not continue its snapshot")
    | none => pure (Kernel.boot sys)
  if journal.isNone then rt.record (outputs.map .output)
  let handOver := fun (outputs : List σ.Out) => do
    (handOver onOutput outputs).block
    if let some log := journal then unless outputs.isEmpty do log.note [.handed]
  handOver outputs
  let since := start.clock_ms
  let epoch ← IO.monoMsNow
  let clock : BaseIO Nat := return since + ((← IO.monoMsNow) - epoch)
  let kernel ← IO.mkRef start
  let fuel := max 1 rt.config.batch
  let mut written := (journal.map (·.past.length)).getD 0
  repeat
    let now ← clock
    let wait ← kernel.modifyGet fun k => ((k.advance now).wait, k)
    let mut input : Option σ.In := none
    match ← rt.take wait with
    | .closed => break
    | .nothing => pure ()
    | .command (.input x) => input := some x
    | .command (.idle timers done) => waiting.modify (·.push (timers, done))
    | .command (.peek i reply) => reply.resolve (← kernel.modifyGet fun k => ((k.cell i).state, k))
    let now ← clock
    let (events, outputs, entries, quiet, still) ← kernel.modifyGet fun k =>
      match Journal.turn k now input fuel with
      | { kernel, events, outputs, entries } =>
        ((events, outputs, entries, kernel.quiet false, kernel.quiet true), kernel)
    if let some log := journal then unless entries.isEmpty do log.append entries
    rt.record events
    handOver outputs
    written := written + entries.length
    if let some save := journal.bind (·.save) then
      if written ≥ max 1 rt.config.snapshotEvery then
        save (← kernel.modifyGet fun k => match k.image with | image => (image, image.kernel))
        written := 0
    let reached := fun (timers : Bool) => if timers then still else quiet
    for (timers, done) in ← waiting.get do
      if reached timers then done.resolve true
    waiting.modify (·.filter fun (timers, _) => !reached timers)

/-- However the loop ends, nobody is left waiting on it: not those it had heard from, and not
those whose commands it never took. -/
private def run (rt : Runtime sys) (onOutput : σ.Out → Async Unit)
    (journal : Option (Journal.Log sys)) : IO Unit := do
  let waiting ← IO.mkRef #[]
  let error ← (rt.loop onOutput waiting journal).toBaseIO
  if let .error e := error then
    discard (IO.eprintln s!"lanes: the shard stopped on an error: {e}").toBaseIO
  if let some log := journal then discard log.close.toBaseIO
  for channel in [rt.inbox, rt.peers] do
    discard <| (channel.close : EIO _ Unit).toBaseIO
    repeat
      match ← channel.tryRecv with
      | some (.idle _ done) => done.resolve false
      | some _ => pure ()
      | none => break
  for (_, done) in ← waiting.get do done.resolve false
  rt.finished.resolve (match error with | .error e => some e | .ok () => none)

/-- Boot a system on one shard, which runs on a thread of its own until `stop`. The handler is
given the runtime, so that an adapter can answer an output with an input (`tryInput`). A program whose
`main` returns without stopping its runtimes does not exit.

Each output goes to `onOutput`, and the shard waits for it: a slow handler holds every actor up,
and a handler must not call `input`, `idle`, `state` or `stop`, which wait for the shard.
`tryInput` is safe.

A timer counts from the clock reading at the start of the batch of work that armed it, so it
can fire early by as long as that batch took. Steps are pure and short, so this is small, but
nothing may depend on a timer not firing early: the semantics lets one fire at any moment.

With a `journal` the shard is durable: it starts in the state the journal describes, and every
input it accepts is in the journal before any output it causes is handed over. Outputs handed
over shortly before the process died may be handed over again, so a handler that must not
repeat itself has to tell. The kernel's clock stands still while the process is down. -/
def startWith (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : Runtime sys → σ.Out → Async Unit)
    (journal : Option (Journal.Log sys) := none) : Async (Runtime sys) := do
  let rt : Runtime sys := {
    config
    inbox := ← CloseableChannel.new (some config.inboxCapacity)
    peers := ← CloseableChannel.new
    log := ← IO.mkRef #[]
    finished := ← IO.Promise.new }
  discard <| IO.asTask (prio := .dedicated) (rt.run (onOutput rt) journal)
  return rt

/-- `startWith` for a handler that only consumes outputs. -/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (journal : Option (Journal.Log sys) := none) : Async (Runtime sys) :=
  startWith sys config (fun _ => onOutput) journal

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

/-- Hand over an input from another shard. It is never refused for want of room; `false` means
the shard has stopped. -/
def peer (rt : Runtime sys) (x : σ.In) : BaseIO Bool :=
  rt.peers.trySend (.input x)

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

/-- Wait until the shard has ended, and say whether an error ended it. A shard ends on an error
when its journal cannot be written: it must not hand over outputs it could not make durable.
Whoever owns the shard should then end the process, so that it is started again. -/
def ended (rt : Runtime sys) : Async (Option IO.Error) := do
  return (← await rt.finished.result?).join

end Runtime

end Lanes
