/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Lanes.Actors.Batch
public import Lanes.Actors.Mailbox

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
  /-- Inputs wait here for the shard. When it is full, `tryInput` refuses. At least one. -/
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

private abbrev Cmd (sys : System σ) :=
  Batch.Command σ (fun i => IO.Promise (sys.State i)) (IO.Promise Bool)

structure Runtime (sys : System σ) [Hashable σ.Id] where
  private mk ::
  private config : Runtime.Config
  private inbox : IO.Ref (Mailbox (Cmd sys) (IO.Promise Unit))
  private log : IO.Ref (Array (Event σ))
  private finished : IO.Promise (Option IO.Error)

private initialize live : IO.Ref Nat ← IO.mkRef 0

/-- How many shards are running in this process. A shard that is started and never stopped
keeps the process from ending, so a program, and a test, can ask. -/
def Runtime.running : BaseIO Nat :=
  live.get

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

private def stopped : IO.Error := IO.userError "lanes: the runtime has stopped"

private def record (rt : Runtime sys) (events : List (Event σ)) : BaseIO Unit := do
  if rt.config.record then rt.log.modify (· ++ events.toArray)

private def handOver (onOutput : σ.Out → Async Unit) (outputs : List σ.Out) : Async Unit := do
  for out in outputs do
    try onOutput out
    catch e => IO.eprintln s!"lanes: output handler failed: {e}"

/-- Everything that has arrived, and whether the inbox is closed. If nothing has and the
kernel has nothing to do, the calling thread, which is the shard's own, sleeps until something
arrives or `wait` has passed. -/
private def take (rt : Runtime sys) (wait : Kernel.Wait) : IO (List (Cmd sys) × Bool) := do
  let grab : BaseIO (List (Cmd sys) × Bool) := do
    let taken ← rt.inbox.modifyGet Mailbox.take
    for room in taken.wake do room.resolve ()
    return (taken.batch, taken.closed)
  let (batch, closed) ← grab
  if wait == .none || closed || !batch.isEmpty then return (batch, closed)
  let wake ← IO.Promise.new
  if ← rt.inbox.modifyGet (Mailbox.rest wake) then
    match wait with
    | .for_ms ms => Async.block do
      let sleep ← Sleep.mk (.ofNat ms)
      Async.race (discard <| await wake.result?) sleep.wait
      sleep.stop
    | _ => discard <| IO.wait wake.result?
  grab

/--
The shard's loop, on a thread of its own. It is not an `Async` task, for a reason that no test
of behaviour shows: Lean never updates an object in place once another thread may see it, and
state held across an `await` is handed to the task system. A kernel kept that way is copied,
actor table and all, on every step (`Tests/Scale.lean`). Here it is created on this thread and
never leaves it; only commands, events and outputs cross.

What to do with the commands taken at once is `Batch.run`, a pure function with its theorems:
the turns it asks of the kernel, and the acts to perform for them, in order. This loop reads
the clock, takes every command that has arrived, and performs the acts: one exchange with the
other threads and one write to the journal for however many inputs arrived together. With a
journal the kernel starts as the journal describes (`Journal.resume`).
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
  let save := journal.bind (·.save)
  let snapshotEvery := save.map fun _ => rt.config.snapshotEvery
  let mut written := (journal.map (·.past.length)).getD 0
  repeat
    let now ← clock
    let wait ← kernel.modifyGet fun k => ((k.advance now).wait, k)
    let (batch, closed) ← rt.take wait
    if batch.isEmpty && closed then break
    let config : Batch.Config := { now_ms := ← clock, fuel := max 1 rt.config.batch, snapshotEvery }
    let held ← waiting.get
    let (acts, resolved, still, count) ← kernel.modifyGet fun k =>
      match Batch.run config k written held batch with
      | { kernel, written, acts, resolved, waiting } => ((acts, resolved, waiting, written), kernel)
    written := count
    for act in acts do
      match act with
      | .append entries => if let some log := journal then log.append entries.toList
      | .record events => rt.record events.toList
      | .handOver outputs => handOver outputs.toList
      | .save image => if let some save := save then save image
      | .answer _ reply state => reply.resolve state
    for heard in resolved do heard.resolve true
    waiting.set still

/-- However the loop ends, nobody is left waiting on it: not those it had heard from, and not
those whose commands it never took. Those are taken out of the inbox and dropped, and a caller
waits on a promise that answers when it is dropped. The inbox is closed first, before the
journal, which may take its time: nothing is accepted by a shard that has ended. -/
private def run (rt : Runtime sys) (onOutput : σ.Out → Async Unit)
    (journal : Option (Journal.Log sys)) : IO Unit := do
  let waiting ← IO.mkRef #[]
  let error ← (rt.loop onOutput waiting journal).toBaseIO
  if let .error e := error then
    discard (IO.eprintln s!"lanes: the shard stopped on an error: {e}").toBaseIO
  for wake in ← rt.inbox.modifyGet Mailbox.close do wake.resolve ()
  discard <| rt.inbox.modifyGet Mailbox.take
  if let some log := journal then discard log.close.toBaseIO
  for (_, done) in ← waiting.get do done.resolve false
  live.modify (· - 1)
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
    inbox := ← IO.mkRef {}
    log := ← IO.mkRef #[]
    finished := ← IO.Promise.new }
  live.modify (· + 1)
  discard <| IO.asTask (prio := .dedicated) (rt.run (onOutput rt) journal)
  return rt

/-- `startWith` for a handler that only consumes outputs. -/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (journal : Option (Journal.Log sys) := none) : Async (Runtime sys) :=
  startWith sys config (fun _ => onOutput) journal

private def capacity (rt : Runtime sys) : Nat :=
  max 1 rt.config.inboxCapacity

private def offer (rt : Runtime sys) (c : Cmd sys) : BaseIO Bool := do
  match ← rt.inbox.modifyGet (Mailbox.offer rt.capacity c) with
  | .taken wake =>
    if let some wake := wake then wake.resolve ()
    return true
  | _ => return false

/-- Waits while the inbox is full. The wait is rare and the offer is not, and making a promise
to wait on costs far more than an offer, so the offer is tried first. -/
private def send (rt : Runtime sys) (c : Cmd sys) : Async Unit := do
  if ← rt.offer c then return
  repeat
    let room ← IO.Promise.new
    match ← rt.inbox.modifyGet (Mailbox.offerOrWait rt.capacity c room) with
    | .taken wake =>
      if let some wake := wake then wake.resolve ()
      return
    | .closed => throw stopped
    | .full => discard <| await room.result?

/-- Hand over an input, waiting while the inbox is full. Throws once the runtime has stopped. -/
def input (rt : Runtime sys) (x : σ.In) : Async Unit :=
  rt.send (.input x)

/-- Hand over an input if the inbox has room. `false` means nothing was accepted: the system is
busy or has stopped. -/
def tryInput (rt : Runtime sys) (x : σ.In) : Async Bool :=
  rt.offer (.input x)

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
  for wake in ← rt.inbox.modifyGet Mailbox.close do wake.resolve ()
  discard <| await rt.finished.result?

/-- Wait until the shard has ended, and say whether an error ended it. A shard ends on an error
when its journal cannot be written: it must not hand over outputs it could not make durable.
Whoever owns the shard should then end the process, so that it is started again. -/
def ended (rt : Runtime sys) : Async (Option IO.Error) := do
  return (← await rt.finished.result?).join

end Runtime

end Lanes
