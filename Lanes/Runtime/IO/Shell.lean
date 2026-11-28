/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Lanes.Runtime.Batch
public import Lanes.Runtime.Mailbox
public import Lanes.Runtime.Pace
public import Lanes.Runtime.IO.Park

/-!
The runtime is a shell around the kernel: one task that takes commands from an inbox, tells the
kernel the time, lets it work, and hands its outputs on. Which message is next, which timers
are due, how long to sleep and when the shard is idle are the kernel's answers
(`Lanes.Kernel`), not decisions made here.

By `Kernel.exec_reachable` nothing this loop does can take the system outside the semantics.
What is trusted is that it hands outputs on as the kernel gave them. Unless `parallel` is off or
there is one worker, the inputs that arrive together are accepted together and the steps of the
actors they reach may be worked out in parallel, which changes nothing the kernel does
(`Kernel.runWaves_eq`). With `auto` whether they are is `Pace`'s choice, from this loop's timing
of the batches before; it is trusted only to be fast, since no spread changes a batch
(`Batch.run_spread`).

The inbox is bounded, which is the system's back-pressure: `input` waits for room and
`tryInput` refuses (rule 3.8).
-/

public section

namespace Lanes

open Std Std.Async

variable {σ : Signature}

/-- Whether the actors a turn reaches step in parallel. -/
inductive Runtime.Parallel where
  | off
  /-- Every wave with mail for more than one actor (D64). -/
  | on
  /-- A batch at a time, as `Pace` chooses from how long the batches before it took. -/
  | auto
  deriving DecidableEq, Repr

/-- How many batches that did work ran on the shard's thread, and how many on the pool. -/
structure Runtime.Batches where
  inline : Nat := 0
  pool : Nat := 0
  deriving Repr

/-- How a shard runs: its bounds and its threads. Every field has a default. -/
structure Runtime.Config where
  /-- Inputs wait here for the shard. When it is full, `tryInput` refuses. At least one. -/
  inboxCapacity : Nat := 1024
  /-- Units of kernel work between two looks at the inbox, so that a busy shard still admits
  inputs. At least one is done. -/
  batch : Nat := 64
  /-- Keep the events performed, for tests. By `Kernel.exec_reachable` they are a run of the
  semantics, but for the starts that bring released actors back. -/
  record : Bool := false
  /-- The most threads that work out the steps of different actors at once (`Kernel.runWaves`);
  `0` is the machine's hardware threads. With one, or with `parallel` off, each input is a turn
  of its own, as the kernel was always run; otherwise the inputs that arrive together are one
  turn, at most `batch` to a turn, and the actors they reach may step in
  parallel. -/
  workers : Nat := 0
  parallel : Runtime.Parallel := .auto
  /-- What `auto` counts as worth the pool. -/
  pace : Pace.Config := {}

private abbrev Cmd (sys : System σ) :=
  Batch.Command σ (fun ids => IO.Promise (Batch.Peek sys ids)) (IO.Promise Bool)

instance {sys : System σ} {ids : List σ.Id} : Nonempty (Batch.Peek sys ids) :=
  ⟨{ states := ids.map fun i => ⟨i, (sys.actor i).init⟩
     ids_eq := by simp [List.map_map, Function.comp_def] }⟩

/-- Who is woken when the inbox changes: the shard, which parks, or a sender waiting for room. -/
private inductive Wake where
  | shard
  | sender (room : IO.Promise Unit)

/-- A running shard: `sys` executed by the kernel on a thread of its own. Start one with
`Runtime.start` or `Runtime.startWith`, hand it inputs with `input` or `tryInput`, and end it
with `stop`. By `Kernel.exec_reachable`, nothing it does takes the system outside the
semantics. -/
structure Runtime (sys : System σ) [Hashable σ.Id] where
  private mk ::
  private config : Runtime.Config
  private inbox : IO.Ref (Mailbox (Cmd sys) Wake)
  private parker : Parker
  private log : IO.Ref (Array (Event σ))
  private ran : IO.Ref Runtime.Batches
  private finished : IO.Promise (Option IO.Error)
  private recovered : IO.Ref Bool

private initialize live : IO.Ref Nat ← IO.mkRef 0

/-- How many shards are running in this process. A shard that is started and never stopped
keeps the process from ending, so a program, and a test, can ask. -/
def Runtime.running : BaseIO Nat :=
  live.get

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

private def stopped : IO.Error := IO.userError "lanes: the runtime has stopped"

private def wake (rt : Runtime sys) : Wake → BaseIO Unit
  | .shard => rt.parker.unpark
  | .sender room => room.resolve ()

private def record (rt : Runtime sys) (events : List (Event σ)) : BaseIO Unit := do
  if rt.config.record then rt.log.modify (· ++ events.toArray)

private def handOver (onOutput : σ.Out → Async Unit) (outputs : List σ.Out) : Async Unit := do
  for out in outputs do
    try onOutput out
    catch e => IO.eprintln s!"lanes: output handler failed: {e}"

/-- Everything that has arrived, and whether the inbox is closed. If nothing has and the
kernel has nothing to do, the calling thread, which is the shard's own, parks until something
arrives or `wait` has passed. It may wake early; the loop then asks the kernel again. -/
private def take (rt : Runtime sys) (wait : Kernel.Wait) : IO (List (Cmd sys) × Bool) := do
  let grab : BaseIO (List (Cmd sys) × Bool) := do
    let taken ← rt.inbox.modifyGet Mailbox.take
    for w in taken.wake do rt.wake w
    return (taken.batch, taken.closed)
  let (batch, closed) ← grab
  if wait == .none || closed || !batch.isEmpty then return (batch, closed)
  if ← rt.inbox.modifyGet (Mailbox.rest .shard) then
    match wait with
    | .for_ms ms => rt.parker.parkAtMost ms
    | _ => rt.parker.park
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
other threads for however many inputs arrived together. The kernel starts at boot: a shard's
state lives as long as its process.
-/
private def loop (rt : Runtime sys) (onOutput : σ.Out → Async Unit)
    (waiting : IO.Ref (Array (Bool × IO.Promise Bool))) : IO Unit := do
  let (start, outputs) := Kernel.boot sys
  rt.record (outputs.map .output)
  let handOver := fun (outputs : List σ.Out) => do
    discard <| Parker.wait (← (handOver onOutput outputs).toBaseIO)
  handOver outputs
  rt.recovered.set true
  let since := start.clock_ms
  let epoch ← IO.monoMsNow
  let clock : BaseIO Nat := return since + ((← IO.monoMsNow) - epoch)
  let kernel ← IO.mkRef start
  let workers := match rt.config.workers with
    | 0 => (System.Platform.Internal.getHardwareConcurrency ()).toNat
    | n => n
  let parallel := if workers ≤ 1 then .off else rt.config.parallel
  let mut pace : Pace := {}
  let mut worked_ns ← IO.monoNanosNow
  repeat
    let now ← clock
    let wait ← kernel.modifyGet fun k => ((k.advance now).wait, k)
    let (batch, closed) ← rt.take wait
    if batch.isEmpty && closed then break
    let spread : Kernel.Spread := match parallel with
      | .off => {}
      | .on => { workers }
      | .auto => pace.spread rt.config.pace workers
    let config : Batch.Config := { now_ms := ← clock, fuel := max 1 rt.config.batch, spread }
    let held ← waiting.get
    -- Peeks are answered at the end of the batch wherever they fall (`Batch.run_erase_peeks`), so
    -- they are put last, where they do not part inputs that are accepted together.
    let batch := if parallel == .off then batch
      else Batch.group (max 1 rt.config.batch) (batch.filter (!·.isPeek)) ++ batch.filter (·.isPeek)
    let start_ns ← IO.monoNanosNow
    let (acts, resolved, still) ← kernel.modifyGet fun k =>
      match Batch.run config k held batch with
      | { kernel, acts, resolved, waiting } => ((acts, resolved, waiting), kernel)
    let units := Pace.work acts
    if units != 0 then
      if parallel == .auto then
        let end_ns ← IO.monoNanosNow
        pace := pace.observe rt.config.pace workers spread (end_ns - start_ns) units
          (end_ns - worked_ns)
        worked_ns := end_ns
      rt.ran.modify fun b =>
        if 1 < spread.workers then { b with pool := b.pool + 1 }
        else { b with inline := b.inline + 1 }
    for act in acts do
      match act with
      | .work _ => pure ()
      | .record events => rt.record events.toList
      | .handOver outputs => handOver outputs.toList
      | .answer _ reply peek => reply.resolve peek
    for heard in resolved do heard.resolve true
    waiting.set still

/-- However the loop ends, nobody is left waiting on it: not those it had heard from, and not
those whose commands it never took. Those are taken out of the inbox and dropped, and a caller
waits on a promise that answers when it is dropped. The inbox is closed first: nothing is
accepted by a shard that has ended. -/
private def run (rt : Runtime sys) (onOutput : σ.Out → Async Unit) : IO Unit := do
  let waiting ← IO.mkRef #[]
  let error ← (rt.loop onOutput waiting).toBaseIO
  if let .error e := error then
    discard (IO.eprintln s!"lanes: the shard stopped on an error: {e}").toBaseIO
  for w in ← rt.inbox.modifyGet Mailbox.close do rt.wake w
  discard <| rt.inbox.modifyGet Mailbox.take
  for (_, done) in ← waiting.get do done.resolve false
  live.modify (· - 1)
  rt.finished.resolve (match error with | .error e => some e | .ok () => none)

/-- Boot a system on one shard, which runs on a thread of its own until `stop`. The handler is
given the runtime, so that an adapter can answer an output with an input (`tryInput`). A
program whose `main` returns without stopping its runtimes does not exit.

Each output goes to `onOutput`, and the shard waits for it: a slow handler holds every actor up,
and a handler must not call `input`, `idle`, `state` or `stop`, which wait for the shard.
`tryInput` is safe.

A timer counts from the clock reading at the start of the batch of work that armed it, so it
can fire early by as long as that batch took. Steps are pure and short, so this is small, but
nothing may depend on a timer not firing early: the semantics lets one fire at any moment.

The shard's state lives as long as its process: every start is a boot, with every actor in its
initial state. State that must outlive the process belongs in a service outside, reached
through an adapter. -/
def startWith (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : Runtime sys → σ.Out → Async Unit) : Async (Runtime sys) := do
  let rt : Runtime sys := {
    config
    inbox := ← IO.mkRef {}
    parker := ← Parker.new
    log := ← IO.mkRef #[]
    ran := ← IO.mkRef {}
    finished := ← IO.Promise.new
    recovered := ← IO.mkRef false }
  live.modify (· + 1)
  discard <| IO.asTask (prio := .dedicated) (rt.run (onOutput rt))
  return rt

/-- `startWith` for a handler that only consumes outputs. -/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ()) : Async (Runtime sys) :=
  startWith sys config (fun _ => onOutput)

private def capacity (rt : Runtime sys) : Nat :=
  max 1 rt.config.inboxCapacity

private def offer (rt : Runtime sys) (c : Cmd sys) : BaseIO Bool := do
  match ← rt.inbox.modifyGet (Mailbox.offer rt.capacity c) with
  | .taken wake =>
    if let some w := wake then rt.wake w
    return true
  | _ => return false

/-- Waits while the inbox is full. The wait is rare and the offer is not, and making a promise
to wait on costs far more than an offer, so the offer is tried first. -/
private def send (rt : Runtime sys) (c : Cmd sys) : Async Unit := do
  if ← rt.offer c then return
  repeat
    let room ← IO.Promise.new
    match ← rt.inbox.modifyGet (Mailbox.offerOrWait rt.capacity c (.sender room)) with
    | .taken wake =>
      if let some w := wake then rt.wake w
      return
    | .closed => throw stopped
    | .full => discard <| await room.result?

/-- Hand over an input, waiting while the inbox is full. Throws once the runtime has stopped. -/
def input (rt : Runtime sys) (x : σ.In) : Async Unit :=
  rt.send (.input x)

/-- Hand over an input if the inbox has room. `false` means nothing was accepted: the system is
busy or has stopped. -/
def tryInput (rt : Runtime sys) (x : σ.In) : BaseIO Bool :=
  rt.offer (.input x)

/-- Wait until everything handed over so far is handled and no message is queued. With
`timers`, also until no timer is pending. Throws if the runtime stops first. -/
def idle (rt : Runtime sys) (timers : Bool := false) : Async Unit := do
  let done ← IO.Promise.new
  rt.send (.idle timers done)
  unless (← await done.result?) == some true do throw stopped

/-- How many batches have run on the shard's thread and how many on the pool. -/
def batches (rt : Runtime sys) : BaseIO Runtime.Batches :=
  rt.ran.get

/-- The events performed so far. Empty unless `Config.record` is on. -/
def trace (rt : Runtime sys) : BaseIO (Array (Event σ)) :=
  rt.log.get

/-- The state of actor `i` at the end of the batch that takes this, waiting while the inbox is
full. For tests; an application reads with `tryPeek`. -/
def state (rt : Runtime sys) (i : σ.Id) : Async (sys.State i) := do
  let reply ← IO.Promise.new
  rt.send (.peek [i] (fun _ => false) reply)
  let some peek ← await reply.result? | throw stopped
  return peek.get i List.mem_cons_self

/-- Ask for the states of the actors `ids` if the inbox has room, without waiting. They are read
at the end of the batch that takes the peek, once everything that batch and those before it
produced is handed over (`Batch.run_sound`), with every request before that boundary and none
after it (`Batch.run_peeks`), and nothing else the batch does changes (`Batch.run_erase_peeks`).
With `every`, the states of every actor started that it holds of are read too
(`Batch.Peek.others`). `reply` is given them on a task of its own, or `none` if the shard stops
first. `false` means nothing was asked: the shard is busy or has stopped.

The states are then shared with that task: an actor stepped before the task lets go of its
state starts from a copy of it. -/
def tryPeek (rt : Runtime sys) (ids : List σ.Id) (reply : Option (Batch.Peek sys ids) → BaseIO Unit)
    (every : σ.Id → Bool := fun _ => false) : BaseIO Bool := do
  let promise ← IO.Promise.new
  unless ← rt.offer (.peek ids every promise) do return false
  discard <| BaseIO.mapTask (t := promise.result?) reply
  return true

/-- Stop, and return when the shard has ended. It takes no more commands, finishes those already
handed over and at most one more batch of work, then ends. Messages still queued between actors
are abandoned and pending timers never fire. -/
def stop (rt : Runtime sys) : Async Unit := do
  for w in ← rt.inbox.modifyGet Mailbox.close do rt.wake w
  discard <| await rt.finished.result?

/-- Whether the shard has started: booted and handed over what booting put out. -/
def hasRecovered (rt : Runtime sys) : BaseIO Bool :=
  rt.recovered.get

/-- The commands waiting in the inbox. -/
def depth (rt : Runtime sys) : BaseIO Nat :=
  rt.inbox.modifyGet fun m => (m.count, m)

/-- Wait until the shard has ended, and say whether an error ended it. Whoever owns the shard
should then end the process, so that it is started again. -/
def ended (rt : Runtime sys) : Async (Option IO.Error) := do
  return (← await rt.finished.result?).join

end Runtime

end Lanes
