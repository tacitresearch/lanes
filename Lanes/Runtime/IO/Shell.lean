/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Std.Time
public import Lanes.Runtime.Peek
public import Lanes.Runtime.Sched
public import Lanes.Runtime.IO.Park

/-!
The runtime runs a system's actors free, on worker threads, as Go and Tokio run theirs. Each
actor has a slot (`Sched.Slot`) in a reference of its own: its state, its mailbox, and whether
it is idle, on a run queue or running. Each worker has a run queue of actors with mail; it takes
the first, or steals one from another worker's queue when its own is empty, steps it on up to
`budget` items of its mailbox, and lets it go. An actor runs on one worker at a time, and its
messages are handled in the order they reached it.

What to do is decided by the pure functions of `Lanes.Runtime.Sched`, called under the slot's
reference; this file only moves data between threads. `Sched.Run.reachable` proves that every
run of the scheduler's model is a run of the semantics; what is trusted is that the threads
here perform the model's transitions (`TRUSTED.md`, which says how each is atomic).

- A step takes the item and the state out of the slot, runs the step function outside any lock,
  and puts the result back; other threads only push to the slot meanwhile, which commutes with
  both (`Sched.Slot.take_push`, `Sched.Slot.put_push`).
- The messages a step sends are pushed before the actor is let go of, so the messages of a link
  arrive in order.
- A step that sends takes a shared lock from before it writes back until its last push; a step
  that stops its actor takes it alone. So no message to an actor that stops is between a step
  and its push, which the model asks (`Sched.Step.step`).
- Timers are kept on an agenda by a thread of their own, which pushes each to its actor when it
  is due. One that was cancelled or armed again is dropped when its actor takes it.
- The inbox is bounded: at most `inboxCapacity` inputs wait for their actor (`Sched.Ledger`),
  and `input` waits for room while `tryInput` refuses (rule 3.8).
- Each step is told the moment (D101): the time, the wall clock read at the start plus the
  monotonic time since, and a seed from its worker's generator, seeded from the operating
  system. The record has the moment as a tick before the step, so a replay gives each step what
  it was told (`Sched.Step.step`).
-/

public section

namespace Lanes

open Std Std.Async

variable {σ : Signature}

/-- How a runtime runs: its bounds and its threads. Every field has a default. -/
structure Runtime.Config where
  /-- Inputs accepted that their actor has not taken. When there are this many, `tryInput`
  refuses. At least one. -/
  inboxCapacity : Nat := 1024
  /-- Items a worker handles for one actor before it lets go of it, so that a busy actor does
  not keep others waiting. At least one. -/
  budget : Nat := 64
  /-- Keep the events performed, for tests. By `Sched.Run.reachable` they are a run of the
  semantics. -/
  record : Bool := false
  /-- Worker threads; `0` is the machine's hardware threads. -/
  workers : Nat := 0

namespace Runtime

/-- An actor's slot, and the readers waiting for its state while a worker holds it. A box
retired is on its way out of the table, at rest: whoever finds it looks again. -/
structure Box (sys : System σ) (i : σ.Id) where
  slot : Sched.Slot sys i
  readers : List (IO.Promise (sys.State i)) := []
  retired : Bool := false

/-- What every thread shares besides the actors: the inputs waiting, the counts that say when
the system is idle, and who waits on them. -/
abbrev Ledger := Sched.Ledger (IO.Promise Unit) (IO.Promise Bool)

end Runtime

private def shards : Nat := 64

/-- A running system. Start one with `Runtime.start` or `Runtime.startWith`, hand it inputs with
`input` or `tryInput`, and end it with `stop`. By `Sched.Run.reachable`, nothing it does takes
the system outside the semantics. -/
structure Runtime (sys : System σ) [Hashable σ.Id] where
  private mk ::
  private config : Runtime.Config
  private workers : Nat
  private boxes : { a : Array (IO.Ref (Std.DHashMap σ.Id fun i => IO.Ref (Runtime.Box sys i))) //
    0 < a.size }
  private queues : Array (IO.Ref (Fifo σ.Id))
  private parkers : Array Parker
  private sleepers : IO.Ref (List Nat)
  private ledger : IO.Ref Runtime.Ledger
  /-- The timers armed, by when they are due and the order they were armed in. -/
  private agenda : IO.Ref (Std.TreeMap Kernel.Due ((i : σ.Id) × σ.Msg i × Kernel.Due))
  private alarms : IO.Ref Nat
  private timer : Parker
  /-- Taken shared by a step that sends, from its write-back to its last push, and alone by a
  step that stops its actor. -/
  private sending : Std.BaseSharedMutex
  /-- Held while an input is recorded and pushed, and while a step is written back and recorded,
  when `record` is on, so that the record orders them as they happened. -/
  private recording : Std.BaseMutex
  private log : IO.Ref (Array (Event σ))
  private stopping : IO.Ref Bool
  private finished : IO.Promise (Option IO.Error)
  private recovered : IO.Ref Bool
  /-- The monotonic clock at the start. -/
  private epoch : Nat
  /-- The wall clock at the start, in milliseconds since the Unix epoch. -/
  private wall : Nat
  /-- Each worker's generator of seeds. -/
  private seeds : Array (IO.Ref UInt64)
  private nextHome : IO.Ref Nat

private initialize live : IO.Ref Nat ← IO.mkRef 0

/-- How many runtimes are running in this process. A runtime that is started and never stopped
keeps the process from ending, so a program, and a test, can ask. -/
def Runtime.running : BaseIO Nat :=
  live.get

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

private def stopped : IO.Error := IO.userError "lanes: the runtime has stopped"

/-- The time, in milliseconds since the Unix epoch: the wall clock at the start, then the
monotonic clock, so that setting the wall clock back while the runtime runs changes nothing. -/
private def clock (rt : Runtime sys) : BaseIO Nat :=
  return rt.wall + ((← IO.monoMsNow) - rt.epoch)

/-- SplitMix64 (Steele, Lea and Flood, 2014): the next state of a generator, and its output. -/
private def splitMix (x : UInt64) : UInt64 × UInt64 :=
  let x := x + 0x9E3779B97F4A7C15
  let z := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (x, z ^^^ (z >>> 31))

/-- The moment worker `w` tells its next step: the time and a seed from its own generator. -/
private def moment (rt : Runtime sys) (w : Nat) : BaseIO Moment := do
  let now_ms ← rt.clock
  let seed ← match rt.seeds[w]? with
    | some g => g.modifyGet fun x => match splitMix x with | (x, out) => (out, x)
    | none => pure 0
  return { now_ms, seed }

private def record (rt : Runtime sys) (events : List (Event σ)) : BaseIO Unit := do
  if rt.config.record then rt.log.modify (· ++ events.toArray)

private def shardOf (rt : Runtime sys) (i : σ.Id) :
    IO.Ref (Std.DHashMap σ.Id fun i => IO.Ref (Box sys i)) :=
  rt.boxes.1[(hash i).toNat % rt.boxes.1.size]'(Nat.mod_lt _ rt.boxes.2)

/-- The box of `i`, made the first time it is asked for. -/
private def box (rt : Runtime sys) (i : σ.Id) : BaseIO (IO.Ref (Box sys i)) := do
  let shard := rt.shardOf i
  if let some b := (← shard.get).get? i then return b
  let fresh ← IO.mkRef ({ slot := Sched.Slot.fresh sys i } : Box sys i)
  shard.modifyGet fun t =>
    match t.get? i with
    | some b => (b, t)
    | none => (fresh, t.insert i fresh)

/-- Wake a worker asleep, if any, to look for work. -/
private def wakeOne (rt : Runtime sys) : BaseIO Unit := do
  let w? ← rt.sleepers.modifyGet fun
    | [] => (none, [])
    | w :: rest => (some w, rest)
  if let some w := w? then
    if let some p := rt.parkers[w]? then p.unpark

private def enqueue (rt : Runtime sys) (w : Nat) (i : σ.Id) : BaseIO Unit := do
  if let some q := rt.queues[w % rt.workers]? then q.modify (·.push i)
  rt.wakeOne

/-- Push `x` to `i`'s mailbox, and put `i` on worker `w`'s run queue if it was idle. A box
retired is about to leave the table, so the push looks again until it has. -/
private def pushTo (rt : Runtime sys) (w : Nat) (i : σ.Id) (x : Sched.Item σ i) : BaseIO Unit := do
  repeat
    let b ← rt.box i
    let pushed ← b.modifyGet fun bx =>
      if bx.retired then (none, bx)
      else match bx.slot.push x with | (q, s) => (some q, { bx with slot := s })
    match pushed with
    | some true => rt.enqueue w i; return
    | some false => return
    | none => IO.sleep 0

/-- The worker whose run queue an input from outside joins: they take turns. -/
private def home (rt : Runtime sys) : BaseIO Nat :=
  rt.nextHome.modifyGet fun n => (n, n + 1)

private def ledgerDo {α : Type} (rt : Runtime sys) (f : Ledger → α × Ledger) : BaseIO α :=
  rt.ledger.modifyGet f

private def handOver (onOutput : σ.Out → Async Unit) (outputs : List σ.Out) : BaseIO Unit := do
  for out in outputs do
    match ← Parker.wait (← (onOutput out).toBaseIO) with
    | .ok () => pure ()
    | .error e => discard (IO.eprintln s!"lanes: output handler failed: {e}").toBaseIO

private def arm (rt : Runtime sys) (i : σ.Id) (armed : List (σ.Msg i × Kernel.Due)) :
    BaseIO Unit := do
  for (msg, due) in armed do
    let n ← rt.alarms.modifyGet fun n => (n, n + 1)
    let key : Kernel.Due := ⟨due.deadline_ms, n⟩
    let earliest ← rt.agenda.modifyGet fun a =>
      (a.minKey?.all (fun k => compare key k == .lt), a.insert key ⟨i, msg, due⟩)
    if earliest then rt.timer.unpark

/-- The timers' thread: push every timer due to its actor, then sleep until the next. -/
private def ring (rt : Runtime sys) : IO Unit := do
  repeat
    if ← rt.stopping.get then break
    let now ← rt.clock
    let due ← rt.agenda.modifyGet fun a =>
      let ready := a.toList.takeWhile (·.1.deadline_ms ≤ now)
      (ready.map (·.2), ready.foldl (fun a e => a.erase e.1) a)
    for ⟨i, msg, d⟩ in due do
      rt.ledgerDo fun l => ((), l.pushed 1)
      rt.pushTo (← rt.home) i (.timer msg d)
    match (← rt.agenda.get).minKey? with
    | some first =>
      let now ← rt.clock
      if now < first.deadline_ms then rt.timer.parkAtMost (first.deadline_ms - now)
    | none => rt.timer.park

private def answer (readers : List (IO.Promise (sys.State i))) (state : sys.State i) :
    BaseIO Unit := do
  for r in readers do r.resolve state

/-- Whether the workers are to end: the runtime is stopping, and every input it took has
been taken by its actor. -/
private def ending (rt : Runtime sys) : BaseIO Bool := do
  if ← rt.stopping.get then return (← rt.ledger.get).inputs == 0
  return false

/-- What the steps of a turn did to the ledger's counts, given to it once at the turn's end: the
items taken off or dropped, and the pending timers before and after. -/
private structure Tally where
  gone : Nat := 0
  before : Nat := 0
  after : Nat := 0

/-- One step of `i`, which worker `w` holds, with `held` the state it kept from the step before:
`none` when the mailbox was empty, else the state to keep and what the step did to the counts. A state kept in the worker's hands
between two steps is updated in place; one written back to the slot is seen by other threads,
and Lean copies it at its next update. So it goes back to the slot only when the worker lets go
of the actor, which nothing can tell: no other thread reads the state of an actor held. -/
private def step (rt : Runtime sys) (w : Nat) (onOutput : σ.Out → Async Unit) (i : σ.Id)
    (b : IO.Ref (Box sys i)) (held : Option (sys.State i)) :
    BaseIO (Option (Option (sys.State i) × Tally)) := do
  let t ← rt.moment w
  let now := t.now_ms
  let (taken, before) ← b.modifyGet fun bx =>
    let pending := bx.slot.pending
    match bx.slot.take with
    | (t, s) => ((t, pending), { bx with slot := s })
  match taken with
  | .empty => return none
  | .stale => return some (held, { gone := 1 })
  | .job j =>
    let j := match held with | some s => { j with state := s } | none => j
    let (state, effects) := j.run t
    let stops := effects.any Effect.isStop
    let sends := effects.any fun | .send .. => true | _ => false
    if stops then rt.sending.write
    else if sends then rt.sending.read
    if rt.config.record then rt.recording.lock
    let (c, after) ← b.modifyGet fun bx =>
      match bx.slot.put now ((sys.actor i).init, effects) with
      | (s, c) => ((c, s.pending), { bx with slot := s })
    if rt.config.record then
      rt.record (.tick t :: j.work.event :: c.outputs.map .output)
      rt.recording.unlock
    let freed := (if j.work.input then 1 else 0) + c.droppedInputs
    let room ← if freed == 0 && c.sends.isEmpty then pure [] else
      rt.ledgerDo fun l => (l.pushed c.sends.length).free freed
    for p in room do p.resolve ()
    for e in c.sends do rt.pushTo w e.dst (.msg (some i) e.msg)
    if stops then rt.sending.unlockWrite
    else if sends then rt.sending.unlockRead
    rt.arm i c.armed
    handOver onOutput c.outputs
    return some (some state,
      { gone := (if j.work.consumes then 1 else 0) + c.dropped, before, after })

/-- Worker `w` steps `i` on up to `budget` items, then lets it go, writing its state back. -/
private def serve (rt : Runtime sys) (w : Nat) (onOutput : σ.Out → Async Unit) (i : σ.Id) :
    BaseIO Unit := do
  let b ← rt.box i
  unless ← b.modifyGet fun bx => match bx.slot.begin with | (ok, s) => (ok, { bx with slot := s }) do
    return
  let mut n := 0
  let mut held := none
  let mut tally : Tally := {}
  while n < max 1 rt.config.budget do
    let some (next, t) ← rt.step w onOutput i b held | break
    held := next
    tally := { gone := tally.gone + t.gone, before := tally.before + t.before
               after := tally.after + t.after }
    n := n + 1
    if n % 8 == 0 then
      if ← rt.ending then break
  let keep := rt.config.record
  let (again, retired, readers, state) ← b.modifyGet fun bx =>
    let s := match held with
      | some state => { bx.slot with cell := { bx.slot.cell with state } }
      | none => bx.slot
    match s.release with
    | (q, s) =>
      let rest := !keep && !q && bx.readers.isEmpty && s.cell.up && s.cell.timers.isEmpty
        && (sys.actor i).fresh s.cell.state
      ((q, rest, bx.readers, s.cell.state), { slot := s, readers := [], retired := rest })
  answer readers state
  if retired then (rt.shardOf i).modify (·.erase i)
  if again then rt.enqueue w i
  if tally.gone != 0 || tally.before != tally.after then
    let idle ← rt.ledgerDo (Sched.Ledger.done tally.gone tally.before tally.after)
    for p in idle do p.resolve true

/-- The next actor for worker `w`: the first on its run queue, or one stolen from another's. -/
private def next (rt : Runtime sys) (w : Nat) : BaseIO (Option σ.Id) := do
  for k in [0:rt.workers] do
    let some q := rt.queues[(w + k) % rt.workers]? | continue
    if let some i ← q.modifyGet fun f => match f.pop? with
        | some (i, f) => (some i, f)
        | none => (none, f) then
      return some i
  return none

private def worker (rt : Runtime sys) (w : Nat) (onOutput : σ.Out → Async Unit) : IO Unit := do
  repeat
    if ← rt.ending then break
    match ← rt.next w with
    | some i => rt.serve w onOutput i
    | none =>
      if ← rt.stopping.get then break
      -- Say it sleeps before it looks once more, so that whoever queues an actor after the look
      -- finds it asleep and wakes it.
      rt.sleepers.modify (w :: ·)
      match ← rt.next w with
      | some i =>
        rt.sleepers.modify (·.filter (· != w))
        rt.serve w onOutput i
      | none =>
        if ← rt.stopping.get then break
        if let some p := rt.parkers[w]? then p.park
        rt.sleepers.modify (·.filter (· != w))

/-- Start the actors of `sys.boot` in order, on the calling thread, before any worker runs. -/
private def boot (rt : Runtime sys) (onOutput : σ.Out → Async Unit) : BaseIO Unit := do
  for i in sys.boot do
    let b ← rt.box i
    let (c, after) ← b.modifyGet fun bx =>
      let s := bx.slot
      match ({ s with cell := { s.cell with up := true } } : Sched.Slot sys i).put 0
          ((sys.actor i).recoverAt {} s.cell.state) with
      | (s, c) => ((c, s.pending), { bx with slot := s })
    rt.record (c.outputs.map .output)
    rt.ledgerDo fun l => ((), l.pushed c.sends.length)
    for e in c.sends do rt.pushTo 0 e.dst (.msg (some i) e.msg)
    rt.arm i c.armed
    handOver onOutput c.outputs
    rt.ledgerDo fun l => ((), { l with timers := l.timers + after })

/-- However the runtime ends, nobody is left waiting on it. -/
private def run (rt : Runtime sys) (onOutput : σ.Out → Async Unit) : IO Unit := do
  rt.boot onOutput
  rt.recovered.set true
  let timer ← IO.asTask (prio := .dedicated) rt.ring
  let threads ← (List.range rt.workers).mapM fun w =>
    IO.asTask (prio := .dedicated) (rt.worker w onOutput)
  let mut error : Option IO.Error := none
  for t in threads do
    if let .error e ← IO.wait t then error := some e
  rt.timer.unpark
  discard <| IO.wait timer
  if let some e := error then
    discard (IO.eprintln s!"lanes: a worker stopped on an error: {e}").toBaseIO
  let (room, idle) ← rt.ledgerDo Sched.Ledger.close
  for p in room do p.resolve ()
  for p in idle do p.resolve false
  live.modify (· - 1)
  rt.finished.resolve error

/-- Start a system, which runs on worker threads of its own until `stop`. The handler is given
the runtime, so that an adapter can answer an output with an input (`tryInput`). A program
whose `main` returns without stopping its runtimes does not exit.

Each output goes to `onOutput`, and the worker that put it out waits for it: a slow handler
holds that worker up, and a handler must not call `input`, `idle`, `state` or `stop`, which may
wait for the workers. `tryInput` is safe.

A timer counts from the clock reading at the start of the step that armed it. Nothing may
depend on a timer not firing early: the semantics lets one fire at any moment.

Every start is a boot, with every actor in its initial state. State that must outlive the
process belongs in a service outside, reached through an adapter. -/
def startWith (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : Runtime sys → σ.Out → Async Unit) : Async (Runtime sys) := do
  let workers := match config.workers with
    | 0 => max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat
    | n => n
  let wall := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat
  let seeds ← (List.range workers).toArray.mapM fun _ => do
    let bytes ← IO.getRandomBytes 8
    IO.mkRef (bytes.foldl (fun (x : UInt64) b => (x <<< 8) ||| b.toUInt64) 0)
  let first ← IO.mkRef ∅
  let rest ← (List.range (shards - 1)).toArray.mapM fun _ => IO.mkRef ∅
  let rt : Runtime sys := {
    config, workers
    boxes := ⟨#[first] ++ rest, by simp; omega⟩
    queues := ← (List.range workers).toArray.mapM fun _ => IO.mkRef {}
    parkers := ← (List.range workers).toArray.mapM fun _ => Parker.new
    sleepers := ← IO.mkRef []
    ledger := ← IO.mkRef {}
    agenda := ← IO.mkRef ∅
    alarms := ← IO.mkRef 0
    timer := ← Parker.new
    sending := ← Std.BaseSharedMutex.new
    recording := ← Std.BaseMutex.new
    log := ← IO.mkRef #[]
    stopping := ← IO.mkRef false
    finished := ← IO.Promise.new
    recovered := ← IO.mkRef false
    epoch := ← IO.monoMsNow
    wall, seeds
    nextHome := ← IO.mkRef 0 }
  live.modify (· + 1)
  discard <| IO.asTask (prio := .dedicated) (rt.run (onOutput rt))
  return rt

/-- `startWith` for a handler that only consumes outputs. -/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ()) : Async (Runtime sys) :=
  startWith sys config (fun _ => onOutput)

private def capacity (rt : Runtime sys) : Nat :=
  max 1 rt.config.inboxCapacity

/-- Push an input the ledger took. -/
private def deliver (rt : Runtime sys) (x : σ.In) : BaseIO Unit := do
  let w ← rt.home
  match sys.accept x with
  | ⟨i, msg⟩ =>
    if rt.config.record then
      rt.recording.lock
      rt.record [.input x]
      rt.pushTo w i (.msg none msg)
      rt.recording.unlock
    else rt.pushTo w i (.msg none msg)

private def offer (rt : Runtime sys) (x : σ.In) : BaseIO Bool := do
  let offered : Sched.Ledger.Offered (IO.Promise Unit) ←
    rt.ledgerDo (Sched.Ledger.offer rt.capacity)
  match offered with
  | .taken =>
    rt.deliver x
    return true
  | _ => return false

/-- Hand over an input, waiting while the inbox is full. Throws once the runtime has stopped. -/
def input (rt : Runtime sys) (x : σ.In) : Async Unit := do
  if ← rt.offer x then return
  repeat
    let room : IO.Promise Unit ← IO.Promise.new
    let offered : Sched.Ledger.Offered (IO.Promise Unit) ←
      rt.ledgerDo (α := Sched.Ledger.Offered (IO.Promise Unit))
        (Sched.Ledger.offerOrWait rt.capacity room)
    match offered with
    | .taken =>
      rt.deliver x
      return
    | .closed => throw stopped
    | .full => discard <| await room.result?

/-- Hand over an input if the inbox has room. `false` means nothing was accepted: the system is
busy or has stopped. -/
def tryInput (rt : Runtime sys) (x : σ.In) : BaseIO Bool :=
  rt.offer x

/-- Wait until everything handed over so far is handled and no message is waiting. With
`timers`, also until no timer is pending. Throws if the runtime stops first. -/
def idle (rt : Runtime sys) (timers : Bool := false) : Async Unit := do
  let done : IO.Promise Bool ← IO.Promise.new
  if (← rt.ledger.get).closed then throw stopped
  let now : Bool ← rt.ledgerDo (α := Bool) (Sched.Ledger.idle timers done)
  if now then return
  unless (← await done.result?) == some true do throw stopped

/-- The events performed so far. Empty unless `Config.record` is on. -/
def trace (rt : Runtime sys) : BaseIO (Array (Event σ)) :=
  rt.log.get

/-- The state of `i` between two of its steps: at once if no worker holds it, else when the
worker writes back its step or lets go of it. -/
private def stateOf (rt : Runtime sys) (i : σ.Id) : BaseIO (Task (Option (sys.State i))) := do
  have : Nonempty (sys.State i) := ⟨(sys.actor i).init⟩
  let b ← rt.box i
  let reader ← IO.Promise.new
  let now? ← b.modifyGet fun bx =>
    match bx.slot.peek? with
    | some s => (some s, bx)
    | none => (none, { bx with readers := reader :: bx.readers })
  match now? with
  | some s => return .pure (some s)
  | none => return reader.result?

/-- The started actors that `every` holds of. -/
private def startedWhere (rt : Runtime sys) (every : σ.Id → Bool) : BaseIO (List σ.Id) := do
  let mut ids := []
  for shard in rt.boxes.1 do
    for ⟨i, b⟩ in (← shard.get).toList do
      if every i && (← b.get).slot.cell.up then ids := i :: ids
  return ids

/-- Ask for the states of the actors `ids`, and of every started actor that `every` holds of.
Each is read between two of its steps, so it has every message that actor took before and none
after; the states of different actors are not read at one moment. `reply` is given them on a
task of its own. `false` means nothing was asked: the runtime has stopped.

The states are shared with that task: an actor stepped before the task lets go of its state
starts from a copy of it. -/
def tryPeek (rt : Runtime sys) (ids : List σ.Id) (reply : Option (Peek sys ids) → BaseIO Unit)
    (every : σ.Id → Bool := fun _ => false) : BaseIO Bool := do
  if (← rt.ledger.get).closed then return false
  let read := fun (i : σ.Id) => do
    let t ← rt.stateOf i
    return t.map fun s => s.map fun s => (⟨i, s⟩ : (i : σ.Id) × sys.State i)
  let mine ← ids.mapM read
  let others ← (← rt.startedWhere every).mapM read
  discard <| BaseIO.mapTasks (tasks := mine ++ others) fun states => do
    match states.mapM id with
    | none => reply none
    | some states =>
      let (got, rest) := states.splitAt ids.length
      if h : got.map (·.1) = ids then
        reply (some { states := got, ids_eq := h, every, others := rest })
      else reply none
  return true

/-- The state of actor `i` between two of its steps. For tests; an application reads with
`tryPeek`. -/
def state (rt : Runtime sys) (i : σ.Id) : Async (sys.State i) := do
  if (← rt.ledger.get).closed then throw stopped
  let some s ← await (← rt.stateOf i) | throw stopped
  return s

/-- Stop, and return when the runtime has ended. It takes no more inputs, and its workers go on
until every input it took has been taken by its actor, then end. Messages still waiting are
abandoned and pending timers never fire. -/
def stop (rt : Runtime sys) : Async Unit := do
  let (room, idle) ← rt.ledgerDo (α := List (IO.Promise Unit) × List (IO.Promise Bool))
    Sched.Ledger.close
  for p in room do p.resolve ()
  for p in idle do p.resolve false
  rt.stopping.set true
  for p in rt.parkers do p.unpark
  rt.timer.unpark
  discard <| await rt.finished.result?

/-- Whether the runtime has started: booted and handed over what booting put out. -/
def hasRecovered (rt : Runtime sys) : BaseIO Bool :=
  rt.recovered.get

/-- The inputs accepted that their actor has not taken. -/
def depth (rt : Runtime sys) : BaseIO Nat :=
  return (← rt.ledger.get).inputs

/-- Wait until the runtime has ended, and say whether an error ended it. Whoever owns the
runtime should then end the process, so that it is started again. -/
def ended (rt : Runtime sys) : Async (Option IO.Error) := do
  return (← await rt.finished.result?).join

end Runtime

end Lanes
