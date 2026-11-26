/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Async
public import Std.Sync
public import Std.Data.DHashMap
public import Lanes.Actors.World

/-!
# The concurrent runtime

Runs a `System` on `Std.Async`. Each actor is a task that takes one message at a time from its
own bounded mailbox, calls the actor's `step`, and performs the returned effects. Actors share
nothing. This file is the only place where the concurrency of a Lanes application lives.

The runtime is trusted, not proved (see `TRUSTED.md`). It is built to be checked instead: with
`Config.record` on, it records the `Event`s it performs, and the recorded list replays through
`SysState.run`. A trace the semantics rejects is a runtime bug.

## What the runtime promises

It behaves as some run of `SysState.step` under an environment model where links between actors
are reliable and ordered, links from the outside are reliable and unordered, and nothing crashes
unless an actor stops itself.

Every step takes a number from one global counter, and the recorded trace is ordered by it. A
message carries the number of the step that sent it. When an actor stops, the messages sent to
it by earlier steps are lost with its mailbox and later ones are kept, exactly as
`SysState.down` says.

## Main definitions

- `Runtime.Config`: mailbox capacity, restart policy, trace recording.
- `Runtime.start`: boot a system.
- `Runtime.input`: hand an external input to the system.
- `Runtime.idle`, `Runtime.trace`, `Runtime.state`: for tests and trace checking.
-/

public section

namespace Lanes

open Std Std.Async

variable {σ : Signature}

/-- Settings of a running system. Every limit is explicit (rules 2.5, 2.6). -/
structure Runtime.Config (σ : Signature) where
  /-- Capacity of every actor's mailbox. A sender to a full mailbox waits (rule 3.8). -/
  mailboxCapacity : Nat := 1024
  /-- Which actors start again at once after stopping, without waiting for a message. -/
  restart : σ.Id → Bool := fun _ => false
  /-- Record every event, for trace checking and tests. -/
  record : Bool := false

/--
The environment model the runtime promises to stay within: links between actors are reliable
and ordered, inputs from outside arrive in no particular order, and the only failure is an actor
stopping itself. Recorded traces replay through `SysState.run` under this model.
-/
def Runtime.Config.env (config : Runtime.Config σ) : EnvModel σ where
  link src _ := if src.isSome then Link.reliable else Link.unordered
  restarts := config.restart

/-- What sits in a mailbox. -/
private inductive Item (σ : Signature) (i : σ.Id) where
  /-- A message, with its sender and the number of the step that sent it. -/
  | msg (src : Option σ.Id) (m : σ.Msg i) (sentAt : Nat)
  /-- A timer that fired. It counts only if `token` still identifies the pending timer. -/
  | timer (m : σ.Msg i) (token : Nat)

/-- The part of an actor that senders touch, guarded by a mutex. -/
private structure Gate (σ : Signature) (i : σ.Id) where
  /-- The mailbox of the running actor, or `none` if the actor is down. -/
  mailbox : Option (CloseableChannel (Item σ i)) := none
  /-- The number of the step at which the actor last stopped. -/
  downAt : Nat := 0

/-- An actor in the runtime. `state` and `timers` are touched only by the actor's own task. -/
private structure Cell (sys : System σ) (i : σ.Id) where
  gate : Mutex (Gate σ i)
  state : IO.Ref (sys.State i)
  timers : IO.Ref (List (σ.Msg i × Nat))

/-- A running system. -/
structure Runtime (sys : System σ) [Hashable σ.Id] where
  private mk ::
  private config : Runtime.Config σ
  private cells : Mutex (DHashMap σ.Id (Cell sys))
  private clock : IO.Ref Nat
  private inFlight : IO.Ref Int
  private log : Mutex (Array (Nat × Event σ))
  private onOutput : σ.Out → Async Unit

namespace Runtime

variable {sys : System σ} [Hashable σ.Id]

/-- The number of the next step. -/
private def tick (rt : Runtime sys) : BaseIO Nat :=
  rt.clock.modifyGet fun n => (n + 1, n + 1)

/-- Record an event as step `seq`. -/
private def record (rt : Runtime sys) (seq : Nat) (ev : Event σ) : BaseIO Unit := do
  if rt.config.record then
    rt.log.atomically (modify (·.push (seq, ev)))

/-- The cell of actor `i`, created on first use. -/
private def cell (rt : Runtime sys) (i : σ.Id) : BaseIO (Cell sys i) :=
  rt.cells.atomically do
    match (← get).get? i with
    | some c => return c
    | none =>
      let c : Cell sys i := {
        gate := ← Mutex.new {}
        state := ← IO.mkRef (sys.actor i).init
        timers := ← IO.mkRef [] }
      modify (·.insert i c)
      return c

/-- What a sender must do with a message. -/
private inductive Route (σ : Signature) (i : σ.Id) where
  /-- Put it in this mailbox. -/
  | enqueue (mailbox : CloseableChannel (Item σ i))
  /-- The actor was down: it has been given this new mailbox and must be started. -/
  | start (mailbox : CloseableChannel (Item σ i))
  /-- The message was sent before the actor stopped and is lost with the old mailbox. -/
  | lost

/-- Put an item in a mailbox, waiting if it is full. `false` if the mailbox was closed. -/
private def offer {i : σ.Id} (mailbox : CloseableChannel (Item σ i)) (item : Item σ i) :
    Async Bool := do
  if ← mailbox.trySend item then return true
  match ← await (← mailbox.send item) with
  | .ok _ => return true
  | .error _ => return false

mutual

/--
Deliver `m` to the mailbox of actor `i`, starting the actor if it is down. Waits while the
mailbox is full.
-/
private partial def post (rt : Runtime sys) (src : Option σ.Id) (i : σ.Id) (m : σ.Msg i)
    (sentAt : Nat) : Async Unit := do
  let cell ← rt.cell i
  rt.inFlight.modify (· + 1)
  repeat
    let route : Route σ i ← cell.gate.atomically do
      let gate ← get
      match gate.mailbox with
      | some mailbox => return .enqueue mailbox
      | none =>
        if sentAt ≤ gate.downAt then return .lost
        let mailbox ← CloseableChannel.new (some rt.config.mailboxCapacity)
        set { gate with mailbox := some mailbox }
        return .start mailbox
    match route with
    | .lost =>
      rt.inFlight.modify (· - 1)
      break
    | .start mailbox =>
      background (rt.live i cell mailbox (boot := false))
      if ← offer mailbox (.msg src m sentAt) then break
    | .enqueue mailbox =>
      if ← offer mailbox (.msg src m sentAt) then break

/-- Perform the effects of step `seq` of actor `i`. Returns whether the actor asked to stop. -/
private partial def perform (rt : Runtime sys) (i : σ.Id) (cell : Cell sys i)
    (mailbox : CloseableChannel (Item σ i)) (seq : Nat) (effs : List (Effect σ i)) :
    Async Bool := do
  let mut stop := false
  for eff in effs do
    match eff with
    | .send to msg => rt.post (some i) to msg seq
    | .emit out =>
      rt.record (← rt.tick) (.output out)
      try rt.onOutput out
      catch e => IO.eprintln s!"lanes: output handler failed: {e}"
    | .after delay_ms msg =>
      let token ← rt.tick
      cell.timers.modify fun ts =>
        if ts.any (·.1 = msg) then ts.map fun t => if t.1 = msg then (msg, token) else t
        else ts ++ [(msg, token)]
      background do
        Async.sleep (.ofNat delay_ms)
        discard <| offer mailbox (.timer msg token)
    | .cancel msg => cell.timers.modify (·.filter (·.1 ≠ msg))
    | .stop => stop := true
  return stop

/--
The task of actor `i`: start through `recover`, then handle the mailbox one item at a time. When
the actor stops, close the mailbox, keep the messages sent after the stopping step, and start
again if there are any or the restart policy says so.
-/
private partial def live (rt : Runtime sys) (i : σ.Id) (cell : Cell sys i)
    (mailbox : CloseableChannel (Item σ i)) (boot : Bool) : Async Unit := do
  let mut mailbox := mailbox
  let mut boot := boot
  repeat
    let seq ← rt.tick
    -- Actors in `System.boot` are started by `SysState.init`, not by a `start` event.
    if !boot then rt.record seq (.start i)
    boot := false
    let r := (sys.actor i).recover (← cell.state.get)
    cell.state.set r.1
    let mut stoppedAt : Option Nat := none
    if ← rt.perform i cell mailbox seq r.2 then stoppedAt := some seq
    while stoppedAt.isNone do
      let item ← match ← mailbox.tryRecv with
        | some item => pure (some item)
        | none => await (← mailbox.recv)
      let some item := item | break
      match item with
      | .msg src m _ =>
        let seq ← rt.tick
        rt.record seq (.deliver ⟨src, i, m⟩)
        let r := (sys.actor i).step (← cell.state.get) m
        cell.state.set r.1
        if ← rt.perform i cell mailbox seq r.2 then stoppedAt := some seq
        rt.inFlight.modify (· - 1)
      | .timer m token =>
        if (← cell.timers.get).contains (m, token) then
          cell.timers.modify (·.erase (m, token))
          let seq ← rt.tick
          rt.record seq (.timeout i m)
          let r := (sys.actor i).step (← cell.state.get) m
          cell.state.set r.1
          if ← rt.perform i cell mailbox seq r.2 then stoppedAt := some seq
    let some downAt := stoppedAt | break
    cell.timers.set []
    let old := mailbox
    let (next, lost) ← cell.gate.atomically do
      -- Closing can only fail if the mailbox is already closed.
      discard <| (old.close : EIO _ Unit).toBaseIO
      let mut kept : Array (Item σ i) := #[]
      let mut lost : Int := 0
      repeat
        match ← old.tryRecv with
        | some (.msg src m sentAt) =>
          if sentAt ≤ downAt then lost := lost + 1 else kept := kept.push (.msg src m sentAt)
        | some (.timer ..) => pure ()
        | none => break
      if kept.isEmpty && !rt.config.restart i then
        set ({ mailbox := none, downAt } : Gate σ i)
        return (none, lost)
      let fresh ← CloseableChannel.new (some rt.config.mailboxCapacity)
      for item in kept do
        discard <| fresh.trySend item
      set ({ mailbox := some fresh, downAt } : Gate σ i)
      return (some fresh, lost)
    rt.inFlight.modify (· - lost)
    match next with
    | some fresh => mailbox := fresh
    | none => break

end

/--
Boot a system: start the actors in `sys.boot`, in order. Each output the system emits is passed
to `onOutput`; adapters use it to answer the outside world.
-/
def start (sys : System σ) [Hashable σ.Id] (config : Runtime.Config σ := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ()) : Async (Runtime sys) := do
  let rt : Runtime sys := {
    config, onOutput
    cells := ← Mutex.new {}
    clock := ← IO.mkRef 0
    inFlight := ← IO.mkRef 0
    log := ← Mutex.new #[] }
  for i in sys.boot do
    let cell ← rt.cell i
    let fresh ← cell.gate.atomically do
      if (← get).mailbox.isSome then return none
      let mailbox ← CloseableChannel.new (some config.mailboxCapacity)
      set ({ mailbox := some mailbox } : Gate σ i)
      return some mailbox
    if let some mailbox := fresh then
      background (rt.live i cell mailbox (boot := true))
  return rt

/-- Hand an external input to the system. Returns once it is in the receiver's mailbox, so a
full mailbox pushes back on the caller. -/
def input (rt : Runtime sys) (x : σ.In) : Async Unit := do
  let ⟨i, msg⟩ := sys.accept x
  let seq ← rt.tick
  rt.record seq (.input x)
  rt.post none i msg seq

/-- Wait until no message is in flight. Pending timers do not count. For tests. -/
def idle (rt : Runtime sys) : Async Unit := do
  while (← rt.inFlight.get) > 0 do
    Async.sleep 1

/-- The events recorded so far, in order. Empty unless `Config.record` is on. -/
def trace (rt : Runtime sys) : BaseIO (Array (Event σ)) := do
  let log ← rt.log.atomically get
  return (log.qsort fun a b => a.1 < b.1).map (·.2)

/-- The current state of actor `i`, as last written by its task. For tests and inspection; an
application reads state by sending the actor a message. -/
def state (rt : Runtime sys) (i : σ.Id) : BaseIO (sys.State i) := do
  (← rt.cell i).state.get

end Runtime

end Lanes
