/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Kernel

/-!
The free-running scheduler's decisions, as pure functions over one actor's slot: its state, its
mailbox and whether it is idle, on a run queue or running. The shell (`Lanes.Runtime`) keeps
each slot in a reference of its own and calls these under it; worker threads take actors off
run queues and step them. `Lanes.Runtime.SchedSound` proves that every run of the scheduler's
model, which applies these functions, is a run of the semantics.

A step is taken in three parts, so that the step function runs outside the slot's lock: `take`
the next item and the state out of the slot, `Job.run` the step on them, and `put` the result
back. Only the worker that holds the actor takes and puts; other threads only `push` to its
mailbox meanwhile, which commutes with both (`Sched.take_push`, `Sched.put_push`).

`Ledger` is what every thread shares besides the actors: the inputs accepted that their actor
has not taken yet, bounded by the inbox's capacity (rule 3.8), and the counts that say when the
system is idle.
-/

@[expose] public section

namespace Lanes.Sched

variable {σ : Signature}

/-- What waits in an actor's mailbox: a message, from an actor or from outside, or one of its
timers that went off. -/
inductive Item (σ : Signature) (i : σ.Id) where
  | msg (src : Option σ.Id) (m : σ.Msg i)
  | timer (m : σ.Msg i) (due : Kernel.Due)

def Item.isInput {i : σ.Id} : Item σ i → Bool
  | .msg none _ => true
  | _ => false

inductive Status where
  | idle
  /-- On a run queue: some worker will take it. -/
  | queued
  /-- Held by one worker, which steps it. -/
  | running
  deriving DecidableEq, Repr

/-- One actor, as the scheduler keeps it. -/
structure Slot (sys : System σ) (i : σ.Id) where
  cell : Kernel.Cell sys i
  mail : Fifo (Item σ i) := {}
  status : Status := .idle
  /-- Tells apart two timers of this actor due at the same time. -/
  nextToken : Nat := 0

/-- What a step does: handle a message, start the actor, or handle a timer. -/
inductive Work (σ : Signature) (i : σ.Id) where
  | deliver (src : Option σ.Id) (m : σ.Msg i)
  | start
  | timeout (m : σ.Msg i)

structure Job (sys : System σ) (i : σ.Id) where
  work : Work σ i
  state : sys.State i

inductive Taken (sys : System σ) (i : σ.Id) where
  | empty
  /-- A timer that was cancelled or armed again since it went off: dropped. -/
  | stale
  | job (j : Job sys i)

/-- What a step leaves for the shell to do: messages to push to other actors' mailboxes,
outputs to hand over, timers to put on the agenda, and the items of the mailbox it dropped
when the actor stopped. -/
structure Commit (σ : Signature) (i : σ.Id) where
  sends : List (Envelope σ) := []
  outputs : List σ.Out := []
  armed : List (σ.Msg i × Kernel.Due) := []
  dropped : Nat := 0
  /-- How many of those were inputs. -/
  droppedInputs : Nat := 0

namespace Work

def event {i : σ.Id} : Work σ i → Event σ
  | .deliver src m => .deliver ⟨src, i, m⟩
  | .start => .start i
  | .timeout m => .timeout i m

/-- Whether the item was taken off the mailbox: a start leaves the message that caused it. -/
def consumes {i : σ.Id} : Work σ i → Bool
  | .start => false
  | _ => true

/-- Whether the item was an input, whose place in the inbox's bound is then free. -/
def input {i : σ.Id} : Work σ i → Bool
  | .deliver none _ => true
  | _ => false

end Work

def Job.run {sys : System σ} {i : σ.Id} (j : Job sys i) : sys.State i × List (Effect σ i) :=
  match j.work with
  | .deliver _ m | .timeout m => (sys.actor i).step j.state m
  | .start => (sys.actor i).recover j.state

/-- Arm the timer for `msg` at `due`, replacing the one for `msg` if it is pending. -/
def arm {α β : Type} [DecidableEq α] (timers : List (α × β)) (msg : α) (due : β) :
    List (α × β) :=
  if timers.any (·.1 = msg) then timers.map fun t => if t.1 = msg then (msg, due) else t
  else timers ++ [(msg, due)]

namespace Slot

variable {sys : System σ} {i : σ.Id}

def fresh (sys : System σ) (i : σ.Id) : Slot sys i :=
  { cell := { state := (sys.actor i).init } }

/-- Put `x` in the mailbox. `true`: the actor was idle and is now queued, so the caller puts it
on a run queue. -/
def push (x : Item σ i) (s : Slot sys i) : Bool × Slot sys i :=
  if s.status = .idle then (true, { s with mail := s.mail.push x, status := .queued })
  else (false, { s with mail := s.mail.push x })

/-- A worker that took the actor off a run queue holds it, if it was queued. An actor is on a
run queue at most once while it is queued, but a stale entry is harmless: `false`, and the
worker drops it. -/
def begin (s : Slot sys i) : Bool × Slot sys i :=
  if s.status = .queued then (true, { s with status := .running }) else (false, s)

/-- The worker lets go of the actor. `true`: mail is waiting, so it is queued again and the
caller puts it on a run queue. -/
def release (s : Slot sys i) : Bool × Slot sys i :=
  if s.mail.isEmpty then (false, { s with status := .idle })
  else (true, { s with status := .queued })

/-- The next item and the state, taken out of the slot so that the step updates the state in
place (D84). A message to an actor that is down starts it and stays queued, as in the kernel
(`Kernel.run1`); a timer counts only if it is still pending (`Kernel.fire`). -/
def take (s : Slot sys i) : Taken sys i × Slot sys i :=
  match s.mail.pop? with
  | none => (.empty, s)
  | some (.msg src m, rest) =>
    if s.cell.up then
      (.job ⟨.deliver src m, s.cell.state⟩,
        { s with mail := rest, cell := { s.cell with state := (sys.actor i).init } })
    else
      (.job ⟨.start, s.cell.state⟩,
        { s with cell := { s.cell with state := (sys.actor i).init, up := true } })
  | some (.timer m due, rest) =>
    if s.cell.up && s.cell.timers.contains (m, due) then
      (.job ⟨.timeout m, s.cell.state⟩,
        { s with mail := rest,
                 cell := { s.cell with state := (sys.actor i).init,
                                       timers := s.cell.timers.eraseP (·.1 = m) } })
    else (.stale, { s with mail := rest })

def perform (now_ms : Nat) : Slot sys i × Commit σ i → Effect σ i → Slot sys i × Commit σ i
  | (s, c), .send to msg => (s, { c with sends := c.sends ++ [⟨some i, to, msg⟩] })
  | (s, c), .emit out => (s, { c with outputs := c.outputs ++ [out] })
  | (s, c), .after delay_ms msg =>
    let due : Kernel.Due := ⟨now_ms + delay_ms, s.nextToken⟩
    ({ s with nextToken := s.nextToken + 1, cell := { s.cell with timers := arm s.cell.timers msg due } },
      { c with armed := c.armed ++ [(msg, due)] })
  | (s, c), .cancel msg =>
    ({ s with cell := { s.cell with timers := s.cell.timers.eraseP (·.1 = msg) } }, c)
  | (s, c), .stop => (s, c)

/-- Take the actor down: it loses its timers and its mailbox, and what it sent itself. -/
def down (s : Slot sys i) (c : Commit σ i) : Slot sys i × Commit σ i :=
  ({ s with mail := {}, cell := { s.cell with up := false, timers := [] } },
    { c with sends := c.sends.filter fun e => decide (e.dst ≠ i), dropped := s.mail.length
             droppedInputs := s.mail.toList.countP Item.isInput })

/-- Write back the result of a step taken at `now_ms` and perform its effects on the actor. -/
def put (now_ms : Nat) (r : sys.State i × List (Effect σ i)) (s : Slot sys i) :
    Slot sys i × Commit σ i :=
  let (s, c) := r.2.foldl (perform now_ms) ({ s with cell := { s.cell with state := r.1 } }, {})
  if r.2.any Effect.isStop then down s c else (s, c)

/-- The state of an actor that no worker holds: its state between two steps. -/
def peek? (s : Slot sys i) : Option (sys.State i) :=
  if s.status = .running then none else some s.cell.state

/-- How many timers of the actor are pending. -/
def pending (s : Slot sys i) : Nat :=
  s.cell.timers.length

end Slot

/-- What every thread shares besides the actors. `W` wakes a sender waiting for room, `I` an
idle waiter. -/
structure Ledger (W I : Type) where
  /-- Inputs accepted that their actor has not taken: at most the inbox's capacity. -/
  inputs : Nat := 0
  /-- Items in mailboxes or in a worker's hands. -/
  items : Nat := 0
  timers : Nat := 0
  closed : Bool := false
  waiting : List W := []
  idlers : List (Bool × I) := []

namespace Ledger

variable {W I : Type}

inductive Offered (W : Type) where
  | taken
  | full
  | closed

def offer (capacity : Nat) (l : Ledger W I) : Offered W × Ledger W I :=
  if l.closed then (.closed, l)
  else if l.inputs < capacity then (.taken, { l with inputs := l.inputs + 1, items := l.items + 1 })
  else (.full, l)

/-- `offer`, and when there is no room remember `room` to be woken when there is. -/
def offerOrWait (capacity : Nat) (room : W) (l : Ledger W I) : Offered W × Ledger W I :=
  match offer capacity l with
  | (.full, l) => (.full, { l with waiting := room :: l.waiting })
  | answered => answered

def quiet (l : Ledger W I) (timers : Bool) : Bool :=
  l.items == 0 && (!timers || l.timers == 0)

/-- Who waits for the system to be idle and may now stop waiting. -/
def settle (l : Ledger W I) : List I × Ledger W I :=
  let (ready, rest) := l.idlers.partition fun (timers, _) => l.quiet timers
  (ready.map (·.2), { l with idlers := rest })

/-- Wait until the system is idle: `true` if it already is. -/
def idle (timers : Bool) (w : I) (l : Ledger W I) : Bool × Ledger W I :=
  if l.quiet timers then (true, l) else (false, { l with idlers := (timers, w) :: l.idlers })

/-- `n` items were put in mailboxes (a message, a timer that went off). -/
def pushed (n : Nat) (l : Ledger W I) : Ledger W I :=
  { l with items := l.items + n }

/-- A step is done: it pushed `sent` messages, took its item off the mailbox if `consumed`, which
was an input if `input`, dropped `dropped` items of which `droppedInputs` inputs, and left
`before` pending timers `after`. The senders waiting for room, if an input left, and the idle
waiters now answered. -/
def done (sent : Nat) (consumed input : Bool) (dropped droppedInputs before after : Nat)
    (l : Ledger W I) : (List W × List I) × Ledger W I :=
  let freed := (if input then 1 else 0) + droppedInputs
  let l := { l with
    items := l.items + sent - (if consumed then 1 else 0) - dropped
    inputs := l.inputs - freed
    timers := l.timers + after - before }
  let (room, l) := if freed != 0 then (l.waiting, { l with waiting := [] }) else ([], l)
  let (idle, l) := l.settle
  ((room, idle), l)

/-- Take no more inputs. Every sender waiting for room and every idle waiter is to be told. -/
def close (l : Ledger W I) : (List W × List I) × Ledger W I :=
  ((l.waiting, l.idlers.map (·.2)), { l with closed := true, waiting := [], idlers := [] })

end Ledger

end Lanes.Sched
