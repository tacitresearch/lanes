/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.DHashMap
public import Std.Data.TreeMap
public import Lanes.Core.World
public import Lanes.Data.Fifo

/-!
The kernel is the runtime's whole decision logic as pure functions over a hash map of actors,
a queue of messages and an agenda of timers. It runs one shard: one thread, no concurrency.
`Kernel.abs` reads a kernel state as a `SysState`, and `Lanes.Runtime.KernelSound` proves that
each kernel operation is a run of `SysState.step`. The shell around it only moves data.

Time is data: the shell tells the kernel what the clock says (`advance`) and the kernel says
which timers are due (`step`) and how long nothing will be (`wait`). The kernel never keeps
emitted outputs. It hands them to the shell, which is the semantics' `emit` followed at once by
`output`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace Kernel

/-- When a timer is due. The token tells apart two timers due at the same time. -/
structure Due where
  deadline_ms : Nat
  token : Nat
  deriving DecidableEq, Ord, Repr

structure Cell (sys : System σ) (i : σ.Id) where
  state : sys.State i
  up : Bool := false
  timers : List (σ.Msg i × Due) := []

end Kernel

structure Kernel (sys : System σ) [Hashable σ.Id] where
  cells : Std.DHashMap σ.Id (Kernel.Cell sys) := ∅
  queue : Fifo (Envelope σ) := {}
  nextToken : Nat := 0
  clock_ms : Nat := 0
  /-- The pending timers of every cell, earliest first. -/
  agenda : Std.TreeMap Kernel.Due ((i : σ.Id) × σ.Msg i) := ∅
  /-- Who goes first when a timer is due and a message is queued. -/
  timerTurn : Bool := true

namespace Kernel

variable {sys : System σ} [Hashable σ.Id]

structure Step (sys : System σ) [Hashable σ.Id] where
  kernel : Kernel sys
  events : List (Event σ) := []
  outputs : List σ.Out := []

def cell (k : Kernel sys) (i : σ.Id) : Cell sys i :=
  (k.cells.get? i).getD { state := (sys.actor i).init }

def setCell (k : Kernel sys) (i : σ.Id) (c : Cell sys i) : Kernel sys :=
  { k with cells := k.cells.insert i c }

/-- The system state a kernel state stands for. Outputs are not kept in the kernel, so the
caller says which are still to be handed over. -/
def abs (k : Kernel sys) (outbox : List σ.Out := []) : SysState sys where
  state i := (k.cell i).state
  up i := (k.cell i).up
  net := k.queue.toList
  timers i := (k.cell i).timers.map (·.1)
  outbox := outbox

/-- The environment the kernel stays within: one shard, so every link is reliable and ordered,
and nothing crashes. -/
def env : EnvModel σ := {}

def unschedule (k : Kernel sys) (dues : List Due) : Kernel sys :=
  { k with agenda := dues.foldl (·.erase ·) k.agenda }

def perform (k : Kernel sys) (i : σ.Id) : Effect σ i → Kernel sys × List σ.Out
  | .send to msg => ({ k with queue := k.queue.push ⟨some i, to, msg⟩ }, [])
  | .emit out => (k, [out])
  | .after delay_ms msg =>
    let c := k.cell i
    let due : Due := ⟨k.clock_ms + delay_ms, k.nextToken⟩
    let timers :=
      if c.timers.any (·.1 = msg) then c.timers.map fun t => if t.1 = msg then (msg, due) else t
      else c.timers ++ [(msg, due)]
    let k := k.unschedule ((c.timers.filter fun t => t.1 = msg).map Prod.snd)
    (({ k with nextToken := k.nextToken + 1, agenda := k.agenda.insert due ⟨i, msg⟩ }).setCell i
      { c with timers }, [])
  | .cancel msg =>
    let c := k.cell i
    ((k.unschedule ((c.timers.find? fun t => t.1 = msg).toList.map Prod.snd)).setCell i
      { c with timers := c.timers.eraseP (·.1 = msg) }, [])
  | .stop => (k, [])

/-! Pairs are taken apart by pattern from here on, never by projection: a projection keeps the
pair alive, the pair keeps the kernel alive, and a kernel with two owners is copied when it is
updated. `Tests/Scale.lean` measures that this does not happen. -/

def performAll (k : Kernel sys) (i : σ.Id) (effs : List (Effect σ i)) :
    Kernel sys × List σ.Out :=
  effs.foldl (init := (k, [])) fun (k, outs) eff =>
    let (k, more) := k.perform i eff
    (k, outs ++ more)

def down (k : Kernel sys) (i : σ.Id) : Kernel sys :=
  let c := k.cell i
  (({ k with queue := k.queue.filter fun e => decide (e.dst ≠ i) }).unschedule
    (c.timers.map Prod.snd)).setCell i { c with up := false, timers := [] }

def settle (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    Kernel sys × List σ.Out :=
  let c := k.cell i
  let (k, outs) := (k.setCell i { c with state := r.1 }).performAll i r.2
  (if r.2.any Effect.isStop then k.down i else k, outs)

/-- Actor `i` leaves memory when it is at rest: up, with no timers, in a state that starting it
gives (`Actor.fresh`). Its next message starts it again as it was, so nothing can tell
(`docs/decisions/D51-release-actors-at-rest.md`). Mail still queued for it is no reason to keep
it: finding out would take a look through the queue, and its next message starts it as any
other would. -/
def rest (k : Kernel sys) (i : σ.Id) : Kernel sys :=
  let c := k.cell i
  if (sys.actor i).fresh c.state && c.up && c.timers.isEmpty then
    { k with cells := k.cells.erase i }
  else k

def handle (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) : Kernel sys × List σ.Out :=
  let r := (sys.actor i).step (k.cell i).state msg
  let (k, outs) := k.settle i r
  (k.rest i, outs)

def startActor (k : Kernel sys) (i : σ.Id) : Kernel sys × List σ.Out :=
  let c := k.cell i
  (k.setCell i { c with up := true }).settle i ((sys.actor i).recover c.state)

def boot (sys : System σ) [Hashable σ.Id] : Kernel sys × List σ.Out :=
  sys.boot.foldl (init := ({}, [])) fun (k, outs) i =>
    let (k, more) := k.startActor i
    (k, outs ++ more)

def accept (k : Kernel sys) (x : σ.In) : Step sys :=
  { kernel := { k with queue := k.queue.push ⟨none, (sys.accept x).1, (sys.accept x).2⟩ }
    events := [.input x] }

/-- Take the oldest message. If its receiver is down, start the receiver and leave the message
queued; otherwise the receiver handles it. Nothing happens when nothing is queued. -/
def run1 (k : Kernel sys) : Step sys :=
  match k.queue.pop? with
  | none => { kernel := k }
  | some (e, rest) =>
    if (k.cell e.dst).up then
      let (k, outs) := ({ k with queue := rest }).handle e.dst e.msg
      { kernel := k, events := .deliver e :: outs.map .output, outputs := outs }
    else
      let (k, outs) := k.startActor e.dst
      { kernel := k, events := .start e.dst :: outs.map .output, outputs := outs }

/-- The timer for `msg` at `due` goes off. It counts only if that timer is still pending: one
that was cancelled or armed again is ignored, and the agenda is left as it is, because the shell
may name a `due` that is another timer's. -/
def fire (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (due : Due) : Step sys :=
  let c := k.cell i
  if c.up && c.timers.contains (msg, due) then
    let (k, outs) := ((k.unschedule [due]).setCell i
      { c with timers := c.timers.eraseP (·.1 = msg) }).handle i msg
    { kernel := k, events := .timeout i msg :: outs.map .output, outputs := outs }
  else { kernel := k }

/-- The clock never goes back, whatever the shell reports. -/
def advance (k : Kernel sys) (now_ms : Nat) : Kernel sys :=
  { k with clock_ms := max k.clock_ms now_ms }

/-- The timer to fire now, if a timer is what comes next: the earliest, when it is due and it
is the timers' turn or no message is queued. -/
def timerNext (k : Kernel sys) : Option (Due × (i : σ.Id) × σ.Msg i) :=
  k.agenda.minEntry?.filter fun (due, _) =>
    due.deadline_ms ≤ k.clock_ms && (k.timerTurn || k.queue.isEmpty)

/-- One unit of work: the earliest timer if it is due, or the oldest message. When both are
there they take turns, because a timer that is always due would otherwise keep every message
waiting, and a queue that is never empty every timer. -/
def step (k : Kernel sys) : Step sys :=
  match k.timerNext with
  | some (due, ⟨i, msg⟩) => ({ k with timerTurn := false }).fire i msg due
  | none => ({ k with timerTurn := true }).run1

/-- How long the shell may sleep when no input arrives. -/
inductive Wait where
  | none
  | for_ms (ms : Nat)
  | forever
  deriving DecidableEq, Repr

def wait (k : Kernel sys) : Wait :=
  if !k.queue.isEmpty then .none
  else
    match k.agenda.minKey? with
    | some due =>
      if due.deadline_ms ≤ k.clock_ms then .none else .for_ms (due.deadline_ms - k.clock_ms)
    | none => .forever

/-- At most `fuel` units of work, stopping when there is none to do now. -/
def runBatch (k : Kernel sys) : (fuel : Nat) → Step sys
  | 0 => { kernel := k }
  | fuel + 1 =>
    if k.wait = .none then
      match k.step with
      | { kernel, events, outputs } =>
        match kernel.runBatch fuel with
        | { kernel, events := later, outputs := more } =>
          { kernel, events := events ++ later, outputs := outputs ++ more }
    else { kernel := k }

/-- No message is queued and, with `timers`, no timer is pending. -/
def quiet (k : Kernel sys) (timers : Bool) : Bool :=
  k.queue.isEmpty && (!timers || k.agenda.isEmpty)

/-- A kernel written down, as a snapshot holds it. -/
structure Image (sys : System σ) where
  cells : List ((i : σ.Id) × Cell sys i)
  queue : List (Envelope σ)
  agenda : List (Due × ((i : σ.Id) × σ.Msg i))
  nextToken : Nat
  clock_ms : Nat
  timerTurn : Bool

def image (k : Kernel sys) : Image sys where
  cells := k.cells.toList
  queue := k.queue.toList
  agenda := k.agenda.toList
  nextToken := k.nextToken
  clock_ms := k.clock_ms
  timerTurn := k.timerTurn

def Image.kernel (img : Image sys) : Kernel sys where
  cells := .ofList img.cells
  queue := { front := img.queue }
  agenda := .ofList img.agenda
  nextToken := img.nextToken
  clock_ms := img.clock_ms
  timerTurn := img.timerTurn

/-- Everything a shell can ask of a kernel. -/
inductive Op (σ : Signature) where
  | input (x : σ.In)
  | advance (now_ms : Nat)
  | step
  | batch (fuel : Nat)
  | fire (i : σ.Id) (msg : σ.Msg i) (due : Due)
  /-- The kernel becomes the one its image restores. That is the same system state
  (`Kernel.abs_image_kernel`), but not the same value: a hash map built again is laid out
  differently. A shard that saves an image goes on with the restored kernel, so that a shard
  started from the saved image computes the very same values, and no theorem is needed that
  two kernels alike in everything observable behave alike. -/
  | snapshot

def apply (k : Kernel sys) : Op σ → Step sys
  | .input x => k.accept x
  | .advance now_ms => { kernel := k.advance now_ms }
  | .step => k.step
  | .batch fuel => k.runBatch fuel
  | .fire i msg due => k.fire i msg due
  | .snapshot => { kernel := k.image.kernel }

def exec (k : Kernel sys) : List (Op σ) → Step sys
  | [] => { kernel := k }
  | op :: ops =>
    match k.apply op with
    | { kernel, events, outputs } =>
      match kernel.exec ops with
      | { kernel, events := later, outputs := more } =>
        { kernel, events := events ++ later, outputs := outputs ++ more }

end Kernel

end Lanes
