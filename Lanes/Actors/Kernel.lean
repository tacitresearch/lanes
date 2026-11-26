/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Data.DHashMap
public import Lanes.Actors.World
public import Lanes.Data.Fifo

/-!
The kernel is the runtime's whole decision logic as pure functions over a hash map of actors
and a queue of messages. It runs one shard: one thread, no concurrency. `Kernel.abs` reads a
kernel state as a `SysState`, and `Lanes.Actors.KernelSound` proves that each kernel operation
is a run of `SysState.step`. The shell around it only moves data.

The kernel never keeps emitted outputs. It hands them to the shell as commands, which is the
semantics' `emit` followed at once by `output`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

namespace Kernel

structure Cell (sys : System σ) (i : σ.Id) where
  state : sys.State i
  up : Bool := false
  /-- Pending timers with the token the shell must present when one fires. A re-armed timer gets
  a new token, so a firing that was already on its way is recognised as stale. -/
  timers : List (σ.Msg i × Nat) := []

/-- What the kernel asks its shell to do. -/
inductive Command (σ : Signature) where
  | emit (out : σ.Out)
  | arm (i : σ.Id) (msg : σ.Msg i) (token : Nat) (delay_ms : Nat)

def outputs (commands : List (Command σ)) : List σ.Out :=
  commands.filterMap fun
    | .emit out => some out
    | .arm .. => none

end Kernel

structure Kernel (sys : System σ) [Hashable σ.Id] where
  cells : Std.DHashMap σ.Id (Kernel.Cell sys) := ∅
  queue : Fifo (Envelope σ) := {}
  nextToken : Nat := 0

namespace Kernel

variable {sys : System σ} [Hashable σ.Id]

/-- The events a kernel operation performed, in order, and what the shell must do. -/
structure Step (sys : System σ) [Hashable σ.Id] where
  kernel : Kernel sys
  events : List (Event σ) := []
  commands : List (Command σ) := []

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

def perform (k : Kernel sys) (i : σ.Id) : Effect σ i → Kernel sys × List (Command σ)
  | .send to msg => ({ k with queue := k.queue.push ⟨some i, to, msg⟩ }, [])
  | .emit out => (k, [.emit out])
  | .after delay_ms msg =>
    let c := k.cell i
    let token := k.nextToken
    let timers :=
      if c.timers.any (·.1 = msg) then c.timers.map fun t => if t.1 = msg then (msg, token) else t
      else c.timers ++ [(msg, token)]
    (({ k with nextToken := token + 1 }).setCell i { c with timers },
      [.arm i msg token delay_ms])
  | .cancel msg =>
    let c := k.cell i
    (k.setCell i { c with timers := c.timers.eraseP (·.1 = msg) }, [])
  | .stop => (k, [])

def performAll (k : Kernel sys) (i : σ.Id) (effs : List (Effect σ i)) :
    Kernel sys × List (Command σ) :=
  effs.foldl (fun acc eff => ((acc.1.perform i eff).1, acc.2 ++ (acc.1.perform i eff).2)) (k, [])

def down (k : Kernel sys) (i : σ.Id) : Kernel sys :=
  ({ k with queue := k.queue.filter fun e => decide (e.dst ≠ i) }).setCell i
    { (k.cell i) with up := false, timers := [] }

def settle (k : Kernel sys) (i : σ.Id) (r : sys.State i × List (Effect σ i)) :
    Kernel sys × List (Command σ) :=
  let done := (k.setCell i { (k.cell i) with state := r.1 }).performAll i r.2
  (if r.2.any Effect.isStop then done.1.down i else done.1, done.2)

def handle (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) : Kernel sys × List (Command σ) :=
  k.settle i ((sys.actor i).step (k.cell i).state msg)

def startActor (k : Kernel sys) (i : σ.Id) : Kernel sys × List (Command σ) :=
  (k.setCell i { (k.cell i) with up := true }).settle i ((sys.actor i).recover (k.cell i).state)

def boot (sys : System σ) [Hashable σ.Id] : Kernel sys × List (Command σ) :=
  sys.boot.foldl (fun acc i => ((acc.1.startActor i).1, acc.2 ++ (acc.1.startActor i).2)) ({}, [])

def accept (k : Kernel sys) (x : σ.In) : Step sys :=
  { kernel := { k with queue := k.queue.push ⟨none, (sys.accept x).1, (sys.accept x).2⟩ }
    events := [.input x] }

/-- Take the oldest message. If its receiver is down, start the receiver and leave the message
queued; otherwise the receiver handles it. `none` when nothing is queued. -/
def run1 (k : Kernel sys) : Option (Step sys) :=
  match k.queue.pop? with
  | none => none
  | some (e, rest) =>
    if (k.cell e.dst).up then
      let r := ({ k with queue := rest }).handle e.dst e.msg
      some { kernel := r.1, events := .deliver e :: (outputs r.2).map .output, commands := r.2 }
    else
      let r := k.startActor e.dst
      some { kernel := r.1, events := .start e.dst :: (outputs r.2).map .output, commands := r.2 }

/-- A timer the shell armed has fired. It counts only if its token is still the pending one. -/
def fire (k : Kernel sys) (i : σ.Id) (msg : σ.Msg i) (token : Nat) : Step sys :=
  let c := k.cell i
  if c.up && c.timers.contains (msg, token) then
    let r := (k.setCell i { c with timers := c.timers.eraseP (·.1 = msg) }).handle i msg
    { kernel := r.1, events := .timeout i msg :: (outputs r.2).map .output, commands := r.2 }
  else { kernel := k }

/-- Everything a shell can ask of a kernel. -/
inductive Op (σ : Signature) where
  | input (x : σ.In)
  | run
  | fire (i : σ.Id) (msg : σ.Msg i) (token : Nat)

def apply (k : Kernel sys) : Op σ → Step sys
  | .input x => k.accept x
  | .run => k.run1.getD { kernel := k }
  | .fire i msg token => k.fire i msg token

def exec (k : Kernel sys) : List (Op σ) → Kernel sys × List (Event σ)
  | [] => (k, [])
  | op :: ops =>
    let r := k.apply op
    let rest := r.kernel.exec ops
    (rest.1, r.events ++ rest.2)

end Kernel

end Lanes
