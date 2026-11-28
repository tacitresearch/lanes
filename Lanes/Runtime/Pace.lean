/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Batch

/-!
Whether a shard's next batch works out its actors' steps on Lean's task pool or on the shard's
own thread, from the shard's timing of its recent batches. It chooses only how a batch runs:
whatever spread it gives, the batch is the same (`Batch.run_spread`).

The shell reports, for each batch that did work, its units of work, how long `Batch.run` took,
and how long since the end of the batch before: the batch's cycle, idle time included. Each is
kept as a rate, each batch weighing an eighth less than the one after it: the time a unit of work
takes on the shard's thread (`cost`), the cycle a unit while each way is in use (`inline`,
`pool`), and the cycle a unit whatever the way (`arrived`).

The pool is used only after the shard has done `firstUnits` units of work on its own thread,
for an actor's first steps pay for its start; only for work that costs at least `cheap_ns` a unit
on the shard's thread; and only while the work arriving would keep the shard's thread alone busy `busyOn` percent of the
time or more (then until it falls under `busyOff`): a shard that keeps up alone gains only a
shorter batch, and the pool's threads take cores the rest of the process may need. Then the way
with the shorter cycle is kept, the other taken when it is shorter by an eighth. Cycles and not
batches are compared because a pool that takes the cores of the threads that bring the inputs
makes batches shorter and the shard wait longer for the next.

The way not in use is run again for one batch in two cases: when the cycle of the way in use has
halved or doubled since the other was last run, for the work has changed; and after `probeEvery`
batches times how much longer the other's cycle was, so that the batches run the slower way cost
about one in `probeEvery` at most. A batch's time is noisy, so a way left on one batch's word is
tried again sooner: after `probeFirst` batches, then twice that, and so on while it stays the
slower. The pool cannot shorten a cycle more than `workers` times, so
the cycle on the shard's thread is read as at most that many times the pool's.

A wave on the pool is cut into pieces of at least `piece_ns` of work at the shard's rate, so a
narrow wave of cheap steps is left to the kernel (`Kernel.Spread.minPiece`).

The first batch on the shard's thread after a batch on the pool counts as the pool's. Lean never
updates in place an object another thread has seen, so that batch copies the state of every actor
the pool stepped, once. It is a cost of the pool: counted as the shard's, a state of a million
numbers makes its steps look costly, and the pool look no slower than the shard's thread.
-/

@[expose] public section

namespace Lanes.Pace

structure Config where
  /-- Work cheaper than this a unit on the shard's thread is never tried on the pool: handing a
  message to another thread costs about a microsecond (D64). -/
  cheap_ns : Nat := 2000
  /-- The least work in a piece of a wave, which costs a task and the wake-up of a thread. -/
  piece_ns : Nat := 20000
  /-- How busy the work arriving would keep the shard's thread alone, in percent, for the pool to
  be taken, and under which it is left. -/
  busyOn : Nat := 75
  busyOff : Nat := 50
  probeFirst : Nat := 8
  probeEvery : Nat := 64
  probeAtMost : Nat := 1024
  /-- The units of work a shard does on its own thread before it may try the pool; until then each
  batch's cost replaces the one before. An actor's first steps pay for its start, as a first write
  copies an initial state the system holds, and say little of the steps after them. -/
  firstUnits : Nat := 64
  deriving Repr

/-- Nanoseconds and units of work, each batch weighing an eighth less than the next. -/
structure Rate where
  ns : Nat := 0
  units : Nat := 0
  deriving Repr

def Rate.add (r : Rate) (ns units : Nat) : Rate :=
  { ns := r.ns - r.ns / 8 + ns, units := r.units - r.units / 8 + units }

def Rate.perUnit (r : Rate) : Option Nat :=
  if r.units = 0 then none else some (r.ns / r.units)

end Pace

structure Pace where
  cost : Pace.Rate := {}
  inline : Pace.Rate := {}
  pool : Pace.Rate := {}
  arrived : Pace.Rate := {}
  /-- The way in use. -/
  pooled : Bool := false
  /-- Batches run the way in use since the other was last run. -/
  since : Nat := 0
  /-- The cycle of the way in use when the other was last run; `0` if not known. -/
  base : Nat := 0
  /-- How many times in a row the other way was run and found the slower. -/
  confirmed : Nat := 0
  /-- The batch before ran on the pool. -/
  afterPool : Bool := false
  /-- The units of work done on the shard's thread, up to `firstUnits`. -/
  timed : Nat := 0
  deriving Repr

namespace Pace

/-- Nanoseconds a unit of work on the shard's thread. -/
def unit_ns (p : Pace) : Option Nat :=
  p.cost.perUnit

/-- How much of the time the work arriving would keep the shard's thread busy, in percent. -/
def busy (p : Pace) : Nat :=
  p.unit_ns.elim 0 fun i => p.arrived.units * i * 100 / max 1 p.arrived.ns

/-- Whether the pool may be used: the shard has timed enough of its work, the work is not cheap,
and the shard's thread alone would be behind. -/
def worth (c : Config) (p : Pace) : Bool :=
  c.firstUnits ≤ p.timed &&
    p.unit_ns.any fun i => c.cheap_ns ≤ i && (if p.pooled then c.busyOff else c.busyOn) ≤ p.busy

/-- The cycles a unit of the way in use and of the other, when both are known; the shard's
thread's at most `workers` times the pool's. -/
def cycles (workers : Nat) (p : Pace) : Option (Nat × Nat) :=
  match p.inline.perUnit, p.pool.perUnit with
  | some i, some q =>
    let i := min i (q * max 1 workers)
    some (if p.pooled then (q, i) else (i, q))
  | _, _ => none

/-- The way to use, as last measured: the shard's thread unless the pool is worth it, the pool
when it is untried, and otherwise the way in use unless the other is faster by an eighth. -/
def prefer (c : Config) (workers : Nat) (p : Pace) : Bool :=
  if !p.worth c then false
  else
    match p.cycles workers with
    | none => true
    | some (now, other) => if other + other / 8 < now then !p.pooled else p.pooled

/-- How many batches the way in use runs before the other is run again. -/
def probeAfter (c : Config) (confirmed now other : Nat) : Nat :=
  min (c.probeFirst * 2 ^ min confirmed 16)
    (min c.probeAtMost (c.probeEvery * max 1 (other / max 1 now)))

/-- Whether the next batch is to run on the pool. -/
def choose (c : Config) (workers : Nat) (p : Pace) : Bool :=
  if workers ≤ 1 || !p.worth c then false
  else
    match p.cycles workers with
    | none => p.pooled
    | some (now, other) =>
      let changed := p.base != 0 && (2 * p.base ≤ now || 2 * now ≤ p.base)
      if changed || probeAfter c p.confirmed now other ≤ p.since then !p.pooled else p.pooled

/-- The spread of the next batch: on the shard's thread, or on up to `workers` threads in pieces
of at least `piece_ns` of work. -/
def spread (c : Config) (workers : Nat) (p : Pace) : Kernel.Spread :=
  if p.choose c workers then
    { workers, minPiece := max 1 (c.piece_ns / max 1 (p.unit_ns.getD 1)) }
  else {}

def cycleOf (p : Pace) (pooled : Bool) : Nat :=
  ((if pooled then p.pool else p.inline).perUnit).getD 0

/-- A batch that did `units` units of work in a cycle of `cycle`, on the pool when `pooled`, `ns`
of it in `Batch.run`. A batch run the way not in use replaces that way's rates, which were old. -/
def record (c : Config) (workers : Nat) (p : Pace) (pooled : Bool) (ns units cycle : Nat) : Pace :=
  let probe := pooled != p.pooled
  let p : Pace := { p with arrived := p.arrived.add cycle units }
  let p : Pace := if pooled then p
    else { p with cost := if probe || p.timed < c.firstUnits then { ns, units }
                  else p.cost.add ns units,
                  timed := min c.firstUnits (p.timed + units) }
  let p : Pace :=
    if !probe then
      let p : Pace := if pooled then { p with pool := p.pool.add cycle units }
        else { p with inline := p.inline.add cycle units }
      { p with since := p.since + 1, base := if p.base = 0 then p.cycleOf pooled else p.base }
    else
      let p : Pace := if pooled then { p with pool := { ns := cycle, units } }
        else { p with inline := { ns := cycle, units } }
      { p with since := 0, base := p.cycleOf p.pooled, confirmed := p.confirmed + 1 }
  let next := p.prefer c workers
  if next = p.pooled then p
  else { p with pooled := next, since := 0, base := p.cycleOf next, confirmed := 0 }

/-- A batch ran with `spread` and did `units` units of work in `ns`, `elapsed_ns` after the end
of the batch before. Its cycle counts the time between at most three times the batch, so that a
shard that was idle long is soon seen busy again once it is, and not at all before the first
batch, when the shard was starting. The first batch on the shard's thread after the pool is the
pool's: it adds to the pool's cycle, and neither to the shard's cost nor to its cycle. -/
def observe (c : Config) (workers : Nat) (p : Pace) (spread : Kernel.Spread)
    (ns units elapsed_ns : Nat) : Pace :=
  let pooled := decide (1 < spread.workers)
  let cycle := if p.arrived.units = 0 then ns else max ns (min elapsed_ns (4 * ns))
  if !pooled && p.afterPool then
    { p with arrived := p.arrived.add cycle units, pool := p.pool.add cycle units,
             afterPool := false }
  else { p.record c workers pooled ns units cycle with afterPool := pooled }

/-- The units of work in a batch: the messages delivered, the timers fired, the actors
started. -/
def work {σ : Signature} {sys : System σ} {P : List σ.Id → Type} (acts : Array (Batch.Act sys P)) :
    Nat :=
  acts.foldl (init := 0) fun
    | n, .record events => events.foldl (init := n) fun
      | n, .deliver _ | n, .timeout .. | n, .start _ => n + 1
      | n, _ => n
    | n, _ => n

end Lanes.Pace
