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

Each way keeps a rate: the nanoseconds and units of work of the batches it ran, each batch
weighing an eighth less than the one after it. Work cheaper than `cheap_ns` a unit on the shard's
thread stays there, and the pool is not tried. Costlier work is tried on the pool, and the faster
way is kept: the other is taken when it is faster by an eighth.

The way not in use is run again for one batch, to see whether it has become the faster, in two
cases. When the rate of the way in use has halved or doubled since the other was last run, the
work has changed. Otherwise after `probeEvery` batches times how much slower the other way was,
so that the batches run the slower way cost about one in `probeEvery` at most. The pool cannot
be more than `workers` times faster, so the rate of the shard's thread is read as at most that
many times the pool's.

A wave on the pool is cut into pieces of at least `piece_ns` of work at the rate of the shard's
thread, so a narrow wave of cheap steps is left to the kernel (`Kernel.Spread.minPiece`).
-/

@[expose] public section

namespace Lanes.Pace

structure Config where
  /-- Work cheaper than this a unit on the shard's thread is never tried on the pool: handing a
  message to another thread costs about a microsecond (D64). -/
  cheap_ns : Nat := 2000
  /-- The least work in a piece of a wave, which costs a task and the wake-up of a thread. -/
  piece_ns : Nat := 20000
  probeEvery : Nat := 64
  probeAtMost : Nat := 1024
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
  inline : Pace.Rate := {}
  pool : Pace.Rate := {}
  /-- The way in use. -/
  pooled : Bool := false
  /-- Batches run the way in use since the other was last run. -/
  since : Nat := 0
  /-- The rate of the way in use when the other was last run; `0` if not known. -/
  base : Nat := 0
  deriving Repr

namespace Pace

/-- Nanoseconds a unit of work on the shard's thread and on the pool, when both are known, the
first at most `workers` times the second. -/
def rates (workers : Nat) (p : Pace) : Option (Nat × Nat) :=
  match p.inline.perUnit, p.pool.perUnit with
  | some i, some q => some (min i (q * max 1 workers), q)
  | _, _ => none

def cheap (c : Config) (workers : Nat) (p : Pace) : Bool :=
  match p.rates workers, p.inline.perUnit with
  | some (i, _), _ | none, some i => i < c.cheap_ns
  | none, none => true

/-- The rates of the way in use and of the other. -/
def ways (p : Pace) (rates : Nat × Nat) : Nat × Nat :=
  if p.pooled then (rates.2, rates.1) else rates

/-- The way to use, as last measured: the shard's thread for cheap work, the pool when it is
untried, and otherwise the way in use unless the other is faster by an eighth. -/
def prefer (c : Config) (workers : Nat) (p : Pace) : Bool :=
  if p.cheap c workers then false
  else
    match p.rates workers with
    | none => true
    | some rates =>
      let (now, other) := p.ways rates
      if other + other / 8 < now then !p.pooled else p.pooled

/-- How many batches the way in use runs before the other is run again. -/
def probeAfter (c : Config) (now other : Nat) : Nat :=
  min c.probeAtMost (c.probeEvery * max 1 (other / max 1 now))

/-- Whether the next batch is to run on the pool. -/
def choose (c : Config) (workers : Nat) (p : Pace) : Bool :=
  if workers ≤ 1 || p.cheap c workers then false
  else
    match p.rates workers with
    | none => p.pooled
    | some rates =>
      let (now, other) := p.ways rates
      let changed := p.base != 0 && (2 * p.base ≤ now || 2 * now ≤ p.base)
      if changed || probeAfter c now other ≤ p.since then !p.pooled else p.pooled

/-- The spread of the next batch: on the shard's thread, or on up to `workers` threads in pieces
of at least `piece_ns` of work. -/
def spread (c : Config) (workers : Nat) (p : Pace) : Kernel.Spread :=
  if p.choose c workers then
    let unit_ns := (p.rates workers).elim (p.inline.perUnit.getD 1) (·.1)
    { workers, minPiece := max 1 (c.piece_ns / max 1 unit_ns) }
  else {}

def rateOf (p : Pace) (pooled : Bool) : Nat :=
  ((if pooled then p.pool else p.inline).perUnit).getD 0

/-- A batch ran with `spread`, taking `ns` for `units` units of work. A batch run the way not in
use replaces that way's rate, which was old. -/
def observe (c : Config) (workers : Nat) (p : Pace) (spread : Kernel.Spread) (ns units : Nat) :
    Pace :=
  let pooled := decide (1 < spread.workers)
  let p : Pace :=
    if pooled = p.pooled then
      let p : Pace := if pooled then { p with pool := p.pool.add ns units }
        else { p with inline := p.inline.add ns units }
      { p with since := p.since + 1, base := if p.base = 0 then p.rateOf pooled else p.base }
    else
      let p : Pace := if pooled then { p with pool := { ns, units } }
        else { p with inline := { ns, units } }
      { p with since := 0, base := p.rateOf p.pooled }
  let next := p.prefer c workers
  if next = p.pooled then p else { p with pooled := next, since := 0, base := p.rateOf next }

/-- The units of work in a batch: the messages delivered, the timers fired, the actors
started. -/
def work {σ : Signature} {sys : System σ} {P : σ.Id → Type} (acts : Array (Batch.Act sys P)) :
    Nat :=
  acts.foldl (init := 0) fun
    | n, .record events => events.foldl (init := n) fun
      | n, .deliver _ | n, .timeout .. | n, .start _ => n + 1
      | n, _ => n
    | n, _ => n

end Lanes.Pace
