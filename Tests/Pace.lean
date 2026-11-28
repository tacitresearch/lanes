/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The pace on made-up timings: a batch of 100 units costs a given number of nanoseconds a unit on
the shard's thread and another on the pool, and the pace chooses each next batch as the shell
asks it to. Whatever it chooses, the batch is the same (`Batch.run_spread`); these check that it
chooses the faster way, leaves the pool when the work changes, and tries the slower way rarely.
-/

namespace Tests.Pace

open Lanes

def config : Pace.Config := {}

/-- `batches` batches of 100 units, each costing `inline_ns` or `pool_ns` a unit as it runs on
the shard's thread or on `workers` threads, and the shard idle for `idle_ns` a unit between two;
the pace after them and, for each batch, whether it ran on the pool. -/
def simulate (p : Pace) (inline_ns pool_ns batches : Nat) (workers : Nat := 4)
    (idle_ns : Nat := 0) : Pace × List Bool :=
  (List.range batches).foldl (init := (p, [])) fun (p, ran) _ =>
    let spread := p.spread config workers
    let pooled := decide (1 < spread.workers)
    let ns := (if pooled then pool_ns else inline_ns) * 100
    (p.observe config workers spread ns 100 (ns + idle_ns * 100), ran ++ [pooled])

/-- As `simulate`, for actors whose states are large and whose steps are cheap: a unit costs
`inline_ns` on the shard's thread, but the first batch costs `copy_ns` a unit, which copies the
states the actors start with, and so do every batch on the pool and the first batch on the shard's
thread after one, which copy the states the pool's threads have seen. -/
def simulateCopies (inline_ns copy_ns batches : Nat) : Pace × List Bool :=
  (List.range batches).foldl (init := ({}, [])) fun (p, ran) n =>
    let spread := p.spread config 4
    let pooled := decide (1 < spread.workers)
    let ns := (if n = 0 || pooled || ran.getLast? = some true then copy_ns else inline_ns) * 100
    (p.observe config 4 spread ns 100 ns, ran ++ [pooled])

def pooled (ran : List Bool) : Nat :=
  ran.countP id

abbrev sig : Signature where
  Id := Fin 3
  Msg _ := Nat
  In := Fin 3 × Nat
  Out := Nat

abbrev counters : System sig where
  State _ := Nat
  actor _ := { init := 0, step := fun s n => (s + n, []), recover := fun s => (s, []) }
  accept x := ⟨x.1, x.2⟩

def acts : Array (Batch.Act counters fun _ => Unit) :=
  #[.work #[], .record #[.input (0, 1), .deliver ⟨none, 0, 1⟩, .output 1, .start 1,
    .timeout 2 0], .handOver #[1], .record #[.deliver ⟨none, 2, 3⟩]]

def tests : List (String × Bool) :=
  let (_, cheap) := simulate {} 500 2500 500
  let (_, heavy) := simulate {} 30000 9000 1000
  let (_, slower) := simulate {} 30000 40000 1000
  let (onPool, _) := simulate {} 30000 9000 300
  let (offPool, left) := simulate onPool 500 2500 300
  let (_, back) := simulate offPool 30000 9000 300
  let (moderate, _) := simulate {} 4000 3000 12
  [ ("pace: cheap work stays on the shard's thread, and the pool is never tried",
      pooled cheap == 0),
    ("pace: costly work goes to the pool when it is faster, the other way tried rarely",
      cheap.length == 500 && heavy.head? == some false && pooled heavy ≥ 980),
    ("pace: costly work stays on the shard's thread when the pool is slower, tried less and less",
      pooled slower ≤ 25 && pooled ((slower.drop 2).take 30) ≤ 4
        && pooled ((slower.drop 200).take 64) ≤ 1),
    ("pace: when the work becomes cheap the pool is left within a few batches",
      (left.take 5).all id && (left.drop 12).all (!·) && !offPool.pooled),
    ("pace: and when it becomes costly again the pool is taken again within a few",
      pooled (back.drop 3) ≥ 285),
    ("pace: a piece of a wave holds at least 20 µs of work at the shard's rate",
      (moderate.spread config 4).minPiece == 5 && (moderate.spread config 4).workers == 4),
    ("pace: a shard that keeps up alone leaves the pool once it sees so, however costly its work",
      pooled (simulate {} 30000 9000 300 (idle_ns := 30000)).2 ≤ 1),
    ("pace: a shard that would be behind alone takes the pool, and keeps it once it keeps up",
      pooled ((simulate {} 30000 9000 300 (idle_ns := 3000)).2.drop 2) ≥ 285),
    ("pace: the pool is not tried on the word of a shard's first few steps, however costly",
      ((({} : Pace).observe config 4 {} 3000000 2 3000000).spread config 4).workers == 1
        && ((({} : Pace).observe config 4 {} 3000000 100 3000000).spread config 4).workers == 4),
    ("pace: steps that only copy large states leave the pool at its first look, for good",
      let ran := (simulateCopies 500 30000 300).2
      pooled ran ≤ config.probeFirst && (ran.drop (config.probeFirst + 4)).all (!·)),
    ("pace: on one worker the pool is never taken",
      pooled (simulate {} 30000 9000 100 (workers := 1)).2 == 0),
    ("pace: the units of a batch are its deliveries, timer firings and starts",
      Pace.work acts == 4) ]

end Tests.Pace
