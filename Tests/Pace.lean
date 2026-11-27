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

/-- `batches` batches, each costing `inline_ns` or `pool_ns` a unit as it runs on the shard's
thread or on `workers` threads; the pace after them and, for each, whether it ran on the pool. -/
def simulate (p : Pace) (inline_ns pool_ns batches : Nat) (workers : Nat := 4) :
    Pace × List Bool :=
  (List.range batches).foldl (init := (p, [])) fun (p, ran) _ =>
    let spread := p.spread config workers
    let pooled := decide (1 < spread.workers)
    (p.observe config workers spread ((if pooled then pool_ns else inline_ns) * 100) 100,
      ran ++ [pooled])

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
  #[.append #[], .record #[.input (0, 1), .deliver ⟨none, 0, 1⟩, .output 1, .start 1,
    .timeout 2 0], .handOver #[1], .record #[.deliver ⟨none, 2, 3⟩]]

def tests : List (String × Bool) :=
  let (_, cheap) := simulate {} 500 2500 500
  let (_, heavy) := simulate {} 30000 9000 1000
  let (_, slower) := simulate {} 30000 40000 1000
  let (onPool, _) := simulate {} 30000 9000 300
  let (offPool, left) := simulate onPool 500 2500 300
  let (_, back) := simulate offPool 30000 9000 300
  let (moderate, _) := simulate {} 4000 3000 10
  [ ("pace: cheap work stays on the shard's thread, and the pool is never tried",
      pooled cheap == 0),
    ("pace: costly work goes to the pool when it is faster, the other way tried rarely",
      cheap.length == 500 && heavy.head? == some false && pooled heavy ≥ 980),
    ("pace: costly work stays on the shard's thread when the pool is slower",
      pooled slower ≤ 20 && ((slower.drop 2).take 60).all (!·)),
    ("pace: when the work becomes cheap the pool is left within a few batches",
      (left.take 5).all id && (left.drop 12).all (!·) && !offPool.pooled),
    ("pace: and when it becomes costly again the pool is taken again within a few",
      pooled (back.drop 3) ≥ 290),
    ("pace: a piece of a wave holds at least 20 µs of work at the shard's rate",
      (moderate.spread config 4).minPiece == 5 && (moderate.spread config 4).workers == 4),
    ("pace: on one worker the pool is never taken",
      pooled (simulate {} 30000 9000 100 (workers := 1)).2 == 0),
    ("pace: the units of a batch are its deliveries, timer firings and starts",
      Pace.work acts == 4) ]

end Tests.Pace
