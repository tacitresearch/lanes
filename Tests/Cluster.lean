/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank
import Tests.Runtime

/-!
One system on several shards. The bank's accounts live on different shards, so transfers cross
between them; the flooders check that messages from one actor to another keep their order
across shards; and a workload of pure computation measures what the extra threads buy.
-/

namespace Tests.Cluster

open Lanes Std.Async Examples.Bank

def bankTest (shards : Nat) : Async (List (String × Bool)) := do
  let responses ← IO.mkRef 0
  let cluster ← Cluster.start (bank (Fin 3) 100) shards {} fun _ => responses.modify (· + 1)
  let clients := (List.finRange 3).toArray.map fun (k : Fin 3) => (do
    for n in [0:200] do
      cluster.input (.transfer ⟨k.val * 1000 + n, k, k + 1, n % 7⟩) : Async Unit)
  discard <| Async.concurrentlyAll clients
  cluster.idle
  let balances ← (List.finRange 3).mapM fun a => return (← cluster.state a).balance
  let homes := (List.finRange 3).map (Cluster.home (σ := sig (Fin 3)) shards)
  cluster.stop
  return [
    (s!"cluster of {shards}: accounts on different shards, money conserved once idle",
      balances.sum == 300 && (shards == 1 || homes.eraseDups.length > 1)),
    (s!"cluster of {shards}: every request answered", (← responses.get) == 600) ]

def floodTest : Async (List (String × Bool)) := do
  let cluster ← Cluster.start Tests.Runtime.flood 3
  discard <| Async.concurrentlyAll #[cluster.input (0, 200), cluster.input (1, 200)]
  cluster.idle
  let states ← (List.finRange 2).mapM fun k => cluster.state k
  cluster.stop
  return [("cluster: self-sends and a cycle of sends across shards all arrive",
    states == [(200, 200), (200, 200)])]

/-! What the threads buy: actors that each do a fixed amount of pure work per message. -/

abbrev workSig : Signature where
  Id := Nat
  Msg _ := Nat
  In := Nat × Nat

def work (n : Nat) : Nat :=
  (List.range n).foldl (fun acc k => (acc * 31 + k) % 1000003) 7

abbrev workers : System workSig where
  State _ := Nat
  actor _ := { init := 0, step := fun s n => ((s + work n) % 1000003, []),
               recover := fun s => (s, []) }
  accept x := ⟨x.1, x.2⟩

def elapsed (shards : Nat) : Async (Nat × List Nat) := do
  let cluster ← Cluster.start workers shards
  let t0 ← IO.monoMsNow
  for round in [0:60] do
    for actor in [0:8] do cluster.input (actor, 20000 + round)
  cluster.idle
  let ms := (← IO.monoMsNow) - t0
  let states ← (List.range 8).mapM fun actor => cluster.state actor
  cluster.stop
  return (ms, states)

def speedTest : Async (List (String × Bool)) := do
  let (one, expected) ← elapsed 1
  let (four, states) ← elapsed 4
  IO.println s!"cluster: 480 units of work take {one} ms on 1 shard, {four} ms on 4"
  return [("cluster: four shards compute what one shard computes", states == expected)]

def tests : IO (List (String × Bool)) := do
  return (← (bankTest 1).block) ++ (← (bankTest 4).block) ++ (← floodTest.block)
    ++ (← speedTest.block)

end Tests.Cluster
