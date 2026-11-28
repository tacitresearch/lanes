/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Waves

/-! How wide the waves of the site's journal are, with an actor and a scheduler for each member
and the reads from the members' states (`Videos.Waves`).

- `videosWaves [actions]`: the waves of entries applied whole (`Lanes.WavePlan.split`).
- `videosWaves kernel [actions]`: the kernel's waves (`Kernel.waves`), which take each message
  on its own, for the same workload taken a batch at a time.
- `videosWaves time [workers] [runs] [actions]`: how long the batches take, run to quiet on one
  thread (`Kernel.runBatch`), in waves on `workers` threads (`Kernel.runWaves`), and as `auto`
  chooses (`Pace`); for each, the median over `runs` of the p50 and p99 of a batch's time,
  counted once for each entry of the batch, which waits for the whole batch, and of the entries
  a second. -/

open Lanes Videos Videos.Waves

def entryWaves (actions : Nat) : IO Unit := do
  IO.println "| Views | Batch | Waves per batch | Entries per wave | In waves of 2 or more | In waves of 8 or more |"
  IO.println "| --- | --- | --- | --- | --- | --- |"
  let mut notes := #[]
  for popular in [true, false] do
    let w : Workload := { actions, popular }
    let d := run w
    let es := d.log.toList
    for n in [64, 256] do
      IO.println (Stats.row (if popular then "by popularity" else "uniform") (measure n es))
    notes := notes.push s!"- Views {if popular then "by popularity" else "uniform"}: {w.members} members, {d.ready.size} videos ready at the end, {d.actions} actions of which {d.reads} reads, {es.length} entries; the actor most entries touch: {hottest es}"
  IO.println ""
  for n in notes do IO.println n

/-- The kernel's waves: for each batch, the messages and the steps one after another that its
waves need with a thread for each receiver, the most messages one receiver has in a wave being
the wave's length. -/
def kernelTable (actions : Nat) : IO Unit := do
  IO.println "| Views | Batch | Entries | Waves per batch | Messages per wave | Receivers per wave | Messages over the longest receiver's |"
  IO.println "| --- | --- | --- | --- | --- | --- | --- |"
  for popular in [true, false] do
    let w : Workload := { actions, popular }
    for n in [64, 256] do
      let batches := batchWaves w n
      let waves := batches.flatten
      let messages := waves.foldl (· + ·.messages) 0
      let actors := waves.foldl (· + ·.actors) 0
      let longest := waves.foldl (· + ·.most) 0
      let entries := (batchEntries w n)
      IO.println s!"| {if popular then "by popularity" else "uniform"} | {n} | {entries} | \
        {ratio waves.length batches.length} | {ratio messages waves.length} | \
        {ratio actors waves.length} | {ratio messages longest} |"
where
  batchEntries (w : Workload) (n : Nat) : Nat := Id.run do
    let mut d := warm w
    let mut count := 0
    for _ in [0:w.actions + 1] do
      if w.actions ≤ d.actions then break
      let (batch, d') := d.gather w n
      let (k, d') := d'.begin batch
      d := d'
      count := count + batch.length
      match k.runBatch 1000000 with
      | { kernel, outputs, .. } => d := d.settle kernel batch outputs
    return count

inductive Way where
  | serial
  | waves
  | auto
  deriving Inhabited

/-- Each batch's time and entries, and how many batches ran on the pool. -/
def timeRun (w : Workload) (n workers : Nat) (way : Way) : IO (Array (Nat × Nat) × Nat) := do
  let mut d := warm w
  let mut pace : Pace := {}
  let mut out := #[]
  let mut pooled := 0
  let mut last_ns ← IO.monoNanosNow
  while d.actions < w.actions do
    let (batch, d') := d.gather w n
    if batch.isEmpty then
      d := d'
      continue
    let (k, d') := d'.begin batch
    d := d'
    let spread : Kernel.Spread := match way with
      | .serial => {}
      | .waves => { workers }
      | .auto => pace.spread {} workers
    let start ← IO.monoNanosNow
    match k.runWaves spread 1000000 with
    | { kernel, outputs, events } =>
      let units := events.foldl (init := 0) fun
        | n, .deliver _ | n, .timeout .. | n, .start _ => n + 1
        | n, _ => n
      -- The branch makes the run happen before the clock is read again.
      if units == 0 && outputs.length == 7 then IO.println ""
      let end_ns ← IO.monoNanosNow
      out := out.push (end_ns - start, batch.length)
      if 1 < spread.workers then pooled := pooled + 1
      pace := pace.observe {} workers spread (end_ns - start) units (end_ns - last_ns)
      last_ns := end_ns
      d := d.settle kernel batch outputs
  return (out, pooled)

def percentile (sorted : Array Nat) (perMille : Nat) : Nat :=
  if sorted.isEmpty then 0 else sorted[min (sorted.size - 1) (sorted.size * perMille / 1000)]!

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s[s.size / 2]!

def spreadPct (xs : Array Nat) : Nat :=
  (xs.foldl max 0 - xs.foldl min xs[0]!) * 100 / max 1 (median xs)

def time (workers runs actions : Nat) : IO Unit := do
  IO.println s!"{workers} workers, {runs} runs, {actions} actions"
  IO.println "| Views | Batch | Way | p50 µs | p99 µs | entries/s | batches on the pool |"
  IO.println "| --- | --- | --- | ---: | ---: | ---: | ---: |"
  let ways := [("serial", Way.serial), ("waves", .waves), ("auto", .auto)]
  for popular in [true, false] do
    let w : Workload := { actions, popular }
    for n in [1, 64, 256] do
      let mut p50s := Array.replicate ways.length #[]
      let mut p99s := Array.replicate ways.length #[]
      let mut rates := Array.replicate ways.length #[]
      let mut pools := Array.replicate ways.length #[]
      for r in [0:runs] do
        for j in [0:ways.length] do
          let m := (j + r) % ways.length
          let (batches, pooled) ← timeRun w n workers (ways[m]!).2
          -- Each entry waits for its whole batch.
          let lat := batches.flatMap fun (ns, k) => Array.replicate k ns
          let sorted := lat.qsort (· < ·)
          let total := batches.foldl (· + ·.1) 0
          p50s := p50s.modify m (·.push (percentile sorted 500))
          p99s := p99s.modify m (·.push (percentile sorted 990))
          rates := rates.modify m (·.push (lat.size * 1000000000 / max 1 total))
          pools := pools.modify m (·.push (pooled * 100 / max 1 batches.size))
      for ((name, _), m) in ways.zipIdx do
        let us := fun (xs : Array Nat) => s!"{(median xs + 500) / 1000} ({spreadPct xs}%)"
        IO.println s!"| {if popular then "by popularity" else "uniform"} | {n} | {name} | \
          {us p50s[m]!} | {us p99s[m]!} | {median rates[m]!} ({spreadPct rates[m]!}%) | \
          {median pools[m]!}% |"

def main (args : List String) : IO Unit := do
  let num (i : Nat) (d : Nat) := (args[i]? >>= String.toNat?).getD d
  match args.head? with
  | some "kernel" => kernelTable (num 1 20000)
  | some "time" => time (num 1 4) (max 1 (num 2 3)) (num 3 20000)
  | _ => entryWaves (num 0 20000)
