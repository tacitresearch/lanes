/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! The shell without IO adapters, `parallel` off, on and auto: `benchAuto [workers] [runs]
[scale] [workload…]`, every workload when none is named. A workload is a list of phases, each a
number of inputs sent to `K` counters as fast as the inbox takes them, input `n` to counter
`n % K`, whose step mixes a hash `spin` times; the shard runs to idle after each phase. Every
run starts a fresh shard. The modes take turns, `runs` times, and the table gives the median
time a message of each and the spread over the runs, (highest − lowest) / median; for auto also
the share of batches it ran on the pool. -/

open Lanes Std.Async

def spin : Nat → UInt64 → UInt64
  | 0, h => h
  | n + 1, h => spin n (mixHash h n.toUInt64)

abbrev sig : Signature where
  Id := Fin 64
  Msg _ := Nat
  In := Fin 64 × Nat
  Out := UInt64

structure Count where
  count : Nat := 0
  hash : UInt64 := 0

abbrev counters : System sig where
  State _ := Count
  actor _ := {
    init := {}
    step := fun s work =>
      let hash := spin work (s.hash + s.count.toUInt64)
      ({ count := s.count + 1, hash }, [.emit hash])
    recover := fun s => (s, []) }
  accept x := ⟨x.1, x.2⟩

/-- `inputs` inputs to `actors` counters, every `every`th step `spin` rounds and the others none. -/
structure Phase where
  actors : Nat
  spin : Nat
  inputs : Nat
  every : Nat := 1

def runOnce (config : Runtime.Config) (phases : List Phase) : IO (Nat × Nat × Runtime.Batches) :=
  Lanes.block do
    let rt ← Runtime.start counters config
    let start ← IO.monoNanosNow
    let mut messages := 0
    for p in phases do
      for n in [0:p.inputs] do
        rt.input (Fin.ofNat 64 (n % max 1 p.actors), if n % max 1 p.every == 0 then p.spin else 0)
      rt.idle
      messages := messages + p.inputs
    let ns := (← IO.monoNanosNow) - start
    let batches ← rt.batches
    rt.stop
    return (ns, messages, batches)

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s[s.size / 2]!

def show1 (ns : Nat) : String :=
  let tenths := (ns + 50) / 100
  s!"{tenths / 10}.{tenths % 10}"

def workloads (scale : Nat) : List (String × List Phase) :=
  let heavy := 20000
  [ ("trivial, wide (64 actors)", [{ actors := 64, spin := 0, inputs := 100000 * scale }]),
    ("trivial, narrow (1 actor)", [{ actors := 1, spin := 0, inputs := 100000 * scale }]),
    ("moderate, wide (spin 2000)", [{ actors := 64, spin := 2000, inputs := 20000 * scale }]),
    ("heavy, wide (spin 20000)", [{ actors := 64, spin := heavy, inputs := 3000 * scale }]),
    ("heavy, narrow (2 actors)", [{ actors := 2, spin := heavy, inputs := 2000 * scale }]),
    ("mixed steps, every other heavy",
      [{ actors := 64, spin := heavy, inputs := 4000 * scale, every := 2 }]),
    ("mixed phases, heavy and trivial",
      (List.range 3).flatMap fun _ =>
        [{ actors := 64, spin := heavy, inputs := 3000 * scale },
         { actors := 64, spin := 0, inputs := 50000 * scale }]) ]

def main (args : List String) : IO Unit := do
  let arg (i : Nat) (d : Nat) := (args[i]? >>= String.toNat?).getD d
  let workers := arg 0 4
  let runs := max 1 (arg 1 5)
  let scale := max 1 (arg 2 1)
  let only := (args.drop 3).filterMap String.toNat?
  let modes : List (String × Runtime.Config) :=
    [("off", { workers, parallel := .off }), ("on", { workers, parallel := .on }),
     ("auto", { workers, parallel := .auto })]
  IO.println s!"| workload | off µs/msg | on µs/msg | auto µs/msg | auto on the pool |"
  IO.println "| --- | ---: | ---: | ---: | ---: |"
  for ((name, phases), index) in (workloads scale).zipIdx do
    unless only.isEmpty || only.contains index do continue
    let mut times : Array (Array Nat) := #[#[], #[], #[]]
    let mut pooled : Array Nat := #[]
    for r in [0:runs] do
      for j in [0:3] do
        let m := (j + r) % 3
        let (ns, messages, batches) ← runOnce (modes.getD m ("", {})).2 phases
        times := times.modify m (·.push (ns / max 1 messages))
        if m == 2 then
          pooled := pooled.push (batches.pool * 100 / max 1 (batches.pool + batches.inline))
    let cell := fun (xs : Array Nat) =>
      let med := median xs
      let spread := (xs.foldl max 0 - xs.foldl min xs[0]!) * 100 / max 1 med
      s!"{show1 med} ({spread}%)"
    IO.println s!"| {name} | {cell times[0]!} | {cell times[1]!} | {cell times[2]!} | \
      {median pooled}% |"
