/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! The kernel alone, without IO: `benchWaves [K] [spin] [workers] [inputs] [rounds]` accepts
`inputs` messages spread over `K` counters, as `LanesMany.lean`'s, and runs them to quiet with
`Kernel.runWaves`, `rounds` times, and prints the time a message and the time a round. With
`workers` 1 it is `runBatch`. -/

open Lanes

def spin : Nat → UInt64 → UInt64
  | 0, h => h
  | n + 1, h => spin n (mixHash h n.toUInt64)

abbrev sig (n : Nat) : Signature where
  Id := Fin (n + 1)
  Msg _ := Nat
  In := Nat
  Out := Nat

structure Count where
  count : Nat := 0
  hash : UInt64 := 0

abbrev many (n work : Nat) : System (sig n) where
  State _ := Count
  actor _ := {
    init := {}
    step := fun s x => ({ count := s.count + 1, hash := spin work (s.hash + x.toUInt64) }, [.emit x])
    recover := fun s => (s, []) }
  accept x := ⟨Fin.ofNat (n + 1) x, x⟩
  boot := List.finRange (n + 1)

def main (args : List String) : IO Unit := do
  let arg (i : Nat) (d : Nat) := (args[i]? >>= String.toNat?).getD d
  let actors := max 1 (arg 0 64)
  let work := arg 1 20000
  let workers := arg 2 1
  let inputs := arg 3 256
  let rounds := arg 4 200
  let sys := many (actors - 1) work
  let mut k := (Kernel.boot sys).1
  let mut outputs := 0
  let start ← IO.monoNanosNow
  for r in [0:rounds] do
    let k1 := k.acceptAll ((List.range inputs).map (· + r * inputs))
    match k1.runWaves workers (inputs * 4) with
    | { kernel, outputs := out, .. } =>
      k := kernel
      outputs := outputs + out.length
  let ns := (← IO.monoNanosNow) - start
  IO.println s!"{actors} actors, spin {work}, {workers} workers: {outputs} messages, \
    {ns / max 1 outputs} ns a message, {ns / 1000000 / max 1 rounds} ms a round of {inputs}"
