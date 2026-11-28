/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! `Lanes.Http.serve` with `K` actors, each a counter: request `n` goes to actor `n % K`, which
counts it and answers. `benchMany [port] [K] [spin] [io=N] [workers=N]`:
each step first mixes a hash `spin` times, to stand for an actor whose step costs something;
`io` and `workers` as for `benchLanes`. -/

open Lanes Lanes.Http

def spin : Nat → UInt64 → UInt64
  | 0, h => h
  | n + 1, h => spin n (mixHash h n.toUInt64)

abbrev sig (n : Nat) : Signature where
  Id := Fin (n + 1)
  Msg _ := ReqId
  In := ReqId
  Out := ReqId

structure Count where
  count : Nat := 0
  hash : UInt64 := 0

def counter (n work : Nat) (i : Fin (n + 1)) : (sig n).Actor i Count where
  init := {}
  step s id :=
    ({ count := s.count + 1, hash := spin work (s.hash + id.toUInt64) }, [.emit id])
  recover s := (s, [])

abbrev many (n work : Nat) : System (sig n) where
  State _ := Count
  actor := counter n work
  accept id := ⟨Fin.ofNat (n + 1) id, id⟩

def bridge (n : Nat) : Bridge (sig n) where
  decode id _ := .ok id
  encode id := some (id, .text "hello\n")

def option (args : List String) (key : String) : Option Nat :=
  args.findSome? fun a => (a.dropPrefix? (key ++ "=")).bind (·.toString.toNat?)

def main (args : List String) : IO Unit := do
  let positional := args.filter (!·.contains '=')
  let port := (positional.head? >>= String.toNat?).getD 8094
  let actors := max 1 ((positional[1]? >>= String.toNat?).getD 64)
  let work := (positional[2]? >>= String.toNat?).getD 0
  let config : Http.ServerConfig :=
    { port := port.toUInt16, ioThreads := (option args "io").getD 0 }
  let runtimeConfig : Runtime.Config :=
    { workers := (option args "workers").getD 1 }
  let server ← (Http.serve (many (actors - 1) work) (bridge (actors - 1)) config runtimeConfig).block
  IO.println s!"listening on {server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
