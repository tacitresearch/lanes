/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! `Lanes.Http.serve` with one actor that answers each request it is handed:
`benchLanes [port] [journal] [snapshotEvery]`. With a journal every request is appended and
flushed before it is answered; with `snapshotEvery` the kernel is also saved and the journal
cut that often. -/

open Lanes Lanes.Http

abbrev helloSig : Signature := Server.sig ReqId ReqId

def hello : Service helloSig Unit where
  init := ()
  step _ id := ((), [id])

def bridge : Bridge helloSig where
  decode id _ := .ok id
  encode id := some (id, .text "hello\n")

def saving : Http.Saving (Server.system hello) :=
  { actors := { id := Codec.unit, state := fun _ => Codec.unit, msg := fun _ => Codec.nat }
    out := Codec.nat }

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8093
  let journal := args[1]?.map System.FilePath.mk
  let snapshotEvery := args[2]? >>= String.toNat?
  let config : Http.ServerConfig := { port := port.toUInt16, journal, system := "bench 1" }
  let runtimeConfig : Runtime.Config := { snapshotEvery := snapshotEvery.getD 65536 }
  let server ← (Http.serve (Server.system hello) bridge config runtimeConfig
    (snapshotEvery.map fun _ => saving)).block
  IO.println s!"listening on {server.port.getD 0}"
  (← IO.getStdout).flush
  server.wait.block
