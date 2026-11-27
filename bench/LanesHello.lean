/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! `Lanes.Http.serve` with one actor that answers each request it is handed:
`benchLanes [port] [journal] [snapshotEvery] [io=N] [workers=N] [parallel=on|auto|off]`. With a
journal every request is appended and flushed before it is answered; with `snapshotEvery` the
kernel is also saved and the journal cut that often (`-` for neither). `io=N` runs the connections on N threads of the
server's own (`ServerConfig.ioThreads`), `workers=N` works out actors' steps on N threads
(`Runtime.Config.workers`), on every wave or as the shard's timing chooses (`parallel`). -/

open Lanes Lanes.Http

def hello : Service ReqId ReqId Unit where
  init := ()
  step _ id := ((), [id])

def bridge : Bridge (Server.sig ReqId ReqId) where
  decode id _ := .ok id
  encode id := some (id, .text "hello\n")

def saving : Http.Saving (Server.system hello) :=
  { actors := { id := Codec.unit, state := fun _ => Codec.unit, msg := fun _ => Codec.nat }
    out := Codec.nat }

/-- The value of `key=N` among the arguments. -/
def option (args : List String) (key : String) : Option Nat :=
  args.findSome? fun a => (a.dropPrefix? (key ++ "=")).bind (·.toString.toNat?)

/-- `parallel=off`, `on` or `auto`; `on` when not given, as `workers=N` alone always meant. -/
def parallel (args : List String) : Runtime.Parallel :=
  match args.findSome? (·.dropPrefix? "parallel=") |>.map (·.toString) with
  | some "off" => .off
  | some "auto" => .auto
  | _ => .on

def main (args : List String) : IO Unit := do
  let positional := args.filter (!·.contains '=')
  let port := (positional.head? >>= String.toNat?).getD 8093
  let journal := (positional[1]?.filter (· != "-")).map System.FilePath.mk
  let snapshotEvery := positional[2]? >>= String.toNat?
  let config : Http.ServerConfig :=
    { port := port.toUInt16, journal, system := "bench 1", ioThreads := (option args "io").getD 0 }
  let runtimeConfig : Runtime.Config :=
    { snapshotEvery := snapshotEvery.getD 65536, workers := (option args "workers").getD 1
      parallel := parallel args }
  let server ← (Http.serve (Server.system hello) bridge config runtimeConfig
    (snapshotEvery.map fun _ => saving)).block
  IO.println s!"listening on {server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
