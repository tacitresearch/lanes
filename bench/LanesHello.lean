/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! `Lanes.Http.serve` with one actor that answers each request it is handed:
`benchLanes [port] [io=N] [workers=N] [parallel=on|auto|off]`. `io=N` runs the connections on N threads of the
server's own (`ServerConfig.ioThreads`), `workers=N` works out actors' steps on N threads
(`Runtime.Config.workers`), on every wave or as the shard's timing chooses (`parallel`). -/

open Lanes Lanes.Http

def hello : Service ReqId ReqId Unit where
  init := ()
  step _ id := ((), [id])

def bridge : Bridge (Server.sig ReqId ReqId) where
  decode id _ := .ok id
  encode id := some (id, .text "hello\n")

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
  let config : Http.ServerConfig := { port := port.toUInt16, ioThreads := (option args "io").getD 0 }
  let runtimeConfig : Runtime.Config :=
    { workers := (option args "workers").getD 1, parallel := parallel args }
  let server ← (Http.serve (Server.system hello) bridge config runtimeConfig).block
  IO.println s!"listening on {server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
