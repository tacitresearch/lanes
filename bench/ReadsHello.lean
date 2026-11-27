/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! A counter behind `Lanes.Http.serve`, for reads answered from the state
(`docs/decisions/D75-reads.md`): `benchReads [port] [journal|-] [reads]`. `POST /inc` adds one,
`GET /` is a request that enters the system and is answered by the counter with its value, and
with `reads`, `GET /read` is answered from the counter's state without entering it. With a
journal every request that enters is appended and synced before it is answered. -/

open Lanes Lanes.Http

def counter : Service (ReqId × Bool) (ReqId × Nat) Nat where
  init := 0
  step n
    | (id, true) => (n + 1, [(id, n + 1)])
    | (id, false) => (n, [(id, n)])

def page (n : Nat) : Response := .text s!"{n}\n"

def bridge : Bridge (Server.sig (ReqId × Bool) (ReqId × Nat)) where
  decode id request := .ok (id, request.path == ["inc"])
  encode | (id, n) => some (id, page n)

def reads (request : Request) : Option (Read (Server.system counter)) :=
  if request.path == ["read"] then some { actor := (), answer := page } else none

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8094
  let journal := (args[1]?.filter (· != "-")).map System.FilePath.mk
  let config : Http.ServerConfig := { port := port.toUInt16, journal, system := "bench reads 1" }
  let server ← (Http.serve (Server.system counter) bridge config
    (reads := if args.contains "reads" then reads else fun _ => none)).block
  IO.println s!"listening on {server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block server.wait
