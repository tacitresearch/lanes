/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
The process `Tests/Ops.lean` stops by SIGTERM: `lanesStopChild drain_ms`, a binary of its own
that imports `Lanes` alone, so that it starts at once. As part of `lanesTest`, each start ran
the initialisation of every test module.
-/

namespace Tests.StopChild

open Lanes Lanes.Http Std Std.Async

inductive Job where
  | ask (id : ReqId)
  | done (id : ReqId)
  deriving DecidableEq, Repr, Hashable

inductive Work where
  | reply (id : ReqId)
  | start (id : ReqId)
  deriving DecidableEq, Repr, Hashable

/-- Answers a request once the work it starts is reported done. -/
def slow : Service Job Work Unit where
  init := ()
  step _
    | .ask id => ((), [.start id])
    | .done id => ((), [.reply id])

def slowBridge : Bridge (Server.sig Job Work) where
  decode id _ := .ok (.ask id)
  encode
    | .reply id => some (id, .text "done\n")
    | .start _ => none

abbrev Slow := admittedFronted (Server.system slow) slowBridge

/-- A server whose work is done when a line arrives on standard input, and never if it ends
first, stopped by a signal. It says on standard output when it is listening and when work has
started. -/
def run (drain_ms : Nat) : IO Unit := do
  let out ← IO.getStdout
  let say (line : String) : IO Unit := do
    out.putStrLn line
    out.flush
  let held : IO.Ref (Option (Http.Server Slow)) ← IO.mkRef none
  let onOutput : Work → Async Unit
    | .start id => do
      say "working"
      discard <| IO.asTask (prio := .dedicated) do
        let line ← (← IO.getStdin).getLine
        if let (some server, false) := (← held.get, line.isEmpty) then
          discard <| Lanes.block (server.tryInput (.done id))
    | .reply _ => pure ()
  Lanes.block do
    let server ← serveFronted (Server.system slow) slowBridge
      { port := 0, ops := { readinessPath := some "/readyz" } } {} onOutput
    held.set (some server)
    server.stopOnSignal drain_ms (listening := say s!"listening {server.port.getD 0}")

end Tests.StopChild

def main : List String → IO UInt32
  | [drain_ms] => do
    Tests.StopChild.run drain_ms.toNat!
    return 0
  | _ => do
    IO.eprintln "usage: lanesStopChild drain_ms"
    return 2
