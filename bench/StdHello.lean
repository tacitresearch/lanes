/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Http

/-! `Std.Http.Server` with a handler that returns a constant: `benchStd [port] [maxRequests]`.
The server's configuration is the default, which is what `Lanes.Http.serve` runs, unless
`maxRequests` is given. -/

open Std Std.Async

def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8091
  let config : Std.Http.Config := match args[1]? >>= String.toNat? with
    | some n => { maxRequests := n }
    | none => {}
  let body := "hello\n".toUTF8
  let handler := Std.Http.Server.Handler.ofFn fun _ =>
    Std.Http.Response.ok.header! "content-type" "text/plain; charset=utf-8" |>.fromBytes body
  let server ← (Std.Http.Server.serve (.v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩) handler config).block
  IO.println s!"listening on {port}"
  (← IO.getStdout).flush
  server.waitShutdown.block
