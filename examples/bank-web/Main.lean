/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BankWeb

/-!
The executable of the bank web example: `lake exe bankWeb [port]`. The balances live as long
as the process: a restart opens every account again at 100.
-/

open Lanes Bank BankWeb in
def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let config : Http.ServerConfig := { port := port.toUInt16 }
  let server ← (Http.serve (bank Acct 100) bridge config).block
  IO.println s!"Lanes Bank listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  Lanes.block (server.stopOnSignal 10000)
