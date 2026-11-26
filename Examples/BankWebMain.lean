/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Examples.BankWeb

/-!
The executable of the bank web example: `lake exe bankWeb [port] [journal]`. With a journal
file the balances survive the process: transfer, `kill -9`, start again.
-/

open Lanes Examples.Bank Examples.BankWeb in
def main (args : List String) : IO Unit := do
  let port := (args.head? >>= String.toNat?).getD 8080
  let journal := args[1]?.map System.FilePath.mk
  let server ← (Http.serve (bank Acct 100) bridge { port := port.toUInt16, journal }).block
  IO.println s!"Lanes Bank listening on http://127.0.0.1:{server.port.getD 0}"
  (← IO.getStdout).flush
  server.wait.block
