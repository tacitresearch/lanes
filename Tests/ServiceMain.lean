/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.Service.All

/-!
`lake exe lanesServiceOracle [--record] [oracle…]`: Lanes's service oracles (`oracles/README.md`)
against the services `LANES_MOTO` and `LANES_POSTGRES` name; each is skipped, with a message,
when its variable is not set. `oracles/moto/run.sh` and `oracles/postgres/run.sh` start a
service, run them and stop it.
-/

def main (args : List String) : IO UInt32 :=
  Tests.Oracle.Service.main "lanesServiceOracle" "." Tests.Oracle.Service.oracles args
