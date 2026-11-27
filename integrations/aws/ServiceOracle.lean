/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Checks.SesMoto

/-!
`lake exe serviceOracle [--record]`: the SES adapter against the service `LANES_MOTO` names,
checked against the email model (`oracles/README.md`); skipped, with a message, when it is not
set. `oracles/moto/run.sh` starts moto, runs it and stops moto.
-/

def main (args : List String) : IO UInt32 :=
  Tests.Oracle.Service.main "serviceOracle" "../.." [Checks.SesMoto.oracle] args
