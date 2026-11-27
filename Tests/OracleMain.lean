/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Oracle.All
import Tests.Oracle.Run

/-!
`lake exe lanesOracle [--cases N] [--seed S] [--record] [package…]`: Lanes's pure oracles
(`oracles/README.md`) against their references, which it builds or sets up first.
-/

def main (args : List String) : IO UInt32 :=
  Tests.Oracle.main "lanesOracle" "." Tests.Oracle.packages args
