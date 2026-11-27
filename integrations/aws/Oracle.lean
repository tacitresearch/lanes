/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Checks.Mail
import Checks.CloudFront
import Tests.Oracle.Run

/-!
`lake exe oracle [--cases N] [--seed S] [--record] [package…]`: the integration's pure oracles
against their references under the repository's `oracles/` (`oracles/README.md`).
-/

def main (args : List String) : IO UInt32 :=
  Tests.Oracle.main "oracle" "../.." [Checks.Mail.package, Checks.CloudFront.package] args
