import Lanes
import Lanes.Testing
import Counter.Counter

/-!
Model checks for the counter, on a small instance: a limit of 2 and four requests in any order.
Every invariant has a `sometimes` property next to it that shows the interesting states are
reached (rule 5.3).

`lake test` runs this. It prints each check's report, then builds the proofs, which this file
does not import, so that a broken proof does not stop the checks. It exits 0 when every check
explored its whole instance and the proofs build, 1 when something failed, and 2 when a check
passed but hit a bound. `lake test -- --json` prints the results as JSON instead, each with its
kind: check or proof.
-/

open Lanes Counter

instance : sig.Inspect := {}
instance : (system { limit := 2 }).Inspect := {}

def requests : List Request :=
  [.increment 1, .increment 2, .increment 3, .read 4]

def main (args : List String) : IO UInt32 := do
  let report := Check.system (system { limit := 2 })
    { driver := (service { limit := 2 }).monitored (Driver.anyOrder requests) }
    [ Check.refines "every response is allowed by the spec",
      .always "the counter never exceeds its limit" fun w => w.state.state () ≤ 2,
      .sometimes "the counter reaches its limit" fun w => w.state.state () == 2,
      .sometimes "an increment is refused" fun w => w.state.outbox.any (!·.applied) ]
  Testing.report args
    [.check "the counter, with a limit of 2 and four requests" report report.renderSystem,
     ← Testing.build "the proofs" ["Counter.Proofs"]]
