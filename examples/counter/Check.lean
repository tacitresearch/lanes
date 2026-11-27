import Lanes
import Counter.Counter

/-!
Model checks for the counter, on a small instance: a limit of 2 and four requests in any order.
Every invariant has a `sometimes` property next to it that shows the interesting states are
reached (rule 5.3).
-/

open Lanes Counter

instance : sig.Inspect := {}
instance : (system { limit := 2 }).Inspect := {}

def requests : List Request :=
  [.increment 1, .increment 2, .increment 3, .read 4]

def main : IO UInt32 := do
  let report := Check.system (system { limit := 2 })
    { driver := (service { limit := 2 }).monitored (Driver.anyOrder requests) }
    [ Check.refines "every response is allowed by the spec",
      .always "the counter never exceeds its limit" fun w => w.state.state () ≤ 2,
      .sometimes "the counter reaches its limit" fun w => w.state.state () == 2,
      .sometimes "an increment is refused" fun w => w.state.outbox.any (!·.applied) ]
  IO.println report.renderSystem
  return if report.ok then 0 else 1
