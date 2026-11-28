/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Election
import Tests.Scale
import Tests.HttpStream
import Tests.Cache
import Tests.MonitorSpeed
import Lanes.Testing

/-! The larger model checks (elections, connections that stream, a cache in front of a store), the
checker's speed and the scale benchmark. Run once per commit,
never in a repeat loop. `--json` prints the results as JSON. -/

def main (args : List String) : IO UInt32 := do
  let results := Tests.Election.tests ++ Tests.Election.fuzzTests ++ (← Tests.Election.speed)
    ++ (← Tests.Election.tasksTests) ++ (← Tests.Election.fingerprintTests) ++ (← Tests.Scale.tests) ++ (← Tests.HttpStream.checks)
    ++ (← Tests.Cache.checks) ++ (← Tests.MonitorSpeed.checks)
  Lanes.Testing.report args (Lanes.Testing.Result.tests results .check) (passes := false)
