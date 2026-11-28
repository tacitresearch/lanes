/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Check
import Videos.EndToEnd
import Lanes.Testing

/-!
`lake test`: the model checks, the bridge without a socket, and the site over HTTP.
`lake exe videosTest <word>…` runs only the model checks whose names contain one of the words;
`lake exe videosTest http`, only the bridge and the site over HTTP.
-/

def main (args : List String) : IO UInt32 := do
  let checks := Lanes.Testing.Result.tests (kind := .check)
  let http := do
    return Lanes.Testing.Result.tests (Videos.EndToEnd.bridgeTests
      ++ Videos.EndToEnd.sharedCacheTests ++ (← Videos.EndToEnd.run))
  let names := args.filter (· != "--json")
  let quiet := Lanes.Testing.wantsJson args
  let results ← if names.isEmpty then do
      pure (checks (← Videos.Check.run [] quiet) ++ checks Videos.Check.capTests ++ (← http))
    else if names == ["http"] then http
    else pure (checks (← Videos.Check.run names quiet))
  Lanes.Testing.report args results
