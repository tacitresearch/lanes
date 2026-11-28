/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Check
import Videos.EndToEnd
import Lanes.Testing

/-!
`lake test`: the model checks at small bounds, the bridge without a socket, and the site over
HTTP. `lake exe videosTest <word>…` runs only the small model checks whose names contain one of
the words; `lake exe videosTest http`, only the bridge and the site over HTTP; `lake exe
videosTest large [<word>…]`, the model checks at large bounds, which take minutes
(`Videos.Check.Size`).
-/

def main (args : List String) : IO UInt32 := do
  let checks := Lanes.Testing.Result.tests (kind := .check)
  let quiet := Lanes.Testing.wantsJson args
  let http := do
    return Lanes.Testing.Result.tests (Videos.EndToEnd.bridgeTests
      ++ Videos.EndToEnd.sharedCacheTests ++ (← Videos.EndToEnd.run))
  let results ← match args.filter (· != "--json") with
    | [] => do
      pure (checks (← Videos.Check.run (quiet := quiet)) ++ checks Videos.Check.capTests ++ (← http))
    | ["http"] => http
    | "large" :: only => checks <$> Videos.Check.run .large only (jobs := 2) (quiet := quiet)
    | only => checks <$> Videos.Check.run .small only (quiet := quiet)
  Lanes.Testing.report args results
