/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Check
import Videos.EndToEnd

/-!
`lake test`: the model checks, the bridge without a socket, and the site over HTTP.
`lake exe videosTest <word>…` runs only the model checks whose names contain one of the words.
-/

def main (args : List String) : IO UInt32 := do
  let tests : List (String × Bool) ← if args.isEmpty then do
      pure ((← Videos.Check.run) ++ Videos.Check.capTests ++ Videos.EndToEnd.bridgeTests
        ++ Videos.EndToEnd.sharedCacheTests ++ (← Videos.EndToEnd.run))
    else Videos.Check.run args
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  IO.println s!"{tests.length - failed.length} passed, {failed.length} failed"
  return if failed.isEmpty then 0 else 1
