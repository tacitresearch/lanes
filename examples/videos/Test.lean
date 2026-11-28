/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Videos.Check
import Videos.EndToEnd

/-!
`lake test`: the model checks at small bounds, the bridge without a socket, and the site over
HTTP. `lake exe videosTest <word>…` runs only the small model checks whose names contain one of
the words; `lake exe videosTest http`, only the bridge and the site over HTTP; `lake exe
videosTest large [<word>…]`, the model checks at large bounds, which take minutes
(`Videos.Check.Size`).
-/

def main (args : List String) : IO UInt32 := do
  let tests : List (String × Bool) ← match args with
    | [] => do
      pure ((← Videos.Check.run) ++ Videos.Check.capTests ++ Videos.EndToEnd.bridgeTests
        ++ Videos.EndToEnd.sharedCacheTests ++ (← Videos.EndToEnd.run))
    | ["http"] => do
      pure (Videos.EndToEnd.bridgeTests ++ Videos.EndToEnd.sharedCacheTests ++ (← Videos.EndToEnd.run))
    | "large" :: only => Videos.Check.run .large only (jobs := 2)
    | only => Videos.Check.run .small only
  let failed := tests.filter (!·.2)
  for (name, ok) in tests do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  IO.println s!"{tests.length - failed.length} passed, {failed.length} failed"
  return if failed.isEmpty then 0 else 1
