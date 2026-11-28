/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Three fixtures are their examples' systems, copied because an example is a Lake package of its
own that the tests cannot import. Each copy, from its `namespace` line on, is its example's file
with `Tests.Fixtures.` before the namespace, so the two cannot drift apart; their headers may
differ.
-/

namespace Tests.Copies

/-- The fixtures and the files they copy. -/
def copies : List (String × String) :=
  [ ("Tests/Fixtures/KV.lean", "examples/kv-cache/KV.lean"),
    ("Tests/Fixtures/Election.lean", "examples/election/Election.lean"),
    ("Tests/Fixtures/Watchdog.lean", "examples/watchdog/Watchdog.lean") ]

/-- A file from its first `namespace` line on, with `Tests.Fixtures.` taken out. -/
def body (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").dropWhile (!·.startsWith "namespace "))
    |>.replace "Tests.Fixtures." ""

def tests : IO (List (String × Bool)) :=
  copies.mapM fun (fixture, original) => do
    let read (path : String) := try some <$> IO.FS.readFile path catch _ => pure none
    let copy ← read fixture
    let source ← read original
    return (s!"fixtures: {fixture} is the system of {original}",
      copy.any (fun text => !(body text).isEmpty) && (copy.map body) == (source.map body))

end Tests.Copies
