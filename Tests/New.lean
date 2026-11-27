/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.New

/-!
`examples/counter` is exactly what `lanes new counter --lanes-path ../..` writes, so the template
and the example cannot drift apart: each file the template makes is compared with the example's.
-/

namespace Tests.New

open Lanes.Cli.New

def tests : IO (List (String × Bool)) := do
  let source := Source.path "../.."
  files.mapM fun (path, contents) => do
    let target := System.FilePath.mk "examples/counter" / fill "counter" source path
    let found ← try some <$> IO.FS.readFile target catch _ => pure none
    return (s!"lanes new: {target} is what the template writes",
      found == some (fill "counter" source contents))

end Tests.New
