/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Tutorial
import Tests.TutorialWeb.Check
import Tests.TutorialWeb.EndToEnd

/-!
`docs/TUTORIAL-WEB.md` stays true, as `docs/TUTORIAL.md` does (`Tests/Tutorial.lean`). Every
`lean` block in it is text of a file of `Tests/TutorialWeb/`, which `lake build` compiles
(imports read `Shelf.` for `Tests.TutorialWeb.`), and every `text` block is what the checker
prints for the shelf of step 5 or for its bug. `live` is the site of step 4 over HTTP against
the test kit's fakes. `Tests.TutorialWeb.Main` defines `main`, so it is built, not imported.
-/

namespace Tests.TutorialWeb

open Tests.Tutorial (blocks occursIn)

def sources : List String :=
  ["Files.lean", "Web.lean", "Main.lean", "Check.lean", "EndToEnd.lean", "Proofs.lean"]

def tests : IO (List (String × Bool)) := do
  let doc ← IO.FS.readFile "docs/TUTORIAL-WEB.md"
  let code ← sources.mapM fun (f : String) => do
    return (← IO.FS.readFile s!"Tests/TutorialWeb/{f}").replace "import Tests.TutorialWeb." "import Shelf."
  let lean := (blocks doc).filter (·.1 == "lean")
  let text := (blocks doc).filterMap fun (info, body) => if info == "text" then some body else none
  let fixed := report Shelf.service
  let bug := report buggy
  let outputs := [fixed.renderSystem, bug.renderSystem]
  return [("tutorial web: it has lean blocks", !lean.isEmpty),
      ("tutorial web: the shelf of step 5 passes its check", fixed.ok),
      ("tutorial web: the bug of step 5 fails it", !bug.ok)]
    ++ lean.zipIdx.map (fun ((_, body), k) =>
      (s!"tutorial web: lean block {k + 1} is in Tests/TutorialWeb/", code.any (occursIn body)))
    ++ text.zipIdx.map (fun (body, k) =>
      (s!"tutorial web: text block {k + 1} is what the checker prints", outputs.contains body))
    ++ outputs.zipIdx.map fun (out, k) =>
      (s!"tutorial web: check {k + 1} of step 5 is quoted", text.contains out)

def live : Std.Async.Async (List (String × Bool)) := Shelf.EndToEnd.live

end Tests.TutorialWeb
