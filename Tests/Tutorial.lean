/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Tutorial.Check

/-!
`docs/TUTORIAL.md` stays true. Every `lean` block in it is text of a file of `Tests/Tutorial/`,
which `lake build` compiles (imports read `Tut.` for `Tests.Tutorial.`), and every `text` block
is what the checker prints for the counter of step 3 or for its bug. `Tests.Tutorial.Main`
defines `main`, so it is built, not imported.
-/

namespace Tests.Tutorial

/-- The fenced blocks of a Markdown text: the word after the fence, and the lines inside. -/
def blocks (text : String) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  let mut open? : Option (String × List String) := none
  for line in text.splitOn "\n" do
    match open?, line.startsWith "```" with
    | none, true => open? := some ((line.drop 3).toString, [])
    | some (info, body), true =>
      out := out ++ [(info, "\n".intercalate body.reverse)]
      open? := none
    | some (info, body), false => open? := some (info, line :: body)
    | none, false => pure ()
  return out

def occursIn (needle haystack : String) : Bool :=
  (haystack.splitOn needle).length > 1

def sources : List String :=
  ["Counter.lean", "Main.lean", "Check.lean"]

def tests : IO (List (String × Bool)) := do
  let doc ← IO.FS.readFile "docs/TUTORIAL.md"
  let code ← sources.mapM fun (f : String) => do
    return (← IO.FS.readFile s!"Tests/Tutorial/{f}").replace "import Tests.Tutorial." "import Tut."
  let lean := (blocks doc).filter (·.1 == "lean")
  let text := (blocks doc).filterMap fun (info, body) => if info == "text" then some body else none
  let fixed := report Tut.service
  let bug := report buggy
  let outputs := [fixed.renderSystem, bug.renderSystem]
  return [("tutorial: it has lean blocks", !lean.isEmpty),
      ("tutorial: the counter of step 3 passes its check", fixed.ok),
      ("tutorial: the bug of step 3 fails it", !bug.ok)]
    ++ lean.zipIdx.map (fun ((_, body), k) =>
      (s!"tutorial: lean block {k + 1} is in Tests/Tutorial/", code.any (occursIn body)))
    ++ text.zipIdx.map (fun (body, k) =>
      (s!"tutorial: text block {k + 1} is what the checker prints", outputs.contains body))
    ++ outputs.zipIdx.map fun (out, k) =>
      (s!"tutorial: check {k + 1} of step 3 is quoted", text.contains out)

end Tests.Tutorial
