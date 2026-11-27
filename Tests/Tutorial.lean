/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Tutorial.Counter

/-!
`docs/TUTORIAL.md` stays true: every `lean` block in it is text of a file of `Tests/Tutorial/`,
which `lake build` compiles, with
`Tut.` for `Tests.Tutorial.` in imports.
`Tests.Tutorial.Main` defines `main`, so it is built, not imported.
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
  ["Counter.lean", "Main.lean"]

def tests : IO (List (String × Bool)) := do
  let doc ← IO.FS.readFile "docs/TUTORIAL.md"
  let code ← sources.mapM fun (f : String) => do
    return (← IO.FS.readFile s!"Tests/Tutorial/{f}").replace "import Tests.Tutorial." "import Tut."
  let lean := (blocks doc).filter (·.1 == "lean")
  return [("tutorial: it has lean blocks", !lean.isEmpty)] ++ lean.zipIdx.map fun ((_, body), k) =>
    (s!"tutorial: lean block {k + 1} is in Tests/Tutorial/", code.any (occursIn body))

end Tests.Tutorial
