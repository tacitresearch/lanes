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

def requires (source : Source) : String :=
  (fill "counter" source (include_str "../templates/app/lakefile.toml.tmpl")).splitOn
    "[[lean_lib]]" |>.head!

def tests : IO (List (String × Bool)) := do
  let source := Source.path "../.."
  let written ← files.mapM fun (path, contents) => do
    let target := System.FilePath.mk "examples/counter" / fill "counter" source path
    let found ← try some <$> IO.FS.readFile target catch _ => pure none
    return (s!"lanes new: {target} is what the template writes",
      found == some (fill "counter" source contents))
  let released := requires (pinned (some "v0.2.0") "0123abc" true)
  let unreleased := requires (pinned none "0123abc" false)
  let untagged := requires (pinned none "0123abc" true)
  return written ++ [
    ("lanes new: an app made at a release requires its tag",
      released.endsWith "name = \"lanes\"\n# Lanes v0.2.0, the release this app was made from.\n\
        # To move to another version, change `rev` and run `lake update lanes`.\n\
        git = \"https://github.com/tacitresearch/lanes\"\nrev = \"v0.2.0\"\n\n"),
    ("lanes new: an app made before any release requires the commit, and says so",
      unreleased.endsWith "# Lanes has no release yet, so this is the commit of Lanes it was made from.\n\
        # To move to another version, change `rev` and run `lake update lanes`.\n\
        git = \"https://github.com/tacitresearch/lanes\"\nrev = \"0123abc\"\n\n"),
    ("lanes new: an app made between releases requires the commit",
      (untagged.splitOn "rev = \"0123abc\"").length == 2
        && (untagged.splitOn "No release tag of Lanes is at the commit").length == 2),
    ("lanes new: a commit on no remote, and changes not committed, are each warned of",
      (warnings "0123abc" true false).isEmpty
        && ((warnings "0123abc" false false).map (·.splitOn "0123abc" |>.length)) == [2]
        && (warnings "0123abc" true true).length == 1
        && (warnings "0123abc" false true).length == 2) ]

end Tests.New
