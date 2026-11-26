/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Lint
import LanesCli.New

/-! The `lanes` command. -/

open Lanes.Cli

def usage : String :=
  "lanes: build verified software in Lean

Usage:
  lanes new <name> [--dir <path>] [--lanes-path <path>] [--rev <rev>]
      Create a new application.
  lanes lint [<path>]
      Check a project against the LANES_STYLE rules.
  lanes check
      Run the project's model checks (`lake test`).
"

def flag? (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => some value
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | "new" :: name :: rest =>
    let dir := (flag? rest "--dir").getD name
    let source : New.Source := match flag? rest "--lanes-path" with
      | some path => .path path
      | none => .git "https://github.com/tacitresearch/lanes" ((flag? rest "--rev").getD "main")
    New.run name dir source
  | ["lint"] => return if (← Lint.run ".") == 0 then 0 else 1
  | ["lint", path] => return if (← Lint.run path) == 0 then 0 else 1
  | ["check"] =>
    let child ← IO.Process.spawn { cmd := "lake", args := #["test"] }
    return (← child.wait)
  | _ =>
    IO.print usage
    return if args.isEmpty || args == ["--help"] || args == ["help"] then 0 else 1
