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
  lanes lint [--fix] [--main] [<path>]
      Check a project against the LANES_STYLE rules, and the files derived from others.
      --fix rewrites the derived files: line counts, the decisions' index, docs/STATUS.md.
      --main numbers new decisions (with --fix) or reports them: use it on the main branch.
  lanes check
      Run the project's model checks (`lake test`).
  lanes inventory [--list <status>]
      In Lanes itself: write docs/INVENTORY.md, every public definition with its status and
      its evidence, or list the library's definitions of one status (`lake exe lanesInventory`).
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
  | "lint" :: rest =>
    let paths := rest.filter (!·.startsWith "--")
    let unknown := rest.filter fun a => a.startsWith "--" && a != "--fix" && a != "--main"
    if paths.length > 1 || !unknown.isEmpty then
      IO.print usage
      return 1
    let options := { fix := rest.contains "--fix", main := rest.contains "--main" }
    return if (← Lint.run (paths.headD ".") options) == 0 then 0 else 1
  | ["check"] =>
    let child ← IO.Process.spawn { cmd := "lake", args := #["test"] }
    return (← child.wait)
  | "inventory" :: rest =>
    let child ← IO.Process.spawn { cmd := "lake", args := #["exe", "lanesInventory"] ++ rest }
    return (← child.wait)
  | _ =>
    IO.print usage
    return if args.isEmpty || args == ["--help"] || args == ["help"] then 0 else 1
