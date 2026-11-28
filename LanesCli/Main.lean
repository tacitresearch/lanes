/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Journal
import LanesCli.Lint
import LanesCli.New

/-! The `lanes` command. -/

open Lanes.Cli

def usage : String :=
  "lanes: build verified software in Lean

Usage:
  lanes new <name> [--dir <path>] [--lanes-path <path>] [--rev <rev>]
      Create a new application.
  lanes lint [--fix] [--main] [--json] [<path>]
      Check a project against the rules of Lanes (AGENTS.md), and the files derived from others.
      --fix rewrites the derived files: the line counts of TRUSTED.md and the decisions' index.
      --main numbers new decisions (with --fix) or reports them: use it on the main branch.
      --json prints the findings as JSON, each with its kind: proof for a `sorry`, else check.
  lanes check [--json]
      Run the project's checks and tests (`lake test`). It exits 0 when everything passed and
      every model check explored its whole instance, 1 when something failed, and 2 when a
      model check passed but hit a bound. --json prints the results as JSON, each with its
      kind (build, proof, check or test): the test driver's (`lake test -- --json`), or the
      build's failure when the driver did not build.
  lanes changelog [--release <version> <date>]
      Print the Unreleased section of the changelog, gathered from docs/changes/; or write it
      into CHANGELOG.md as the release <version> of <date> and remove the fragments.
  lanes stats
      Print the totals no committed file holds: trusted lines, decisions, unreleased changes,
      and in Lanes itself the inventory's statuses by area (`lake exe lanesInventory --summary`).
  lanes inventory [--list <status>]
      In Lanes itself: print every public definition with its status and its evidence, or list
      the library's definitions of one status (`lake exe lanesInventory`).
  lanes journal schema (--type <type> | --codec <term>) [--import <module>]...
      Print the schema of a type's codec, or of a codec, as the build derives it: the type,
      then each named type in it. The modules default to `Lanes`; build them first.
  lanes journal dump <file> [--from <n>] [--count <n>] [--json]
      Print a journal or a snapshot as text, or JSON lines: its manifest, its schema, and each
      record read by name with the file's own schema, with the byte its frame starts at.
  lanes journal verify <file> [--json] [(--type <type> | --codec <term> | --schema <term>)
      [--import <module>]...]
      Check every frame, the prelude and every record, and tell a torn tail from damage; given
      the reader's types, check that they read the file as opening would. Exits 0 or 1.
  lanes docstrings [--list]
      In Lanes itself: how many public declarations of `import Lanes` have a docstring, by
      module, or list those that have none. It reports and fails nothing.
"

def flag? (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => some value
  | _ => none

/-- The totals no committed file holds, since each would change with every item. -/
def stats (root : System.FilePath) : IO UInt32 := do
  let (files, lines) ← Generated.trustedTotal root
  IO.println s!"- Trusted code (TRUSTED.md): {Generated.withCommas lines} lines in {files} files"
  let (decisions, _) ← Generated.readDecisions root
  IO.println s!"- Decisions: {decisions.length}"
  IO.println s!"- Changelog fragments in docs/changes/: {(← Changelog.files root).length}"
  if !(← (root / "LanesCli" / "Inventory.lean").pathExists) then return 0
  IO.println "\nThe inventory (`lanes inventory`), definitions by status:\n"
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "lanesInventory", "--summary"], cwd := some root }
  child.wait

/-- `lake test -- --json`, whose driver prints the results as JSON, on its last line that starts
with `{`; what else it printed is left out. If it printed none, the
driver did not build, or does not take `--json`: that is one failure, of kind build, with
what Lake printed. -/
def checkJson : IO UInt32 := do
  let out ← IO.Process.output { cmd := "lake", args := #["test", "--", "--json"] }
  let printed := (out.stdout.splitOn "\n").reverse.find? (·.startsWith "{")
  if let some json := printed then
    IO.println json
    return out.exitCode
  let messages := "\n".intercalate (((out.stderr ++ out.stdout).trimAscii.toString.splitOn "\n").filter
    (!·.startsWith "trace:"))
  IO.println ("{\"passed\":0,\"bounded\":0,\"failed\":1,\"results\":[{\"name\":\"lake test\","
    ++ "\"kind\":\"build\",\"status\":\"failed\",\"detail\":" ++ Lint.jsonString messages ++ "}]}")
  return if out.exitCode == 0 then 1 else out.exitCode

def main (args : List String) : IO UInt32 := do
  match args with
  | "new" :: name :: rest =>
    let dir := (flag? rest "--dir").getD name
    let source : New.Source ← match flag? rest "--lanes-path", flag? rest "--rev" with
      | some path, _ => pure (.path path)
      | none, some rev => pure (.git New.repository rev)
      | none, none => do
        let some (source, warnings) ← New.ofCheckout | do
          IO.eprintln "lanes new: git cannot say which commit this checkout of Lanes is at, so \
            the app requires `main`; give `--rev` to pin it"
          pure (.git New.repository "main")
        for warning in warnings do IO.eprintln s!"lanes new: warning: {warning}"
        pure source
    New.run name dir source
  | "lint" :: rest =>
    let paths := rest.filter (!·.startsWith "--")
    let unknown := rest.filter fun a =>
      a.startsWith "--" && a != "--fix" && a != "--main" && a != "--json"
    if paths.length > 1 || !unknown.isEmpty then
      IO.print usage
      return 1
    let options :=
      { fix := rest.contains "--fix", main := rest.contains "--main", json := rest.contains "--json" }
    return if (← Lint.run (paths.headD ".") options) == 0 then 0 else 1
  | "changelog" :: rest => Changelog.run "." rest
  | ["stats"] => stats "."
  | ["check"] =>
    let child ← IO.Process.spawn { cmd := "lake", args := #["test"] }
    return (← child.wait)
  | ["check", "--json"] => checkJson
  | "journal" :: rest => Journal.run rest
  | "docstrings" :: rest =>
    let child ← IO.Process.spawn
      { cmd := "lake", args := #["exe", "lanesInventory", "--docstrings"] ++ rest }
    return (← child.wait)
  | "inventory" :: rest =>
    let child ← IO.Process.spawn { cmd := "lake", args := #["exe", "lanesInventory"] ++ rest }
    return (← child.wait)
  | _ =>
    IO.print usage
    return if args.isEmpty || args == ["--help"] || args == ["help"] then 0 else 1
