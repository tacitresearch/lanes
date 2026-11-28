/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LanesCli.Generated
import Lanes.Durable.Pin

/-! `lanes lint`'s check `schema`: every pinned schema of the project (a `.schema` file,
`Lanes/Durable/Pin.lean`) against the schema the build derives, and the corpus it names. The
schemas are terms of the build, so Lean runs, through `lake env`, on a program that imports what
the pinned files name and prints each schema, and each declared migration's two, as
`Journal.schemaText` writes them; what is decided of them is `Lanes.Journal.Pin.check`, here, in
the compiled binary, which reads the corpus. A pinned file inside another Lake package under the
project's root (an example) is that package's, checked by `lanes lint` run there. -/

namespace Lanes.Cli.Schemas

open Lanes.Journal

/-- The pinned files of the project at `root`, from its root, in order: not under a hidden
directory, `templates`, or another Lake package. -/
def files (root : System.FilePath) : IO (List String) := do
  let found ← root.walkDir fun dir => do
    let name := dir.fileName.getD ""
    if name.startsWith "." || name == "templates" then return false
    if dir == root then return true
    return !((← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists))
  let paths := found.toList.filterMap fun f =>
    if f.extension == some "schema" then
      some (f.toString.dropPrefix (root.toString ++ "/")).toString
    else none
  return Generated.sortStrings paths

/-- The files under the corpus directories, from `root`, but the expected dumps and the notes. -/
def corpusFiles (root : System.FilePath) (dirs : List String) : IO (List (String × ByteArray)) := do
  let mut out := []
  for dir in dirs do
    if ← (root / dir).isDir then
      let found ← (root / dir).walkDir
      for f in Generated.sortStrings (found.toList.map (·.toString)) do
        let file : System.FilePath := f
        if !(← file.isDir) && file.extension != some "dump" && file.extension != some "md" then
          out := out ++ [((f.dropPrefix (root.toString ++ "/")).toString, ← IO.FS.readBinFile file)]
  return out

/-- The program that prints, for the `k`th pinned file, `lanes-pin k <schema>` and a line
`lanes-migration k <old> <new>` for each declared migration. -/
def program (pins : List Pin.Header) : String :=
  let imports := pins.foldl (fun acc h => h.imports.foldl (fun acc m =>
    if acc.contains m then acc else acc ++ [m]) acc) ["Lanes.Durable.Inspect"]
  let text := fun (term : String) => s!"Lanes.Journal.schemaText ({term})"
  let lines := pins.zipIdx.flatMap fun (h, k) =>
    s!"IO.println (\"lanes-pin {k} \" ++ {text s!"(({h.schema}) : Lanes.Schema)"})"
      :: h.migrations.map fun m =>
        s!"IO.println (\"lanes-migration {k} \" ++ {text s!"(({m}) : Lanes.Schema.Migration).old"} \
          ++ \" \" ++ {text s!"(({m}) : Lanes.Schema.Migration).new"})"
  String.join (imports.map (s!"import {·}\n"))
    ++ "#eval show IO Unit from do\n" ++ String.join (lines.map (s!"  {·}\n"))

/-- The schemas the program printed: for each pinned file, its schema and its migrations. -/
def readOutput (count : Nat) (stdout : String) :
    List (Option Schema × List (Option (Schema × Schema))) :=
  let lines := stdout.splitOn "\n"
  (List.range count).map fun k =>
    let words := fun (tag : String) => lines.filterMap fun line =>
      match line.splitOn " " with
      | t :: index :: rest => if t == tag && index == toString k then some rest else none
      | _ => none
    let schema := (words "lanes-pin").head?.bind fun | [s] => schemaOfText? s | _ => none
    let ms := (words "lanes-migration").map fun
      | [old, new] => do return (← schemaOfText? old, ← schemaOfText? new)
      | _ => none
    (schema, ms)

/-- The edits `--fix` makes to the pinned files and the problems it cannot fix, from the build.
Build first: the program imports the modules the files name. -/
def plan (root : System.FilePath) : IO Generated.Plan := do
  let paths ← files root
  let mut pins := []
  let mut problems : List Generated.Problem := []
  for path in paths do
    let text ← IO.FS.readFile (root / path)
    match Pin.parse text with
    | .ok (h, _) => pins := pins ++ [(path, text, h)]
    | .error reason => problems := problems ++ [(path, 1, "schema",
        (Pin.Finding.unreadable reason).text)]
  if pins.isEmpty then return { problems }
  let (handle, source) ← IO.FS.createTempFile
  handle.putStr (program (pins.map (·.2.2)))
  handle.flush
  let out ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", source.toString], cwd := some root }
  IO.FS.removeFile source
  let mut edits : List Generated.Edit := []
  for ((path, text, h), (current, ms)) in pins.zip (readOutput pins.length out.stdout) do
    match current, ms.mapM id with
    | some current, some ms =>
      let result := Pin.check text current (ms.map fun (old, new) => Pin.declared old new)
        (← corpusFiles root h.corpus)
      let messages := result.findings.map (·.text)
      match result.fixed with
      | some fixed =>
        unless messages.isEmpty do
          edits := edits ++ [{ path, change := .write fixed, rule := "schema"
                               message := "; ".intercalate messages }]
      | none => problems := problems ++ messages.map (path, 1, "schema", ·)
    | _, _ => problems := problems ++ [(path, 1, "schema",
        s!"Lean could not give the build's schema of `{h.schema}` (build first): \
          {(out.stderr ++ out.stdout).trimAscii}")]
  return { edits, problems }

end Lanes.Cli.Schemas
