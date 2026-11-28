/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! `lanes journal schema`: the schema of a type's codec, as the project's build derives it. A journal
holds no schema yet, so the command reads the build: it runs Lean, through `lake env`, on a
program that imports the modules named and prints the codec's `Schema.text`. -/

namespace Lanes.Cli.Journal

/-- The values of each `name value` pair in `args`. -/
def values (args : List String) (name : String) : List String :=
  match args with
  | flag :: value :: rest =>
    if flag == name then value :: values rest name else values (value :: rest) name
  | _ => []

/-- The program that prints the schema of `codec`, a term, importing `imports`. -/
def schemaProgram (codec : String) (imports : List String) : String :=
  String.join (imports.map (s!"import {·}\n"))
    ++ s!"#eval IO.print (({codec}) : Lanes.Codec _).schema.text\n"

def usage : String :=
  "lanes journal schema (--type <type> | --codec <term>) [--import <module>]...
    Print the schema of a type's codec, or of a codec, as the build derives it: the type, then
    each named type in it. The modules default to `Lanes`; build them first.
"

def run (args : List String) : IO UInt32 := do
  match args with
  | "schema" :: rest =>
    let codec? := ((values rest "--type").head?.map (s!"Lanes.Codec.of ({·})")).orElse
      fun _ => (values rest "--codec").head?
    let some codec := codec? | do IO.eprint usage; return 1
    let imports := match values rest "--import" with
      | [] => ["Lanes"]
      | named => named
    let child ← IO.Process.spawn
      { cmd := "lake", args := #["env", "lean", "--stdin"], stdin := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr (schemaProgram codec imports)
    stdin.flush
    -- The handle closes when its last reference goes, here, so Lean reads to the end.
    child.wait
  | _ =>
    IO.eprint usage
    return 1

end Lanes.Cli.Journal
