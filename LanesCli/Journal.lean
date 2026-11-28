/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Durable.Inspect

/-! `lanes journal`: the schema of a type's codec, as the project's build derives it, and what a
journal or a snapshot file holds (`dump`) and whether it reads (`verify`). A file is
self-describing, so `dump` and `verify` need no application code: what they decide is
`Lanes.Journal.inspect`, and this file only reads the file and prints. The schema of a type
comes from the build: Lean runs, through `lake env`, on a program that imports the modules named
and prints it. -/

namespace Lanes.Cli.Journal

/-- The values of each `name value` pair in `args`. -/
def values (args : List String) (name : String) : List String :=
  match args with
  | flag :: value :: rest =>
    if flag == name then value :: values rest name else values (value :: rest) name
  | _ => []

/-- The flags that take a value. -/
def valued : List String := ["--type", "--codec", "--schema", "--import", "--from", "--count"]

/-- What `args` hold besides flags and their values. -/
def positional : List String → List String
  | flag :: value :: rest =>
    if valued.contains flag then positional rest
    else if flag.startsWith "--" then positional (value :: rest)
    else flag :: positional (value :: rest)
  | [flag] => if flag.startsWith "--" then [] else [flag]
  | [] => []

/-- The modules a program imports: those named, or `Lanes`. -/
def imports (args : List String) : List String :=
  match values args "--import" with
  | [] => ["Lanes"]
  | named => named

/-- The program that prints the schema of `codec`, a term, importing `imports`. -/
def schemaProgram (codec : String) (imports : List String) : String :=
  String.join (imports.map (s!"import {·}\n"))
    ++ s!"#eval IO.print (({codec}) : Lanes.Codec _).schema.text\n"

/-- The program that prints `schema`, a term of `Lanes.Schema`, as `Journal.schemaText` writes it,
on a line of its own. -/
def readerProgram (schema : String) (imports : List String) : String :=
  "import Lanes.Durable.Inspect\n" ++ String.join (imports.map (s!"import {·}\n"))
    ++ s!"#eval IO.println (\"lanes-schema \" ++ Lanes.Journal.schemaText ({schema}))\n"

/-- The term of the schema a reader of a file of `kind` reads its records with, from the flags:
the inputs' type or codec for a journal, whose records are entries, or the records' schema. -/
def readerTerm (kind : Option Lanes.Journal.Kind) (args : List String) :
    Except String (Option String) :=
  let codec := ((values args "--type").head?.map (s!"Lanes.Codec.of ({·})")).orElse
    fun _ => (values args "--codec").head?
  match (values args "--schema").head?, codec, kind with
  | some schema, _, _ => .ok (some s!"(({schema}) : Lanes.Schema)")
  | none, none, _ => .ok none
  | none, some codec, some .snapshot =>
    .error s!"a snapshot holds a kernel's image, not inputs: give the schema of what it holds, \
      --schema '(Lanes.Journal.savedOf codecs).schema', not {codec}"
  | none, some codec, _ =>
    .ok (some s!"Lanes.Journal.Entry.schemaOf (({codec}) : Lanes.Codec _).schema")

def usage : String :=
  "lanes journal schema (--type <type> | --codec <term>) [--import <module>]...
    Print the schema of a type's codec, or of a codec, as the build derives it: the type, then
    each named type in it. The modules default to `Lanes`; build them first.
lanes journal dump <file> [--from <n>] [--count <n>] [--json]
    Print a journal or a snapshot: its manifest, its schema, and each record from place <n>, at
    most <n> of them, read by name with the file's own schema, with the byte its frame starts
    at; then its tail. --json prints JSON lines: the file, a line a record, then the tail.
lanes journal verify <file> [--json] [(--type <type> | --codec <term> | --schema <term>)
    [--import <module>]...]
    Check every frame's length and checksum, the prelude (the format, the manifest's digest of
    the schema frame, the schema), that every record reads with the file's schema, and the
    tail: a torn tail, a write that did not finish, is not damage, and a journal opens with it
    cut off. Given the reader's types, the inputs of a journal (--type, --codec) or the schema
    of its records (--schema), check that they read the file's as opening would. Exits 0 if
    every check passes and 1 otherwise; --json prints the results as `lanes check --json` does.
"

/-- Run Lean on `program` in the current project, through `lake env`. -/
def runLean (program : String) : IO IO.Process.Output := do
  let (handle, path) ← IO.FS.createTempFile
  handle.putStr program
  handle.flush
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", path.toString] }
  IO.FS.removeFile path
  return out

/-- The reader's schema, from the build, if the flags name one. -/
def reader (kind : Option Lanes.Journal.Kind) (args : List String) :
    IO (Except String (Option Lanes.Schema)) := do
  match readerTerm kind args with
  | .error message => return .error message
  | .ok none => return .ok none
  | .ok (some term) =>
    let out ← runLean (readerProgram term (imports args))
    let line := (out.stdout.splitOn "\n").find? (·.startsWith "lanes-schema ")
    match line.bind fun line => Lanes.Journal.schemaOfText? (line.drop 13).toString with
    | some schema => return .ok (some schema)
    | none => return .error s!"Lean could not give the reader's schema, {term}:\n\
        {out.stderr}{out.stdout}"

def number? (args : List String) (name : String) : Option (Option Nat) :=
  match (values args name).head? with
  | none => some none
  | some text => text.toNat?.map some

def dump (path : String) (args : List String) : IO UInt32 := do
  let (some start, some count) := (number? args "--from", number? args "--count") | do
    IO.eprint usage; return 1
  let found := Lanes.Journal.inspect (← IO.FS.readBinFile path)
  if args.contains "--json" then
    for line in found.dumpJson (start.getD 0) count do IO.println line.compress
  else IO.println (found.dumpText (start.getD 0) count)
  return 0

def verify (path : String) (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  match ← reader (Lanes.Journal.inspect bytes).kind args with
  | .error message => do IO.eprintln s!"lanes journal verify: {message}"; return 1
  | .ok schema =>
    let found := Lanes.Journal.inspect bytes schema
    IO.println (if args.contains "--json" then found.verifyJson.compress else found.verifyText)
    return if found.findings.isEmpty then 0 else 1

def run (args : List String) : IO UInt32 := do
  match args with
  | "schema" :: rest =>
    let codec? := ((values rest "--type").head?.map (s!"Lanes.Codec.of ({·})")).orElse
      fun _ => (values rest "--codec").head?
    let some codec := codec? | do IO.eprint usage; return 1
    let child ← IO.Process.spawn
      { cmd := "lake", args := #["env", "lean", "--stdin"], stdin := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr (schemaProgram codec (imports rest))
    stdin.flush
    -- The handle closes when its last reference goes, here, so Lean reads to the end.
    child.wait
  | "dump" :: rest =>
    let [path] := positional rest | do IO.eprint usage; return 1
    dump path rest
  | "verify" :: rest =>
    let [path] := positional rest | do IO.eprint usage; return 1
    verify path rest
  | _ =>
    IO.eprint usage
    return 1

end Lanes.Cli.Journal
