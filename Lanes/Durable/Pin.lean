/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Diff
public import Lanes.Durable.Inspect

/-!
A pinned schema: the schema of what a journal or a snapshot of an application holds, committed as
text, so that a change to the application's types is seen in review and checked by `lanes lint`
before any file written under the old types meets the new binary
(`docs/decisions/D97-data-format.md`, 3.9).

A pinned file is a header, the schema as `lanes journal schema` prints it, for people, and the
schema frame in Base64 (`Journal.schemaText`), for the check. The header names the kind of file,
the term the build gives the schema from, the modules it needs, the declared migrations and the
corpus: the directories of files that the application wrote at earlier schemas, which the build
must still read.

`Pin.check` decides, with no IO: the build's schema against the pinned one by `Schema.compare`,
which is `Schema.Plan.of`, the matching a file is opened with; and every corpus file of the
pin's kind by `Journal.inspect` with the build's schema, as opening reads it. A compatible change
is reported, and `lanes lint --fix` writes the file again; a change that would be refused at
open, or a corpus file that does not read, fails, naming the field or the constructor.
-/

@[expose] public section

namespace Lanes.Journal.Pin

/-- What a pinned file names. `schema` is a term of `Lanes.Schema`, `migrations` terms of
`Lanes.Schema.Migration`, and `corpus` directories from the project's root. -/
structure Header where
  kind : Kind
  schema : String
  imports : List String := []
  migrations : List String := []
  corpus : List String := []
  deriving DecidableEq, Repr

/-- The comment at the start of every pinned file. -/
def preamble : List String :=
  [ "-- The pinned schema of an application's files. `lanes lint` checks that the build's schema",
    "-- reads what this one wrote, and the corpus; `lanes lint --fix` writes this file again after",
    "-- a change that old files read. The text is for people; the frame is what is checked." ]

def Header.lines (h : Header) : List String :=
  [s!"kind: {h.kind.name}", s!"schema: {h.schema}"] ++ h.imports.map (s!"import: {·}")
    ++ h.migrations.map (s!"migration: {·}") ++ h.corpus.map (s!"corpus: {·}")

def kindOf? (name : String) : Option Kind :=
  if name = Kind.journal.name then some .journal
  else if name = Kind.snapshot.name then some .snapshot
  else none

/-- One line of a header, `key: value`, added to what the lines before it gave. -/
def Header.add (h : Option Kind × Option String × Header) (line : String) :
    Except String (Option Kind × Option String × Header) :=
  let (kind, schema, rest) := h
  if line.startsWith "--" then .ok h
  else
    match line.splitOn ": " with
    | key :: value@(_ :: _) =>
      let value := (": ".intercalate value).trimAscii.toString
      match key with
      | "kind" =>
        match kindOf? value with
        | some k => .ok (some k, schema, rest)
        | none => .error s!"kind {value.quote}: a journal or a snapshot"
      | "schema" => .ok (kind, some value, rest)
      | "import" => .ok (kind, schema, { rest with imports := rest.imports ++ [value] })
      | "migration" => .ok (kind, schema, { rest with migrations := rest.migrations ++ [value] })
      | "corpus" => .ok (kind, schema, { rest with corpus := rest.corpus ++ [value] })
      | _ => .error s!"a line {line.quote}: the keys are kind, schema, import, migration, corpus"
    | _ => .error s!"a line {line.quote}, not `key: value`"

def Header.parse (lines : List String) : Except String Header := do
  let (kind, schema, h) ← lines.foldlM Header.add (none, none, { kind := .journal, schema := "" })
  let some kind := kind | throw "no `kind:` line"
  let some schema := schema | throw "no `schema:` line"
  return { h with kind, schema }

/-- How many characters of Base64 a line of the frame holds. -/
def width : Nat := 96

def chunks (text : String) : List String :=
  let cs := text.toList
  (List.range ((cs.length + width - 1) / width)).map fun k =>
    String.ofList ((cs.drop (k * width)).take width)

/-- The pinned file of `s`. -/
def render (h : Header) (s : Schema) : String :=
  "\n".intercalate (preamble ++ h.lines) ++ "\n\n" ++ s.text ++ "\nframe:\n"
    ++ "\n".intercalate (chunks (schemaText s)) ++ "\n"

/-- The header and the schema of a pinned file: the header is the lines before the first blank
one, the schema the frame after the last line `frame:`. A file of a header alone pins nothing
yet: `lanes lint --fix` writes the build's schema into it. -/
def parse (text : String) : Except String (Header × Option Schema) := do
  let lines := text.splitOn "\n"
  let h ← Header.parse (lines.takeWhile (· ≠ ""))
  let frame := (lines.reverse.takeWhile (· ≠ "frame:")).reverse
  if frame.length = lines.length then return (h, none)
  match schemaOfText? (String.join (frame.map (·.trimAscii.toString))) with
  | some s => return (h, some s)
  | none => throw "the frame does not read as a schema"

/-- A migration as `lanes lint` knows it: declared from `old` to `new`, its function not run.
Matching takes it where the writer's schema is `old` and the reader's `new`, as it takes the
application's own; a corpus file then reads if its values read with `old`. What the function
computes is the application's to check, as `Journal.Upgrade`'s `Migration` is. -/
def declared (old new : Schema) : Schema.Migration where
  old
  new
  run := some

/-- What is wrong with a pinned file, or with the build against it. -/
inductive Finding where
  | unreadable (reason : String)
  /-- Files written under the pinned schema would be refused at open: the error names where. -/
  | refused (error : Codec.Error)
  /-- A file of the corpus that the build's schema does not read, or that does not verify. -/
  | corpus (path : String) (finding : Inspect.Finding)
  /-- The build's schema differs in ways old files read: `lanes lint --fix` pins it. -/
  | changed (changes : List Schema.Change)
  /-- The schema is the same, and the file is not as `--fix` writes it. -/
  | stale
  /-- A header with no schema yet. -/
  | unpinned
  deriving Repr

def Finding.text : Finding → String
  | .unreadable reason => s!"the file does not read as a pinned schema: {reason}"
  | .refused error => s!"files written under the pinned schema would be refused at open: \
      {error}. Keep the old name as a former name (`was`), give the field a default, or declare \
      a migration (`from Old := f`, and a `migration:` line here)"
  | .corpus path finding => s!"`{path}` does not read with the build's schema: {finding.text}"
  | .changed [] => "the schema changed in the names of its types; `lanes lint --fix` pins it"
  | .changed changes => s!"the schema changed in ways old files read: \
      {"; ".intercalate (changes.map (·.text))}; `lanes lint --fix` pins it"
  | .stale => "the file is not as `lanes lint --fix` writes it"
  | .unpinned => "no schema is pinned yet: `lanes lint --fix` pins the build's"

/-- What the check finds, and what `lanes lint --fix` writes, if anything. -/
structure Result where
  findings : List Finding
  fixed : Option String := none

/-- What the corpus file at `path` finds, read with the build's schema `current`, if it is a
file of `kind`. -/
def corpusFindings (kind : Kind) (current : Schema) (ms : List Schema.Migration)
    (path : String) (bytes : ByteArray) : List Finding :=
  let found := inspect bytes (some current) ms
  if found.kind = some kind then found.findings.map (.corpus path) else []

/-- The pinned file `text` against the build's schema `current`, with the declared migrations
`ms` and the files of the corpus, each with its path. -/
def check (text : String) (current : Schema) (ms : List Schema.Migration)
    (corpus : List (String × ByteArray)) : Result :=
  match parse text with
  | .error reason => { findings := [.unreadable reason] }
  | .ok (h, pinned) =>
    let files := corpus.flatMap fun (path, bytes) => corpusFindings h.kind current ms path bytes
    let again := render h current
    let fixed := if files.isEmpty then some again else none
    match pinned with
    | none => { findings := files ++ [.unpinned], fixed }
    | some pinned =>
      match Schema.compare ms pinned current with
      | .refused e => { findings := .refused e :: files }
      | .same => { findings := files ++ (if again = text then [] else [.stale]), fixed }
      | .compatible changes => { findings := files ++ [.changed changes], fixed }

/-- A pinned file as `--fix` writes it reads back as its header and its schema. -/
theorem check_render_self {h : Header} {s : Schema} (hp : parse (render h s) = .ok (h, some s))
    {ms : List Schema.Migration} :
    check (render h s) s ms [] = { findings := [], fixed := some (render h s) } := by
  simp [check, hp, Schema.compare_self]

end Lanes.Journal.Pin
