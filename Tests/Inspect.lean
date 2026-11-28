/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Format
import LanesCli.Journal

/-! `lanes journal dump` and `verify` (`Lanes/Durable/Inspect.lean`, `LanesCli/Journal.lean`) on
the files of `Tests/Format.lean`: a good journal and snapshot, a torn tail, a flipped byte, files
of format 1, and a journal of an older schema with and without a reader's schema that reads it.
`Journal.inspect_file`, `Journal.inspect_saved` and `Journal.inspect_cut` say the same of every
file the writer writes. -/

namespace Tests.Inspect

open Lanes Tests.Format

def codecs : Kernel.Image.Codecs counter := ⟨Codec.unit, fun _ => Codec.nat, fun _ => input2⟩

def snapshotFile : ByteArray :=
  Journal.saved codecs "kv" 6 (Journal.recover counter migrated).1.image

/-- The schema a reader of version `k` of the commands reads the journal's entries with. -/
def own2 : Schema := Journal.Entry.own (σ := sig2) input2
def own3 : Schema := Journal.Entry.own (σ := sig3) (Codec.of V3.Cmd)

def findings (bytes : ByteArray) (reader : Option Schema := none) : List Journal.Inspect.Finding :=
  (Journal.inspect bytes reader).findings

def failed (bytes : ByteArray) (reader : Option Schema := none) : List String :=
  ((Journal.inspect bytes reader).results.filter (!·.2.1)).map (·.1)

def tests : List (String × Bool) :=
  let found := Journal.inspect newFile
  [ ("inspect: a journal the writer wrote passes, and its records are its entries, each at the "
      ++ "byte its frame starts at",
      Journal.verify newFile && found.kind == some .journal
        && found.records.length == migrated.length
        && found.records.map (·.byte) == (List.range migrated.length).map (fun k =>
          Frame.span ((Frame.decode newFile).take (3 + k)))
        && found.tail == .clean),
    ("inspect: a record is shown by the names in the file's schema",
      (found.dumpText.splitOn "\n").any (·.endsWith ".input (.put \"a\" 1 0)")
        && (found.dumpJson.map (·.compress)).any
          (·.contains "\"value\":{\"input\":{\"x\":{\"put\":{\"key\":\"a\",\"value\":1,\"ttl_s\":0}}}}")),
    ("inspect: the manifest and the schema are shown",
      found.dumpText.contains "system \"kv\"" && found.dumpText.contains "inductive Tests.Format.V2.Cmd"
        && found.dumpText.contains "ttl_s : Nat := 0"),
    ("inspect: --from and --count bound the records shown",
      (found.dumpJson 2 (some 3)).length == 5
        && ((found.dumpText 2 (some 3)).splitOn "\n").countP (·.startsWith "  2 at byte") == 1),
    ("inspect: a snapshot the writer wrote passes, its one record read by name",
      Journal.verify snapshotFile && Journal.verify snapshotFile (some (Journal.savedOf codecs).schema)
        && (Journal.inspect snapshotFile).kind == some .snapshot
        && (Journal.inspect snapshotFile).records.length == 1),
    ("inspect: a torn tail is torn, not damage, and a journal with one passes",
      let torn := newFile.extract 0 (newFile.size - 3)
      Journal.verify torn && (Journal.inspect torn).tail == .torn lastFrame
        && (Journal.inspect torn).records.length == migrated.length - 1),
    ("inspect: a torn snapshot fails, as torn: a snapshot is written whole",
      findings (snapshotFile.extract 0 (snapshotFile.size - 3)) == [.torn
        (Frame.span ((Frame.decode snapshotFile).take 3))]),
    ("inspect: a flipped byte in the checksum or the payload of a frame is damage where it is",
      [4, 10, 19, 20].all fun k =>
        findings (flip newFile (lastFrame + k)) == [.refused (.damaged lastFrame)]
          && failed (flip newFile (lastFrame + k)) == ["frames"]),
    ("inspect: a flipped byte in the length of a frame before the last is damage where it is",
      let first := Frame.span (Journal.prelude (σ := sig2) input2 "kv")
      findings (flip newFile (first + 3)) == [.refused (.damaged first)]),
    ("inspect: files of format 1 fail as format 1",
      [formerJournal true, formerJournal false, formerSnapshot].all fun bytes =>
        findings bytes == [.refused (.format 1)] && failed bytes == ["prelude"]),
    ("inspect: a file of another format, or of no format, fails naming it",
      findings (Frame.encode ["lanes snapshot 3\n".toUTF8]) == [.refused (.format 3)]
        && findings (Frame.encode ["hello".toUTF8]) == [.refused (.foreign none)]),
    ("inspect: a manifest that does not name the schema frame fails at the prelude",
      findings (edited id (Journal.Prelude.schemaFrame (Journal.Entry.own (σ := sig1) input1)))
        == [.refused .manifest]),
    ("inspect: a journal of an older schema passes, alone and with a reader whose schema reads it",
      Journal.verify oldFile && Journal.verify oldFile (some own2)
        && (Journal.inspect oldFile (some own2)).compared),
    ("inspect: a reader whose schema cannot read the file's fails as opening would, naming the field",
      match findings oldFile (some own3) with
      | [.reader e] => e.problem == .noDefault && (toString e).contains "owner"
          && failed oldFile (some own3) == ["reader"]
      | _ => false),
    ("inspect: a record holding a constructor the reader lacks fails where it is",
      let bytes := Journal.file input2 "kv" ([.advance 1, .input .clear] : List (Journal.Entry sig2))
      match findings bytes (some (Journal.Entry.own (σ := sig1) input1)) with
      | [.unreadable 1 byte _] => some byte == (Journal.inspect bytes).records[1]?.map (·.byte)
      | _ => false),
    ("inspect: the reader's schema of a journal is the schema of its entries",
      Journal.Entry.schemaOf input2.schema == own2),
    ("inspect: a schema printed as text reads back",
      Journal.schemaOfText? (Journal.schemaText own2) == some own2
        && Journal.schemaOfText? "not base64" == none),
    ("inspect: verify --json gives each check as a result of kind check",
      let json := (Journal.inspect oldFile (some own3)).verifyJson.compress
      json.contains "\"failed\":1" && json.contains "\"name\":\"reader\""
        && json.contains "\"kind\":\"check\"") ]

/-- `lanes journal verify` and `dump` on files written to a temporary directory: the exit code,
and the reader's schema got from Lean through `lake env`. -/
def cliTests : IO (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let stamp ← IO.monoNanosNow
  let path := fun (name : String) => s!"{dir}/lanes-inspect-{stamp}-{name}"
  let files := [("old", oldFile), ("torn", newFile.extract 0 (newFile.size - 3)),
    ("flipped", flip newFile (lastFrame + 10)), ("former", formerJournal true),
    ("snapshot", snapshotFile)]
  for (name, bytes) in files do IO.FS.writeBinFile (path name) bytes
  let run := fun (args : List String) => do
    let (out, code) ← IO.FS.withIsolatedStreams (Cli.Journal.run args)
    return (code, out)
  let verify := fun (name : String) (more : List String) => run (["verify", path name] ++ more)
  let (old, _) ← verify "old" []
  let (torn, tornOut) ← verify "torn" []
  let (flipped, _) ← verify "flipped" []
  let (former, formerOut) ← verify "former" ["--json"]
  let (snapshot, _) ← verify "snapshot" []
  let (dump, dumpOut) ← run ["dump", path "old", "--json", "--count", "2"]
  let reads := ["--import", "Tests.Format", "--type", "Tests.Format.V2.Cmd"]
  let (reader, _) ← verify "old" reads
  let (refused, refusedOut) ← verify "old"
    ["--import", "Tests.Format", "--codec", "Lanes.Codec.of Tests.Format.V3.Cmd"]
  let (snapshotType, _) ← verify "snapshot" reads
  for (name, _) in files do IO.FS.removeFile (path name)
  return [
    ("journal verify: exits 0 on a good file, a torn journal and a snapshot, 1 on damage and format 1",
      old == 0 && torn == 0 && tornOut.contains "torn at byte" && flipped == 1 && former == 1
        && formerOut.contains "format 1" && snapshot == 0),
    ("journal dump: --json prints a line for the file, each record shown and the tail",
      dump == 0 && (dumpOut.trimAscii.toString.splitOn "\n").length == 4),
    ("journal verify --type: the reader's schema comes from the build, and one that reads the file "
      ++ "passes",
      reader == 0),
    ("journal verify --codec: a reader's schema that cannot read the file fails, naming the field",
      refused == 1 && refusedOut.contains "owner"),
    ("journal verify --type on a snapshot is refused: a snapshot holds no inputs",
      snapshotType == 1) ]

end Tests.Inspect
