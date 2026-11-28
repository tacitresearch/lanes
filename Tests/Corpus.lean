/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Fixtures.Bank

/-! The corpus of old files (`docs/decisions/D97-data-format.md`, 3.8): journals and snapshots
written by the applications at known schemas, in `Tests/Journals/<application>/<release>/`,
each with the dump `lanes journal dump` gave of it when it was added (`<file>.dump`). The files
are only added, never rewritten, so a change in what this Lanes reads of an old file, its
format, its manifest or its values, shows as a dump that differs. The schemas they were written
with are pinned (`Tests/Schemas/`), and `lanes lint` checks that the build still reads them.

The bank's files are written here; the served applications' by their own packages
(`examples/ledger`, `examples/videos`). `lanesTest corpus` writes the bank's files of this
release and the dump of every corpus file that has none, and rewrites nothing. -/

namespace Tests.Corpus

open Lanes Tests.Fixtures.Bank

/-- The corpus, from the project's root. -/
def root : System.FilePath := "Tests/Journals"

namespace Bank

abbrev Bank3 := bank (Fin 3) 100

def input : Codec (Request (Fin 3)) := Request.codec Codec.fin

def codecs : Kernel.Image.Codecs Bank3 := actors Codec.fin 100

def system : String := "bank"

/-- The schema the bank's journal holds, pinned in `Tests/Schemas/bank-journal.schema`. -/
def journal : Schema := Journal.Entry.own (σ := sig (Fin 3)) input

/-- The schema the bank's snapshot holds, pinned in `Tests/Schemas/bank-snapshot.schema`. -/
def snapshot : Schema := (Journal.savedOf codecs).schema

/-- Every kind of entry, and a transfer refused. The last transfer is not yet run, so the
snapshot holds a message in flight. -/
def entries : List (Journal.Entry (sig (Fin 3))) :=
  [ .advance 1000, .input (.transfer ⟨1, 0, 1, 30⟩), .input (.balance 2 1), .batch 64, .handed,
    .advance 1500, .input (.transfer ⟨3, 2, 0, 500⟩), .batch 64, .snapshot 8,
    .input (.transfer ⟨4, 1, 2, 5⟩) ]

def journalFile : ByteArray := Journal.file input system entries

def snapshotFile : ByteArray :=
  Journal.saved codecs system entries.length (Journal.recover Bank3 entries).1.image

/-- The files of this release, by their names in its directory. -/
def files : List (String × ByteArray) := [("journal", journalFile), ("snapshot", snapshotFile)]

end Bank

/-- The files of the corpus, from the project's root, in order: every file but the expected
dumps and the notes. -/
def corpusFiles : IO (List System.FilePath) := do
  if !(← root.isDir) then return []
  let found ← root.walkDir
  let mut out := []
  for f in found.qsort (·.toString < ·.toString) do
    if !(← f.isDir) && f.extension != some "dump" && f.extension != some "md" then
      out := out ++ [f]
  return out

def dumpOf (file : System.FilePath) : System.FilePath := file.toString ++ ".dump"

/-- What `lanes journal dump` prints of a file. -/
def dump (bytes : ByteArray) : String := (Journal.inspect bytes).dumpText ++ "\n"

/-- The bank's files of every release, each opened by the bank of this build. -/
def bankOpens : IO (List (String × Bool)) := do
  let mut out := []
  for f in ← corpusFiles do
    if (f.toString.splitOn "/").contains "bank" then
      let bytes ← IO.FS.readBinFile f
      let opens := match f.fileName with
        | some "journal" => (Journal.open? (σ := sig (Fin 3)) Bank.input Bank.system bytes).toBool
        | some "snapshot" => (Journal.savedOpen? Bank.codecs Bank.system bytes).toBool
        | _ => false
      out := out ++ [(s!"corpus: {f} opens with the bank of this build", opens)]
  return out

/-- Each corpus file passes `verify` and dumps as it did when it was added. -/
def tests : IO (List (String × Bool)) := do
  let files ← corpusFiles
  let mut out := [("corpus: the bank's files of this release are in the corpus",
    ← (root / "bank" / Journal.lanesVersion / "journal").pathExists)]
  for f in files do
    let bytes ← IO.FS.readBinFile f
    let expected ← if ← (dumpOf f).pathExists then some <$> IO.FS.readFile (dumpOf f) else pure none
    out := out ++ [(s!"corpus: {f} passes verify and dumps as {dumpOf f} says",
      Journal.verify bytes && expected == some (dump bytes))]
  return out ++ (← bankOpens)

/-- `lanesTest corpus`: write the bank's files of this release and the dump of every corpus file
that has none. An existing file is left as it is. -/
def record : IO Unit := do
  let dir := root / "bank" / Journal.lanesVersion
  IO.FS.createDirAll dir
  for (name, bytes) in Bank.files do
    unless ← (dir / name).pathExists do
      IO.FS.writeBinFile (dir / name) bytes
      IO.println s!"wrote {dir / name}"
  for f in ← corpusFiles do
    unless ← (dumpOf f).pathExists do
      IO.FS.writeFile (dumpOf f) (dump (← IO.FS.readBinFile f))
      IO.println s!"wrote {dumpOf f}"

end Tests.Corpus
