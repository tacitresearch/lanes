/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! Format 2 of the files (`Lanes/Durable/Format.lean`) on the compiled code: the prelude and its
manifest, a journal written with an older schema of its inputs read by name and written again
with the reader's, a torn tail, a bad checksum, and files of format 1 refused as such. The
theorems in `Lanes/Durable/Journal.lean` and `Lanes/Durable/Disk.lean` say the same of every
file. -/

namespace Tests.Format

open Lanes

namespace V1

lanes_data inductive Cmd where
  | put (key : String) (value : Nat)
  | drop (key : String)
  deriving DecidableEq, Repr, Codable

end V1

-- The next version: an argument added with a default, and a constructor inserted.
namespace V2

lanes_data inductive Cmd where
  | put (key : String) (value : Nat) (ttl_s : Nat := 0)
  | clear
  | drop (key : String)
  deriving DecidableEq, Repr, Codable

end V2

-- A version that cannot read the first: an argument added with no default.
namespace V3

lanes_data inductive Cmd where
  | put (key : String) (value : Nat) (owner : String)
  | drop (key : String)
  deriving DecidableEq, Repr, Codable

end V3

abbrev sig1 : Signature := { Id := Unit, Msg := fun _ => V1.Cmd, In := V1.Cmd, Out := Nat }
abbrev sig2 : Signature := { Id := Unit, Msg := fun _ => V2.Cmd, In := V2.Cmd, Out := Nat }
abbrev sig3 : Signature := { Id := Unit, Msg := fun _ => V3.Cmd, In := V3.Cmd, Out := Nat }

/-- One actor that counts the commands it is given. -/
def counter : System sig2 where
  State _ := Nat
  actor _ := { init := 0, step := fun n _ => (n + 1, []), recover := fun n => (n, []) }
  accept x := ⟨(), x⟩

def input1 : Codec V1.Cmd := Codec.of V1.Cmd
def input2 : Codec V2.Cmd := Codec.of V2.Cmd

def old : List (Journal.Entry sig1) :=
  [.advance 5, .input (.put "a" 1), .batch 64, .handed, .input (.drop "a"), .batch 64]

def migrated : List (Journal.Entry sig2) :=
  [.advance 5, .input (.put "a" 1 0), .batch 64, .handed, .input (.drop "a"), .batch 64]

def oldFile : ByteArray := Journal.file input1 "kv" old

def newFile : ByteArray := Journal.file input2 "kv" migrated

def opened2 (bytes : ByteArray) := Journal.open? (σ := sig2) input2 "kv" bytes

def written (entries : List (Journal.Entry sig2)) : List ByteArray := Journal.write input2 entries

/-- Whether a journal opened and gave `entries` in its first `size` bytes. -/
def gave (r : Except Journal.Refusal (List (Journal.Entry sig2) × Nat))
    (entries : List (Journal.Entry sig2)) (size : Nat) : Bool :=
  match r with
  | .ok (found, n) => written found == written entries && n == size
  | .error _ => false

def refusedAs {α : Type} (r : Except Journal.Refusal α) (refusal : Journal.Refusal) : Bool :=
  match r with
  | .error e => e == refusal
  | .ok _ => false

/-! Files of format 1, written as format 1 wrote them: each frame a length, an FNV-1a checksum
of four bytes, and the payload. -/

def fnv (payload : ByteArray) : UInt32 :=
  payload.foldl (fun hash byte => (hash ^^^ byte.toUInt32) * 16777619) 2166136261

def u32 (n : Nat) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

def oldFrame (payload : ByteArray) : ByteArray :=
  u32 payload.size ++ u32 (fnv payload).toNat ++ payload

def formerJournal (entries : Bool) : ByteArray :=
  oldFrame "lanes journal 1\nkv".toUTF8
    ++ if entries then oldFrame (oldFrame "1".toUTF8 ++ oldFrame "5".toUTF8) else .empty

def formerSnapshot : ByteArray :=
  oldFrame "lanes snapshot 1\nkv".toUTF8 ++ oldFrame "0".toUTF8

def flip (bytes : ByteArray) (i : Nat) : ByteArray :=
  bytes.set! i (bytes[i]! ^^^ 1)

/-- A prelude whose manifest is changed by `edit`, with entries after it. -/
def edited (edit : Journal.Manifest → Journal.Manifest) (schema : ByteArray) : ByteArray :=
  let own := Journal.Entry.own (σ := sig2) input2
  let manifest := edit (Journal.Prelude.manifest "kv" own)
  let manifestFrame := (Body.encode Journal.schemaLimits Journal.Manifest.codec.toOf manifest).toOption.getD .empty
  Frame.encode ([Journal.Kind.journal.header, manifestFrame, schema]
    ++ Journal.write input2 migrated)

def lastFrame : Nat := newFile.size - (20 + (Journal.Entry.bytes input2 (.batch 64 : Journal.Entry sig2)).size)

def tests : List (String × Bool) :=
  let own := Journal.Entry.own (σ := sig2) input2
  [ ("format: a journal begins with its header, its manifest and its schema, then a frame an entry",
      (Frame.decode newFile).take 3 == Journal.prelude (σ := sig2) input2 "kv"
        && (Frame.decode newFile).length == 3 + migrated.length
        && (Frame.decode newFile).head? == some "lanes journal 2\n".toUTF8),
    ("format: the manifest names the format, Lanes, the system, the toolchain, the runtime and "
      ++ "the schema frame's digest",
      match Journal.manifest? newFile with
      | some m => m.format == 2 && m.lanes == Journal.lanesVersion && m.system == "kv"
          && m.toolchain == Lean.versionString ++ " " ++ Lean.githash
          && m.runtime == "kernel" && m.policy == 1
          && some m.schema == ((Frame.decode newFile)[2]?).map Sha256.hash
      | none => false),
    ("format: a journal opens and gives what was written",
      gave (opened2 newFile) migrated newFile.size),
    ("format: a journal written with an older schema of its inputs is read by name: an argument "
      ++ "added takes its default and a constructor inserted moves none",
      gave (opened2 oldFile) migrated oldFile.size),
    ("format: a reader whose types cannot read the file's is refused at the prelude, naming why",
      match Journal.open? (σ := sig3) (Codec.of V3.Cmd) "kv" oldFile with
      | .error (.schema e) => e.problem == .noDefault && (toString e).contains "owner"
      | _ => false),
    ("format: an entry the reader's type does not have is refused when it is met",
      match Journal.open? (σ := sig1) input1 "kv"
          (Journal.file input2 "kv" ([.advance 1, .input .clear] : List (Journal.Entry sig2))) with
      | .error (.unreadable 1) => true
      | _ => false),
    ("format: a torn tail is cut, and the entries wholly written before it are kept",
      gave (opened2 (newFile.extract 0 (newFile.size - 3))) migrated.dropLast lastFrame),
    ("format: a cut inside the prelude is the journal of nothing",
      (List.range (Frame.span (Journal.prelude (σ := sig2) input2 "kv"))).all fun n =>
        gave (opened2 (newFile.extract 0 n)) [] 0),
    ("format: a bad checksum is damage, and refused where it is",
      (List.range 16).all fun k =>
        refusedAs (opened2 (flip newFile (lastFrame + 4 + k))) (.damaged lastFrame)),
    ("format: a bad checksum in the prelude is damage at its first byte",
      refusedAs (opened2 (flip newFile 10)) (.damaged 0)),
    ("format: a journal of format 1 is refused as format 1, with entries or without",
      refusedAs (opened2 (formerJournal true)) (.format 1)
        && refusedAs (opened2 (formerJournal false)) (.format 1)),
    ("format: a snapshot of format 1 is refused as format 1",
      refusedAs (Journal.savedOpen? (sys := counter)
        ⟨Codec.unit, fun _ => Codec.nat, fun _ => input2⟩ "kv" formerSnapshot) (.format 1)),
    ("format: a journal of another format is refused, naming it",
      refusedAs (opened2 (Frame.encode ["lanes journal 3\n".toUTF8])) (.format 3)
        && refusedAs (opened2 (edited ({ · with format := 3 }) (Journal.Prelude.schemaFrame own)))
          (.format 3)),
    ("format: a journal of another runtime policy is refused, naming it",
      refusedAs (opened2 (edited ({ · with policy := 2 }) (Journal.Prelude.schemaFrame own)))
        (.policy "kernel" 2)),
    ("format: a manifest that does not name the schema frame after it is refused",
      refusedAs (opened2 (edited id
        (Journal.Prelude.schemaFrame (Journal.Entry.own (σ := sig1) input1)))) .manifest),
    ("format: an entry is bounded as a body is, and a snapshot, one body, as a frame is",
      Journal.Kind.journal.limits == {}
        && Journal.Kind.snapshot.limits.maxBytes < 2 ^ 32
        && Journal.Kind.snapshot.limits.maxLength < 2 ^ 32),
    ("format: another system's journal is refused, naming it",
      refusedAs (Journal.open? (σ := sig2) input2 "other" newFile) (.foreign (some "kv"))
        && Journal.named? newFile == some "kv" && Journal.named? oldFile == some "kv") ]

open Journal (Disk) in
/-- A start on a journal written with an older schema writes it again with its own, once. -/
def rewriteTests : List (String × Bool) :=
  let disk : Disk := { journal := oldFile }
  match disk.read (sys := counter) input2 none "kv" with
  | .error _ => [("format: a journal of an older schema is read", false)]
  | .ok found =>
    let mended := (disk.mend input2 "kv" found).foldl Disk.apply disk
    let again := mended.read (sys := counter) input2 none "kv"
    [ ("format: a start finds that a journal of an older schema is not its own",
        written found.past == written migrated && !found.current),
      ("format: and writes it again with its own schema, which it then appends to",
        mended.journal == newFile
          && match again with
            | .ok found => found.current && written found.past == written migrated
                && (mended.mend input2 "kv" found).isEmpty
            | .error _ => false) ]

/-- The same through a store on disk. -/
def storeTest : IO (List (String × Bool)) := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  let path : System.FilePath := s!"{dir}/lanes-format-{← IO.monoNanosNow}.journal"
  let remove := fun (path : System.FilePath) => do
    for file in [path, path.addExtension "lock", path.addExtension "cut",
        path.addExtension "snapshot", path.addExtension "id"] do
      if ← file.pathExists then IO.FS.removeFile file
  IO.FS.writeBinFile path oldFile
  let store : Journal.Store counter := { path, input := input2, system := "kv" }
  let log ← store.open
  let past := log.past
  log.close
  let after ← IO.FS.readBinFile path
  IO.FS.writeBinFile path (formerJournal true)
  let refused ← store.open.toBaseIO
  let left ← IO.FS.readBinFile path
  remove path
  return [
    ("format: a store opens a journal of an older schema and writes it with its own",
      written past == written migrated && after == newFile),
    ("format: a store refuses a journal of format 1, saying so, and leaves it as it was",
      left == formerJournal true && match refused with
        | .error e => (toString e).contains "format 1"
        | .ok _ => false) ]

end Tests.Format
