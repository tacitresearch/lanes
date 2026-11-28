/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Data.Declare
public import Lanes.Data.MatchSound
public import Lanes.Durable.Frame

/-!
Format 2 of the files (`docs/decisions/D97-data-format.md`). A journal and a snapshot begin with
three frames, the prelude: a header that names the kind of file and the format, the manifest,
and the schema of what follows. Every value after them is one body (`Lanes.Body`), written with
that schema and read through the plan from it to the reader's (`Schema.Plan.of`), so a file
written under an older schema is read by name.

`Prelude.check` is what a reader makes of a prelude: refused, with the reason, or the writer's
schema and the plan. A file of format 1 is refused as format 1 (`Refusal.format`), never read
as something else. `Prelude.check_prelude`: a prelude written for a system and a schema is
accepted by a reader of the same, with no plan.
-/

@[expose] public section

namespace Lanes.Journal

/-- The version of Lanes that writes the files. -/
def lanesVersion : String := "0.1.0"

/-- The runtime whose journal a file is, and the version of its policy: what an entry `batch`
means (the kernel's scheduling) and what the entries are. A journal of another policy is
refused: its tail would replay to another kernel. -/
def runtime : String := "kernel"
def policy : Nat := 1

/-- Who wrote a file, for whom, and with what (D97, 3.3). The journal's id is kept beside the
journal, in its `.id` file (D105). -/
lanes_data structure Manifest where
  /-- The format of the file, 2. -/
  format : Nat
  /-- The version of Lanes that wrote it, and its commit when known. -/
  lanes : String
  commit : String := ""
  /-- The application's name and version (`Journal.label`). -/
  system : String
  /-- Lean's version and commit. -/
  toolchain : String
  runtime : String
  policy : Nat
  /-- The SHA-256 of the schema frame. -/
  schema : ByteArray
  deriving DecidableEq, Codable

/-- The kinds of file, each with a header of its own. -/
inductive Kind where
  | journal
  | snapshot
  deriving DecidableEq, Repr

namespace Kind

def name : Kind → String
  | .journal => "journal"
  | .snapshot => "snapshot"

/-- The first frame of a file of this kind in format 2. -/
def header (kind : Kind) : ByteArray := ("lanes " ++ kind.name ++ " 2\n").toUTF8

/-- The start of a file of format 1: its first frame had a length and four bytes of checksum,
then this. -/
def former (kind : Kind) : ByteArray := ("lanes " ++ kind.name ++ " 1\n").toUTF8

/-- How a reader bounds what it reads of each value of a file of this kind. A snapshot is one
value, the whole kernel, so its bounds are those of a frame. -/
def limits : Kind → Codec.Limits
  | .journal => {}
  | .snapshot => { maxBytes := 2 ^ 32 - 1, maxItems := 2 ^ 28, maxLength := 2 ^ 32 - 1
                   maxDepth := 256 }

end Kind

/-- The bounds of the schema frame and of the manifest. A schema nests a few values for each of
its types', so it may be deep. -/
def schemaLimits : Codec.Limits := { maxDepth := 4096 }

/-- Why a journal's files are not opened. A refused file is left as it is. -/
inductive Refusal where
  /-- The file is not a journal of `system`: it is the journal of the system `named`, or no
  journal at all. -/
  | foreign (named : Option String)
  /-- An entry is intact on disk and cannot be read: it holds what the reader's types do not. -/
  | unreadable (entry : Nat)
  /-- A frame is all there and does not check. -/
  | damaged (byte : Nat)
  /-- The snapshot file does not read back whole as a snapshot of `system`. -/
  | snapshot
  /-- The journal does not continue the snapshot (`resume`). -/
  | apart
  /-- The system's name or the schema of its inputs is too large for a prelude, so no journal can
  carry them. -/
  | name
  /-- There is no journal, and the store may not begin one (`Disk.start`). -/
  | missing
  /-- The file is of another format: format 1 is the one before this, which this Lanes does not
  read. -/
  | format (version : Nat)
  /-- The manifest does not read, or does not name the schema frame that follows it. -/
  | manifest
  /-- The journal was written by another runtime, or under another version of its policy. -/
  | policy (runtime : String) (version : Nat)
  /-- The schema frame does not read, or the reader's types cannot read the values it describes:
  the error names the type and the field. -/
  | schema (error : Codec.Error)
  deriving DecidableEq, Repr

/-- The bytes a successful write gave; nothing otherwise, which `Prelude.fits` rules out. -/
def okBytes : Except Codec.Error ByteArray → ByteArray
  | .ok bytes => bytes
  | .error _ => .empty

theorem okBytes_ok {r : Except Codec.Error ByteArray} {bytes : ByteArray} (h : r = .ok bytes) :
    okBytes r = bytes := by
  subst h; rfl

namespace Prelude

/-- The schema frame: the schema as a value written with its own tags. -/
def schemaFrame (s : Schema) : ByteArray :=
  okBytes (Body.writeAny schemaLimits s.toValue)

def manifest (system : String) (s : Schema) : Manifest where
  format := 2
  lanes := lanesVersion
  system
  toolchain := Lean.versionString ++ " " ++ Lean.githash
  runtime
  policy
  schema := Sha256.hash (schemaFrame s)

def manifestFrame (system : String) (s : Schema) : ByteArray :=
  okBytes (Body.encode schemaLimits Manifest.codec.toOf (manifest system s))

/-- The three frames that begin a file of `kind` for `system`, whose values have the schema `s`. -/
def frames (kind : Kind) (system : String) (s : Schema) : List ByteArray :=
  [kind.header, manifestFrame system s, schemaFrame s]

/-- Whether the prelude can be written: the schema and the manifest within their bounds, and each
frame within a frame's. -/
def fits (kind : Kind) (system : String) (s : Schema) : Bool :=
  (Body.writeAny schemaLimits s.toValue).toBool
    && (Body.encode schemaLimits Manifest.codec.toOf (manifest system s)).toBool
    && (frames kind system s).all Frame.fits

/-- What a first frame that is not this kind's header says: a file of another format of this
kind, or no file of this kind. -/
def other (kind : Kind) (first : ByteArray) : Refusal :=
  match (String.fromUTF8? first).bind fun text =>
      (text.dropPrefix? ("lanes " ++ kind.name ++ " ")).bind fun rest =>
        (rest.dropSuffix? "\n").bind (·.toString.toNat?) with
  | some version => .format version
  | none => .foreign none

/-- What a reader of `system`, whose values have the schema `reader`, makes of a prelude: the
writer's schema and the plan from it to the reader's, or why the file is refused. -/
def check (kind : Kind) (system : String) (reader : Schema) (first manifest schema : ByteArray) :
    Except Refusal (Schema × Schema.Plan) :=
  if first ≠ kind.header then .error (other kind first) else
  match Body.decode schemaLimits Manifest.codec.toOf manifest with
  | .error _ => .error .manifest
  | .ok m =>
    if m.format ≠ 2 then .error (.format m.format)
    else if m.system ≠ system then .error (.foreign (some m.system))
    else if m.runtime ≠ runtime ∨ m.policy ≠ policy then .error (.policy m.runtime m.policy)
    else if m.schema ≠ Sha256.hash schema then .error .manifest
    else
      match Body.readAny schemaLimits schema with
      | .error e => .error (.schema e)
      | .ok v =>
        match Schema.ofValue? v with
        | none => .error (.schema { offset := 0, problem := .misfit })
        | some writer =>
          match Schema.Plan.of [] writer reader with
          | .ok plan => .ok (writer, plan)
          | .error e => .error (.schema e)

/-- The system a prelude names, whatever the schema. -/
def named? (kind : Kind) (first manifest : ByteArray) : Option String :=
  if first = kind.header then
    (Body.decode schemaLimits Manifest.codec.toOf manifest).toOption.map (·.system)
  else none

theorem fits_frames {kind : Kind} {system : String} {s : Schema} (h : fits kind system s = true) :
    ∀ p ∈ frames kind system s, p.size < 2 ^ 32 := by
  simp only [fits, Bool.and_eq_true] at h
  exact Frame.all_fits_iff.mp h.2

private theorem ok_of_toBool {r : Except Codec.Error ByteArray} (h : r.toBool = true) :
    ∃ bytes, r = .ok bytes := by
  cases r with
  | ok bytes => exact ⟨bytes, rfl⟩
  | error => simp [Except.toBool] at h

theorem decode_manifestFrame {kind : Kind} {system : String} {s : Schema}
    (h : fits kind system s = true) :
    Body.decode schemaLimits Manifest.codec.toOf (manifestFrame system s)
      = .ok (manifest system s) := by
  simp only [fits, Bool.and_eq_true] at h
  obtain ⟨bytes, hb⟩ := ok_of_toBool h.1.2
  rw [manifestFrame, okBytes_ok hb]
  exact Body.decode_encode hb

theorem readAny_schemaFrame {kind : Kind} {system : String} {s : Schema}
    (h : fits kind system s = true) :
    Body.readAny schemaLimits (schemaFrame s) = .ok s.toValue := by
  simp only [fits, Bool.and_eq_true] at h
  obtain ⟨bytes, hb⟩ := ok_of_toBool h.1.1
  rw [schemaFrame, okBytes_ok hb]
  exact Body.readAny_writeAny hb

/-- A reader of the system and the schema a prelude was written for accepts it, and needs no
plan. -/
theorem check_frames {kind : Kind} {system : String} {s : Schema}
    (h : fits kind system s = true) :
    check kind system s kind.header (manifestFrame system s) (schemaFrame s) = .ok (s, .same) := by
  simp [check, decode_manifestFrame h, readAny_schemaFrame h, Schema.ofValue?_toValue,
    Schema.Plan.of_self, manifest]

theorem named?_frames {kind : Kind} {system : String} {s : Schema}
    (h : fits kind system s = true) :
    named? kind kind.header (manifestFrame system s) = some system := by
  simp [named?, decode_manifestFrame h, manifest, Except.toOption]

/-- A reader of another system refuses the prelude as that system's. -/
theorem check_other {kind : Kind} {named system : String} {s r : Schema}
    (h : fits kind named s = true) (hne : named ≠ system) :
    check kind system r kind.header (manifestFrame named s) (schemaFrame s)
      = .error (.foreign (some named)) := by
  simp [check, decode_manifestFrame h, manifest, hne]

end Prelude

namespace Kind

/-- Whether `bytes` begin as a file of this kind in format 1 did. -/
def formerly (kind : Kind) (bytes : ByteArray) : Bool :=
  bytes.extract 8 (8 + kind.former.size) == kind.former

theorem size_former (kind : Kind) : kind.former.size = 16 + if kind = .journal then 0 else 1 := by
  cases kind <;> decide

theorem header_one (kind : Kind) : kind.header[1]? = some 97 := by
  cases kind <;> decide

theorem former_thirteen (kind : Kind) : ∃ b, kind.former[13]? = some b ∧ b ≠ 97 := by
  cases kind
  · exact ⟨32, by decide, by decide⟩
  · exact ⟨116, by decide, by decide⟩

theorem size_header (kind : Kind) : 1 < kind.header.size := by
  cases kind <;> decide

/-- No file of format 2, cut anywhere, begins as a file of format 1 did: its twenty-second byte
is the second of its header, and that is not the format 1 file's. -/
theorem formerly_cut (kind : Kind) (rest : ByteArray) (n : Nat) :
    kind.formerly ((Frame.one kind.header ++ rest).extract 0 n) = false := by
  rw [formerly, beq_eq_false_iff_ne]
  intro h
  have h13 := congrArg (·[13]?) h
  obtain ⟨b, hb, hne⟩ := former_thirteen kind
  have hL : 8 + 13 < 8 + kind.former.size := by rw [size_former]; split <;> omega
  simp only [hb, getElem?_extract, hL, ↓reduceIte, Nat.zero_add] at h13
  by_cases hn : 8 + 13 < n
  · simp only [hn, ↓reduceIte] at h13
    rw [show 8 + 13 = 20 + 1 from rfl, Frame.getElem?_one_append _ (size_header kind),
      header_one] at h13
    exact hne (Option.some.inj h13).symm
  · simp [hn] at h13

end Kind

end Lanes.Journal
