/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Snapshot
public import Lanes.Lib.Encoding.Json
public import Lanes.Lib.Encoding.Base64
public import Lanes.Lib.Crypto.Hmac

/-!
What `lanes journal dump` and `lanes journal verify` make of a file of format 2, with no
application code: a file holds the schema of its records, so each record reads as a `Value` by
the names in it (`docs/decisions/D97-data-format.md`, 3.7).

`inspect` reads a journal or a snapshot as opening would, and says what it finds instead of
stopping at the first refusal: every frame's length and checksum, the prelude (`Prelude.read`:
the format, the manifest and its digest of the schema frame, the schema), every record read
with the file's schema, and the tail. A tail that a write did not finish is torn, not damage: a
journal opens with it cut off. Given a reader's schema, it is matched with the file's by
`Schema.Plan.of`, as opening matches them, and each record is read through the plan.

`inspect_file` and `inspect_saved`: what the writer writes has no finding, and its records are
the values written. `inspect_cut`: a journal cut at any byte has none either.
-/

@[expose] public section

namespace Lanes

/-! Values as JSON, with their schema: a record is an object of its fields, a constructor with
no fields its name, one with fields an object of its name and its fields, as Lean's `ToJson`
writes them, and bytes are hex. -/

mutual

/-- A value with no schema: a constructor is its index and its fields. -/
def Value.json : Value → Json
  | .nat n => .num n
  | .int i => .num i
  | .string s => .str s
  | .bytes b => .str (Bytes.hex b)
  | .list vs => .arr (Value.jsons vs).toArray
  | .ctor k vs => .obj #[("ctor", .num k), ("fields", .arr (Value.jsons vs).toArray)]

def Value.jsons : List Value → List Json
  | [] => []
  | v :: vs => Value.json v :: Value.jsons vs

end

namespace Schema

mutual

/-- A value read with its schema, as JSON; `null` where it does not fit. -/
def json : Schema → Value → Json
  | .nat, .nat n => .num n
  | .int, .int i => .num i
  | .string, .string s => .str s
  | .bytes, .bytes b => .str (Bytes.hex b)
  | .unit, .ctor 0 [] => .null
  | .list item, .list vs => .arr (vs.map item.json).toArray
  | .map key value, .list vs => .arr (vs.map fun
      | .ctor 0 [k, v] => .arr #[key.json k, value.json v]
      | _ => .null).toArray
  | .record _ _ fields, .ctor 0 vs => .obj (jsonFields fields vs).toArray
  | .sum _ _ ctors, .ctor k vs => jsonCtor ctors k vs
  | .dependent index, .ctor 0 [i, v] => .arr #[index.json i, v.json]
  | _, _ => .null

def jsonFields : List (Field Schema) → List Value → List (String × Json)
  | ⟨name, _, s, _⟩ :: fs, v :: vs => (name, s.json v) :: jsonFields fs vs
  | _, _ => []

def jsonCtor : List (Ctor Schema) → Nat → List Value → Json
  | ⟨name, _, []⟩ :: _, 0, _ => .str name
  | ⟨name, _, fields⟩ :: _, 0, vs => .obj #[(name, .obj (jsonFields fields vs).toArray)]
  | _ :: cs, k + 1, vs => jsonCtor cs k vs
  | [], _, _ => .null

end

end Schema

namespace Journal

/-- The kind of file whose first frame is `first`. -/
def Kind.of? (first : ByteArray) : Option Kind :=
  if first = Kind.journal.header then some .journal
  else if first = Kind.snapshot.header then some .snapshot
  else none

/-- A schema as text that a program can print and another read back (`schemaOfText?_schemaText`):
its frame in Base64. `lanes journal verify --type` gets the reader's schema so from Lean. -/
def schemaText (s : Schema) : String :=
  Base64.encode .std (Prelude.schemaFrame s)

def schemaOfText? (text : String) : Option Schema :=
  (Base64.decode .std text).bind fun bytes =>
    (Body.readAny schemaLimits bytes).toOption.bind Schema.ofValue?

namespace Inspect

/-- How a file ends after its last whole, intact frame. -/
inductive Tail where
  | clean
  /-- A frame from this byte was not written to its end: a write the process did not finish. A
  journal opens with it cut off. -/
  | torn (byte : Nat)
  /-- The frame at this byte is all there and does not check. -/
  | damaged (byte : Nat)
  deriving DecidableEq, Repr

/-- How `bytes` end after their whole frames, which take `size` bytes, as `open?` tells. -/
def Tail.of (bytes : ByteArray) (size : Nat) : Tail :=
  if bytes.size ≤ size then .clean
  else if Frame.unfinished bytes size then .torn size
  else .damaged size

/-- A record after the prelude: its place, the byte its frame starts at, the size of its payload,
and its value read with the file's schema. -/
structure Record where
  index : Nat
  byte : Nat
  size : Nat
  value : Except Codec.Error Value

/-- The records of `payloads`, the first at place `index` in a frame at `byte`. -/
def records (limits : Codec.Limits) (writer : Schema) : Nat → Nat → List ByteArray → List Record
  | _, _, [] => []
  | index, byte, p :: ps =>
    { index, byte, size := p.size, value := Body.read limits writer p }
      :: records limits writer (index + 1) (byte + 20 + p.size) ps

/-- What is wrong with a file. -/
inductive Finding where
  /-- What opening would refuse the file for, at its start or at a damaged frame. -/
  | refused (refusal : Refusal)
  /-- A record does not read with the file's own schema. -/
  | record (index byte : Nat) (error : Codec.Error)
  /-- The reader's schema cannot read the file's: the error names the type and the field. -/
  | reader (error : Codec.Error)
  /-- A record reads with the file's schema, and not through the plan to the reader's: it holds a
  constructor the reader's type does not have. -/
  | unreadable (index byte : Nat) (error : Codec.Error)
  /-- A snapshot that a write did not finish. A snapshot is renamed into place whole, so it never
  opens so; a journal does. -/
  | torn (byte : Nat)
  /-- A snapshot that holds this many records, not one. -/
  | count (records : Nat)
  deriving DecidableEq, Repr

/-- What a record finds, through `plan` when there is a reader. -/
def Record.finding (plan : Option Schema.Plan) (r : Record) : Option Finding :=
  match r.value with
  | .error e => some (.record r.index r.byte e)
  | .ok v =>
    match plan with
    | none => none
    | some p =>
      match p.apply v with
      | .error e => some (.unreadable r.index r.byte e)
      | .ok _ => none

end Inspect

open Inspect in
/-- What a file holds and what is wrong with it. -/
structure Inspection where
  kind : Option Kind := none
  /-- The bytes where the header, the manifest and the schema frame start. -/
  prelude : List Nat := []
  manifest : Option Manifest := none
  /-- The writer's schema, if the prelude reads. -/
  schema : Option Schema := none
  records : List Record := []
  tail : Tail := .clean
  /-- Whether a reader's schema was matched with the file's. -/
  compared : Bool := false
  findings : List Finding := []

namespace Inspect

/-- What a tail finds: damage always, and a torn write in a snapshot. -/
def tailFindings (kind : Option Kind) : Tail → List Finding
  | .clean => []
  | .torn byte => if kind = some .snapshot then [.torn byte] else []
  | .damaged byte => [.refused (.damaged byte)]

/-- What a file whose first frame is no header of format 2 is: a file of format 1, of another
format, or no file of Lanes. -/
def stranger (bytes first : ByteArray) : Refusal :=
  if Kind.journal.formerly bytes || Kind.snapshot.formerly bytes then .format 1
  else
    match Prelude.other .journal first with
    | .foreign _ => Prelude.other .snapshot first
    | refusal => refusal

/-- The plan to the reader's schema, if there is a reader, and what matching finds, with the
declared migrations `ms`. -/
def planFor (ms : List Schema.Migration) (writer : Schema) :
    Option Schema → Option Schema.Plan × List Finding
  | none => (none, [])
  | some reader =>
    match Schema.Plan.of ms writer reader with
    | .ok plan => (some plan, [])
    | .error e => (none, [.reader e])

/-- A file of `kind` whose prelude is whole: its records after it, and their findings. -/
def ofPrelude (kind : Kind) (reader : Option Schema) (ms : List Schema.Migration) (tail : Tail)
    (first manifest schema : ByteArray) (payloads : List ByteArray) : Inspection :=
  let prelude := [0, 20 + first.size, 40 + first.size + manifest.size]
  match Prelude.read kind none first manifest schema with
  | .error refusal =>
    { kind, prelude, tail
      manifest := (Body.decode schemaLimits Manifest.codec.toOf manifest).toOption
      findings := .refused refusal :: tailFindings kind tail }
  | .ok (m, writer) =>
    let rs := records kind.limits writer 0 (60 + first.size + manifest.size + schema.size)
      payloads
    let (plan, matched) := planFor ms writer reader
    let count := if kind = .snapshot ∧ payloads.length ≠ 1 ∧ tail = .clean then
      [.count payloads.length] else []
    { kind, prelude, manifest := m, schema := writer, records := rs, tail
      compared := reader.isSome
      findings := matched ++ count ++ rs.filterMap (·.finding plan) ++ tailFindings kind tail }

end Inspect

open Inspect in
/-- What a journal or a snapshot holds and what is wrong with it, with the reader's schema of
its records when one is given: for a journal, the schema of its entries (`Entry.schemaOf`).
Opening reads with no migration; `lanes lint` gives the ones a pinned schema declares. -/
def inspect (bytes : ByteArray) (reader : Option Schema := none)
    (migrations : List Schema.Migration := []) : Inspection :=
  let frames := Frame.decode bytes
  let tail := Tail.of bytes (Frame.span frames)
  match frames with
  | [] =>
    if Kind.journal.formerly bytes || Kind.snapshot.formerly bytes then
      { tail, findings := [.refused (.format 1)] }
    else { tail, findings := tailFindings none tail }
  | first :: rest =>
    match Kind.of? first with
    | none => { tail, findings := [.refused (stranger bytes first)] }
    | some kind =>
      match rest with
      | manifest :: schema :: payloads =>
        ofPrelude kind reader migrations tail first manifest schema payloads
      | _ =>
        { kind, prelude := [0], tail
          findings := (if kind = .snapshot then [.refused .snapshot] else [])
            ++ tailFindings kind tail }

/-- Whether `lanes journal verify` passes the file. -/
def verify (bytes : ByteArray) (reader : Option Schema := none) : Bool :=
  (inspect bytes reader).findings.isEmpty

/-! What the writer writes passes. -/

namespace Inspect

variable {σ : Signature}

theorem finding_ok {plan : Option Schema.Plan} (hp : plan = none ∨ plan = some .same)
    {r : Record} {v : Value} (h : r.value = .ok v) : r.finding plan = none := by
  rcases hp with rfl | rfl <;> simp [Record.finding, h, Schema.Plan.apply_same]

theorem filterMap_finding {plan : Option Schema.Plan} (hp : plan = none ∨ plan = some .same)
    {rs : List Record} {vs : List Value} (h : rs.map (·.value) = vs.map .ok) :
    rs.filterMap (·.finding plan) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro r hr
  have : r.value ∈ vs.map Except.ok := h ▸ List.mem_map_of_mem hr
  obtain ⟨v, -, hv⟩ := List.mem_map.mp this
  exact finding_ok hp hv.symm

theorem read_bytes (input : Codec σ.In) {entry : Entry σ} (h : Entry.fits input entry = true) :
    Body.read Kind.journal.limits (Entry.own input) (Entry.bytes input entry)
      = .ok ((Entry.schema input).toValue entry) :=
  Body.read_write (Entry.write_of_fits h).1

theorem records_write (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (index byte : Nat) :
    (records Kind.journal.limits (Entry.own input) index byte (write input entries)).map (·.value)
      = (entries.map (Entry.schema input).toValue).map .ok := by
  induction entries generalizing index byte with
  | nil => rfl
  | cons entry entries ih =>
    simp only [write, List.map_cons, records] at ih ⊢
    rw [read_bytes input (h entry List.mem_cons_self), ih fun e he => h e (List.mem_cons_of_mem _ he)]

/-- A journal's tail that opening would cut off finds nothing. -/
theorem tailFindings_unfinished {bytes : ByteArray} {size : Nat}
    (h : Frame.unfinished bytes size = true) : tailFindings (some .journal) (Tail.of bytes size) = [] := by
  unfold Tail.of
  split
  · rfl
  · simp [tailFindings]

theorem tailFindings_none {bytes : ByteArray} {size : Nat}
    (h : Frame.unfinished bytes size = true) : tailFindings none (Tail.of bytes size) = [] := by
  unfold Tail.of
  split
  · rfl
  · simp [tailFindings]

theorem planFor_same {ms : List Schema.Migration} {s : Schema} {reader : Option Schema}
    (hr : reader = none ∨ reader = some s) :
    ∃ plan, (plan = none ∨ plan = some .same) ∧ planFor ms s reader = (plan, []) := by
  rcases hr with rfl | rfl
  · exact ⟨none, .inl rfl, rfl⟩
  · exact ⟨some .same, .inr rfl, by simp [planFor, Schema.Plan.of_self]⟩

end Inspect

open Inspect

/-- A journal file whose frames are its prelude and its first `k` entries, and whose bytes after
them a write did not finish, passes `verify`, alone or with the reader's own schema, and its
records are those entries. -/
theorem inspect_whole (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) {bytes : ByteArray} {k : Nat}
    (hdecode : Frame.decode bytes = prelude input system ++ (write input entries).take k)
    (htail : Frame.unfinished bytes (Frame.span (prelude input system
      ++ (write input entries).take k)) = true)
    {reader : Option Schema} (hr : reader = none ∨ reader = some (Entry.own input)) :
    (inspect bytes reader).findings = []
      ∧ (inspect bytes reader).records.map (·.value)
        = ((entries.take k).map (Entry.schema input).toValue).map .ok := by
  obtain ⟨plan, hplan, hfor⟩ := planFor_same (ms := []) hr
  have htake : (write input entries).take k = write input (entries.take k) := by
    simp [write, List.map_take]
  have hfits : ∀ e ∈ entries.take k, Entry.fits input e = true :=
    fun e he => h e (List.mem_of_mem_take he)
  have hrec := records_write input hfits
  rw [htake] at hdecode htail
  simp only [prelude, Prelude.frames, List.cons_append, List.nil_append] at hdecode htail
  simp only [inspect, hdecode, Kind.of?, ↓reduceIte, ofPrelude,
    Prelude.read_frames hsystem (reader := none) (by simp), hfor, hrec, List.nil_append]
  simp only [reduceCtorEq, false_and, ↓reduceIte, List.nil_append,
    filterMap_finding hplan (hrec _ _), tailFindings_unfinished htail, and_self]

/-- What the writer writes passes `verify`, alone or with the reader's own schema, and `dump`
shows the entries written. -/
theorem inspect_file (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true)
    {reader : Option Schema} (hr : reader = none ∨ reader = some (Entry.own input)) :
    verify (file input system entries) reader = true
      ∧ (inspect (file input system entries) reader).records.map (·.value)
        = (entries.map (Entry.schema input).toValue).map .ok := by
  have hfit := frames_fit input hsystem h
  have hlen : (write input entries).length = entries.length := by simp [write]
  have hdecode : Frame.decode (file input system entries)
      = prelude input system ++ (write input entries).take entries.length := by
    rw [file, Frame.decode_encode hfit, List.take_of_length_le (by omega)]; rfl
  have htail : Frame.unfinished (file input system entries)
      (Frame.span (prelude input system ++ (write input entries).take entries.length)) = true := by
    rw [List.take_of_length_le (by omega)]
    exact Frame.unfinished_of_size_le (by rw [file, Frame.size_encode]; exact Nat.le_refl _)
  obtain ⟨hfind, hrec⟩ := inspect_whole input hsystem h hdecode htail hr
  rw [List.take_of_length_le (Nat.le_refl _)] at hrec
  exact ⟨by simp [verify, hfind], hrec⟩

/-- A journal file cut off at any byte, as the death of the process leaves it, passes `verify`:
a torn tail is never taken for damage. -/
theorem inspect_cut (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (n : Nat)
    {reader : Option Schema} (hr : reader = none ∨ reader = some (Entry.own input)) :
    verify ((file input system entries).extract 0 n) reader = true := by
  have hfit := frames_fit input hsystem h
  have hdecode := Frame.decode_take_eq hfit n
  have htail := Frame.unfinished_take hfit n
  have hone : file input system entries = Frame.one Kind.journal.header
      ++ Frame.encode ([Prelude.manifestFrame system (Entry.own input),
        Prelude.schemaFrame (Entry.own input)] ++ write input entries) := by
    simp [file, frames, prelude, Prelude.frames]
  have hj := Kind.formerly_cut_of .journal .journal (Frame.encode ([Prelude.manifestFrame system
    (Entry.own input), Prelude.schemaFrame (Entry.own input)] ++ write input entries)) n
  have hs := Kind.formerly_cut_of .snapshot .journal (Frame.encode ([Prelude.manifestFrame system
    (Entry.own input), Prelude.schemaFrame (Entry.own input)] ++ write input entries)) n
  rw [← hone] at hj hs
  rw [← file] at hdecode htail
  unfold verify
  generalize Frame.whole (frames input system entries) n = m at hdecode htail
  match m with
  | 0 =>
    simp only [List.take_zero] at hdecode htail
    simp [inspect, hdecode, hj, hs, tailFindings_none htail]
  | 1 =>
    simp [frames, prelude, Prelude.frames] at hdecode htail
    simp [inspect, hdecode, Kind.of?, tailFindings_unfinished htail]
  | 2 =>
    simp [frames, prelude, Prelude.frames] at hdecode htail
    simp [inspect, hdecode, Kind.of?, tailFindings_unfinished htail]
  | k + 3 =>
    have htake : (frames input system entries).take (k + 3)
        = prelude input system ++ (write input entries).take k := by
      simp [frames, prelude, Prelude.frames]
    rw [htake] at hdecode htail
    simp [(inspect_whole input hsystem h hdecode htail hr).1]

/-- What the writer writes as a snapshot passes `verify`, alone or with the reader's own schema,
and `dump` shows the one record written. -/
theorem inspect_saved {sys : System σ} (c : Kernel.Image.Codecs sys) {system : String}
    {index : Nat} {image : Kernel.Image sys} (h : savedFits c system index image = true)
    {reader : Option Schema} (hr : reader = none ∨ reader = some (savedOf c).schema) :
    verify (saved c system index image) reader = true
      ∧ (inspect (saved c system index image) reader).records.map (·.value)
        = [.ok ((savedOf c).toValue (index, image))] := by
  obtain ⟨hp, hbody, -⟩ := savedBody_ok h
  obtain ⟨plan, hplan, hfor⟩ := planFor_same (ms := []) hr
  have hread : Body.read Kind.snapshot.limits (savedOf c).schema (okBytes (savedBody c index image))
      = .ok ((savedOf c).toValue (index, image)) := Body.read_write hbody
  have hsize : Frame.span (savedRecords c system index image)
      = (saved c system index image).size := by
    rw [saved, Frame.size_encode]
  have hdecode := decode_saved h
  simp only [savedRecords, Prelude.frames, List.cons_append, List.nil_append] at hdecode hsize
  have hrec : (records Kind.snapshot.limits (savedOf c).schema 0
      (60 + Kind.snapshot.header.size + (Prelude.manifestFrame system (savedOf c).schema).size
        + (Prelude.schemaFrame (savedOf c).schema).size)
      [okBytes (savedBody c index image)]).map (·.value)
        = [(savedOf c).toValue (index, image)].map .ok := by
    simp [records, hread]
  have hne : Kind.snapshot.header ≠ Kind.journal.header := by decide
  simp only [verify, inspect, hdecode, Kind.of?, hne, ↓reduceIte, ofPrelude,
    Prelude.read_frames hp (reader := none) (by simp), hfor, hsize, Tail.of]
  simp [filterMap_finding hplan hrec, tailFindings, hrec]


/-! The text and the JSON of what was found. -/

namespace Inspect

def Tail.text : Tail → String
  | .clean => "the file ends after its last frame"
  | .torn byte => s!"torn at byte {byte}: a write that did not finish, which opening a journal \
      cuts off"
  | .damaged byte => s!"damaged at byte {byte}: a frame all there that does not check"

def refusalText : Refusal → String
  | .foreign (some named) => s!"the manifest names the system {named.quote}"
  | .foreign none => "not a journal or a snapshot of Lanes"
  | .unreadable entry => s!"entry {entry} cannot be read"
  | .damaged byte => s!"the frame at byte {byte} is all there and does not check"
  | .snapshot => "a snapshot whose prelude is not whole"
  | .apart => "the journal does not continue its snapshot"
  | .name => "the prelude is too large"
  | .missing => "there is no file"
  | .format 1 => "format 1, which this Lanes does not read: move the file aside to begin anew"
  | .format version => s!"format {version}, which this Lanes does not read"
  | .manifest => "the manifest does not read, or does not name the schema frame after it"
  | .policy runtime version => s!"written by the runtime {runtime.quote} under policy \
      {version}, not by {Journal.runtime.quote} under policy {Journal.policy}"
  | .schema error => s!"the schema: {error}"

def Finding.text : Finding → String
  | .refused refusal => refusalText refusal
  | .record index byte error => s!"record {index} at byte {byte} does not read with the \
      file's schema: {error}"
  | .reader error => s!"the reader's schema cannot read the file's: {error}"
  | .unreadable index byte error => s!"record {index} at byte {byte} does not read with the \
      reader's schema: {error}"
  | .torn byte => s!"the snapshot is torn at byte {byte}: a snapshot is written whole, so it \
      does not open"
  | .count n => s!"the snapshot holds {n} records, not one"

/-- The check of `verify` a finding fails. -/
def Finding.check : Finding → String
  | .refused (.damaged _) => "frames"
  | .refused _ => "prelude"
  | .record .. | .count _ => "records"
  | .reader _ | .unreadable .. => "reader"
  | .torn _ => "frames"

/-- At most `shown` texts, then how many more. -/
def bounded (shown : Nat) (texts : List String) : String :=
  "; ".intercalate (texts.take shown
    ++ if texts.length > shown then [s!"and {texts.length - shown} more"] else [])

end Inspect

namespace Inspection

open Inspect

def kindName (i : Inspection) : String :=
  (i.kind.map Kind.name).getD "file"

def kindJson (i : Inspection) : Json :=
  (i.kind.map fun k => Json.str k.name).getD .null

def systemText (m : Manifest) : String :=
  m.system.replace "\nversion " ", version "

/-- The checks `verify` makes of this file, in order. A file that is no file of format 2 has
no frames to check. -/
def checks (i : Inspection) : List String :=
  if i.kind.isNone ∧ i.findings.any (·.check == "prelude") then ["prelude"] else
  ["frames", "prelude"]
    ++ (if i.schema.isSome then ["records"] else [])
    ++ (if i.schema.isSome ∧ i.compared then ["reader"] else [])

/-- What a check that passed found. -/
def passed (i : Inspection) : String → String
  | "frames" => "every whole frame's length and checksum; " ++ i.tail.text
  | "prelude" =>
    match i.manifest, i.schema with
    | some m, some _ => s!"format 2, a {i.kindName} of {(systemText m).quote}; the manifest \
        names the schema frame, which reads"
    | _, _ => "no whole prelude: the journal of nothing, as opening reads it"
  | "records" => s!"{i.records.length} records read with the file's schema"
  | _ => "the reader's schema reads the file's, and every record through it"

/-- Each check, whether it passed, and what it found; at most `shown` findings each. -/
def results (i : Inspection) (shown : Nat := 10) : List (String × Bool × String) :=
  i.checks.map fun name =>
    match i.findings.filter (·.check == name) with
    | [] => (name, true, i.passed name)
    | found => (name, false, bounded shown (found.map (·.text)))

/-- `lanes journal verify` as text: a line a check, then the counts. -/
def verifyText (i : Inspection) : String :=
  let rs := i.results
  let failed := rs.countP (!·.2.1)
  "\n".intercalate (rs.map (fun (name, ok, detail) =>
      (if ok then "ok " else "FAIL ") ++ name ++ ": " ++ detail)
    ++ [s!"{rs.length - failed} passed, {failed} failed"])

def manifestJson (m : Manifest) : Json :=
  .obj #[("format", .num m.format), ("lanes", .str m.lanes), ("commit", .str m.commit),
    ("system", .str m.system), ("toolchain", .str m.toolchain), ("runtime", .str m.runtime),
    ("policy", .num m.policy), ("schema", .str (Bytes.hex m.schema))]

def tailJson : Tail → Json
  | .clean => .obj #[("state", .str "clean")]
  | .torn byte => .obj #[("state", .str "torn"), ("byte", .num byte)]
  | .damaged byte => .obj #[("state", .str "damaged"), ("byte", .num byte)]

/-- `lanes journal verify --json`: the results as `Lanes.Testing` prints them (D104), each a
check, and what the file is. -/
def verifyJson (i : Inspection) : Json :=
  let rs := i.results
  let failed := rs.countP (!·.2.1)
  .obj #[("passed", .num (rs.length - failed)), ("bounded", .num 0), ("failed", .num failed),
    ("results", .arr (rs.map fun (name, ok, detail) => Json.obj #[("name", .str name),
      ("kind", .str "check"), ("status", .str (if ok then "passed" else "failed")),
      ("detail", .str detail)]).toArray),
    ("file", .obj #[("kind", kindJson i), ("records", .num i.records.length),
      ("manifest", (i.manifest.map manifestJson).getD .null), ("tail", tailJson i.tail)])]

def recordText (s : Schema) (r : Record) : String :=
  s!"{r.index} at byte {r.byte}, {r.size} bytes: " ++ match r.value with
    | .ok v => s.display v
    | .error e => s!"does not read: {e}"

def recordJson (s : Schema) (r : Record) : Json :=
  .obj (#[("type", .str "record"), ("index", .num r.index), ("byte", .num r.byte),
    ("size", .num r.size)] ++ match r.value with
      | .ok v => #[("value", s.json v)]
      | .error e => #[("error", .str (toString e))])

def manifestLines (m : Manifest) : List String :=
  [s!"format {m.format}", s!"lanes {m.lanes}" ++ (if m.commit.isEmpty then "" else s!" {m.commit}"),
    s!"system {(systemText m).quote}", s!"toolchain {m.toolchain}",
    s!"runtime {m.runtime}, policy {m.policy}", s!"schema frame SHA-256 {Bytes.hex m.schema}"]

def indent (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map fun line => if line.isEmpty then line else "  " ++ line)

/-- `lanes journal dump` as text: the prelude, the records from place `start`, at most `count`
of them, and the tail; then what `verify` would find. -/
def dumpText (i : Inspection) (start : Nat := 0) (count : Option Nat := none) : String :=
  let at_ := fun k => match i.prelude[k]? with
    | some byte => s!" (frame at byte {byte})"
    | none => ""
  let rs := (i.records.drop start).take (count.getD i.records.length)
  let head := s!"{i.kindName}{at_ 0}" :: match i.manifest with
    | some m => s!"manifest{at_ 1}" :: (manifestLines m).map ("  " ++ ·)
    | none => []
  let schema := match i.schema with
    | some s => [s!"schema{at_ 2}", indent s.text.trimAscii.toString,
        s!"records: {i.records.length}"] ++ rs.map (fun r => "  " ++ recordText s r)
    | none => []
  let found := if i.findings.isEmpty then []
    else "found:" :: i.findings.map ("  " ++ ·.text)
  "\n".intercalate (head ++ schema ++ [s!"tail: {i.tail.text}"] ++ found)

/-- `lanes journal dump --json`: JSON lines, the file first, then a line a record, then the tail
and what `verify` would find. -/
def dumpJson (i : Inspection) (start : Nat := 0) (count : Option Nat := none) : List Json :=
  let rs := (i.records.drop start).take (count.getD i.records.length)
  let file := Json.obj #[("type", .str "file"), ("kind", kindJson i),
    ("prelude", .arr (i.prelude.map fun (b : Nat) => Json.num b).toArray),
    ("manifest", (i.manifest.map manifestJson).getD .null),
    ("schema", (i.schema.map fun s => Json.str s.text).getD .null),
    ("records", .num i.records.length)]
  let records := match i.schema with
    | some s => rs.map (recordJson s)
    | none => []
  file :: records
    ++ [.obj #[("type", .str "tail"), ("tail", tailJson i.tail),
      ("findings", .arr (i.findings.map fun f => Json.obj #[("check", .str f.check),
        ("detail", .str f.text)]).toArray)]]

end Inspection

end Journal

end Lanes
