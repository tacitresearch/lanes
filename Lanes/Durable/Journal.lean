/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Log
public import Lanes.Durable.Format

/-!
The journal of a shard as bytes: how its entries (`Lanes/Runtime/Log.lean`) become the bytes
of a file, which files are opened and which refused (`open?`), and that a file cut short by a
crash opens and gives the entries before the cut (`open?_cut`).

A file is in format 2 (`Lanes/Durable/Format.lean`): the prelude, then one frame per entry, whose
payload is the entry's body. An entry is read through the plan from the file's schema to the
reader's, so a journal written with an older schema of the inputs opens.
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

namespace Entry

/-- The schema of an entry, with the inputs' schema, and the map each way to `Value`. -/
def schema (input : Codec σ.In) : Schema.Of (Entry σ) :=
  (Schema.Of.variants "Lanes.Journal.Entry" [input.schema]
    (.cons "input" [] (.cons "x" [] input.toOf none .nil)
      (.cons "advance" [] (.cons "now_ms" [] .nat none .nil)
        (.cons "batch" [] (.cons "fuel" [] .nat none .nil)
          (.cons "handed" [] .nil
            (.cons "snapshot" [] (.cons "index" [] .nat none .nil) .nil)))))).map
    (fun
      | .input x => .inl (x, ())
      | .advance now_ms => .inr (.inl (now_ms, ()))
      | .batch fuel => .inr (.inr (.inl (fuel, ())))
      | .handed => .inr (.inr (.inr (.inl ())))
      | .snapshot index => .inr (.inr (.inr (.inr (.inl (index, ()))))))
    (fun
      | .inl (x, ()) => some (.input x)
      | .inr (.inl (now_ms, ())) => some (.advance now_ms)
      | .inr (.inr (.inl (fuel, ()))) => some (.batch fuel)
      | .inr (.inr (.inr (.inl ()))) => some .handed
      | .inr (.inr (.inr (.inr (.inl (index, ()))))) => some (.snapshot index)
      | .inr (.inr (.inr (.inr (.inr e)))) => nomatch e)
    (by intro entry; cases entry <;> rfl)

/-- The schema a binary writes its entries with. -/
abbrev own (input : Codec σ.In) : Schema := (schema input).schema

/-- The schema of an entry whose inputs have the schema `input`, for a reader that has no codec
of them, such as `lanes journal verify` (`own_eq_schemaOf`). -/
def schemaOf (input : Schema) : Schema :=
  .sum "Lanes.Journal.Entry" [input]
    [{ name := "input", fields := [{ name := "x", schema := input }] },
     { name := "advance", fields := [{ name := "now_ms", schema := .nat }] },
     { name := "batch", fields := [{ name := "fuel", schema := .nat }] },
     { name := "handed", fields := [] },
     { name := "snapshot", fields := [{ name := "index", schema := .nat }] }]

theorem own_eq_schemaOf (input : Codec σ.In) : own input = schemaOf input.schema := rfl

def write (input : Codec σ.In) (entry : Entry σ) : Except Codec.Error ByteArray :=
  Body.encode Kind.journal.limits (schema input) entry

/-- An entry is one frame on disk, so a torn write loses whole entries and never part of one.
Its payload is its body. -/
def bytes (input : Codec σ.In) (entry : Entry σ) : ByteArray :=
  okBytes (write input entry)

/-- The entry a payload holds, written with the schema `writer` and read through `plan`, the
plan from it to the reader's. -/
def ofBytes (input : Codec σ.In) (writer : Schema) (plan : Schema.Plan) (payload : ByteArray) :
    Option (Entry σ) :=
  (Body.decodeWith Kind.journal.limits writer plan (schema input) payload).toOption

/-- Whether the entry can be written: its body within the journal's bounds, and within a frame. -/
def fits (input : Codec σ.In) (entry : Entry σ) : Bool :=
  match write input entry with
  | .ok bytes => Frame.fits bytes
  | .error _ => false

theorem write_of_fits {input : Codec σ.In} {entry : Entry σ} (h : fits input entry = true) :
    write input entry = .ok (bytes input entry) ∧ (bytes input entry).size < 2 ^ 32 := by
  unfold fits at h
  unfold bytes
  split at h
  · next b hb => exact ⟨by rw [hb]; rfl, by rw [hb]; exact Frame.fits_iff.mp h⟩
  · cases h

theorem ofBytes_bytes (input : Codec σ.In) {entry : Entry σ} (h : fits input entry = true) :
    ofBytes input (own input) .same (bytes input entry) = some entry := by
  simp [ofBytes, Body.decodeWith_same, Body.decode_encode (write_of_fits h).1, Except.toOption]

end Entry

def write (input : Codec σ.In) (entries : List (Entry σ)) : List ByteArray :=
  entries.map (Entry.bytes input)

/-- The entries at the start of `payloads`, up to the first that cannot be read. -/
def read (input : Codec σ.In) (writer : Schema) (plan : Schema.Plan) :
    List ByteArray → List (Entry σ)
  | payload :: rest =>
    match Entry.ofBytes input writer plan payload with
    | some entry => entry :: read input writer plan rest
    | none => []
  | [] => []

theorem read_write (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    read input (Entry.own input) .same (write input entries) = entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [write, List.map_cons, read,
      Entry.ofBytes_bytes input (h entry List.mem_cons_self)]
    exact congrArg (entry :: ·) (ih fun e he => h e (List.mem_cons_of_mem _ he))

theorem read_prefix (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) {payloads : List ByteArray}
    (hprefix : payloads <+: write input entries) :
    read input (Entry.own input) .same payloads <+: entries := by
  obtain ⟨k, rfl⟩ : ∃ k, payloads = (write input entries).take k :=
    ⟨payloads.length, (List.prefix_iff_eq_take.mp hprefix)⟩
  rw [write, ← List.map_take, ← write,
    read_write input fun e he => h e (List.mem_of_mem_take he)]
  exact List.take_prefix k entries

/-- What is appended to a journal file for `entries`: a frame each. -/
def encode (input : Codec σ.In) (entries : List (Entry σ)) : ByteArray :=
  Frame.encode (write input entries)

theorem encode_append (input : Codec σ.In) (a b : List (Entry σ)) :
    encode input (a ++ b) = encode input a ++ encode input b := by
  simp [encode, write, Frame.encode_append]

/-- What names a store's files: the application's name for its system and the version of its
types. Version 0 is the name alone, as every journal was named before there were versions, so
those journals are version 0. A file of an older version is read through an upgrade
(`Lanes.Journal.Upgrade`). -/
def label (system : String) (version : Nat) : String :=
  if version = 0 then system else system ++ "\nversion " ++ toString version

theorem label_zero (system : String) : label system 0 = system := by
  simp [label]

/-- The first three frames of a journal file. A journal is a list of requests, and means
something only to the step functions that answered them, so its manifest names `system`, the
application's name for those: a file of another name is refused. -/
def prelude (input : Codec σ.In) (system : String) : List ByteArray :=
  Prelude.frames .journal system (Entry.own input)

/-- Whether the prelude can be written. -/
def preludeFits (input : Codec σ.In) (system : String) : Bool :=
  Prelude.fits .journal system (Entry.own input)

/-- The frames of a journal file of `entries`. -/
def frames (input : Codec σ.In) (system : String) (entries : List (Entry σ)) : List ByteArray :=
  prelude input system ++ write input entries

def file (input : Codec σ.In) (system : String) (entries : List (Entry σ)) : ByteArray :=
  Frame.encode (frames input system entries)

theorem file_eq (input : Codec σ.In) (system : String) (entries : List (Entry σ)) :
    file input system entries = Frame.encode (prelude input system) ++ encode input entries :=
  Frame.encode_append ..

/-- The system a journal file names, if it begins with the prelude of a journal of format 2. -/
def named? (bytes : ByteArray) : Option String :=
  match Frame.decode bytes with
  | first :: manifest :: _ => Prelude.named? .journal first manifest
  | _ => none

/-- The manifest of a journal file, if it begins with the prelude of a journal of format 2. -/
def manifest? (bytes : ByteArray) : Option Manifest :=
  match Frame.decode bytes with
  | first :: manifest :: _ =>
    if first = Kind.journal.header then
      (Body.decode schemaLimits Manifest.codec.toOf manifest).toOption
    else none
  | _ => none

/--
The entries of a journal file and the bytes that hold them. Bytes after those are a write that
did not finish, which is what the death of the process leaves (`open?_cut`), and may be cut off.
A file whose prelude is not whole is the journal of nothing, and holds no bytes worth keeping.
Everything else that is wrong is refused, never repaired: cutting a file at the first thing
that cannot be read would delete a journal that was opened with the wrong codec. A file of format
1 is refused as such.
-/
def open? (input : Codec σ.In) (system : String) (bytes : ByteArray) :
    Except Refusal (List (Entry σ) × Nat) :=
  match Frame.decode bytes with
  | first :: manifest :: schema :: payloads =>
    match Prelude.check .journal system (Entry.own input) first manifest schema with
    | .error refusal => .error refusal
    | .ok (writer, plan) =>
      let entries := read input writer plan payloads
      let size := Frame.span (first :: manifest :: schema :: payloads)
      if entries.length < payloads.length then .error (.unreadable entries.length)
      else if Frame.unfinished bytes size then .ok (entries, size)
      else .error (.damaged size)
  | few =>
    if Kind.journal.formerly bytes then .error (.format 1)
    else if few.head?.any (· ≠ Kind.journal.header) then
      .error (Prelude.other .journal (few.head?.getD .empty))
    else if Frame.unfinished bytes (Frame.span few) then .ok ([], 0)
    else .error (.damaged (Frame.span few))

theorem frames_fit (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    ∀ p ∈ frames input system entries, p.size < 2 ^ 32 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact Prelude.fits_frames hsystem p hp
  · obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hp
    exact (Entry.write_of_fits (h entry hentry)).2

private theorem file_one (input : Codec σ.In) (system : String) (entries : List (Entry σ)) :
    file input system entries
      = Frame.one Kind.journal.header
        ++ Frame.encode ([Prelude.manifestFrame system (Entry.own input),
          Prelude.schemaFrame (Entry.own input)] ++ write input entries) := by
  simp [file, frames, prelude, Prelude.frames]

private theorem open?_whole (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (bytes : ByteArray) (k : Nat)
    (hdecode : Frame.decode bytes = prelude input system ++ (write input entries).take k)
    (htail : Frame.unfinished bytes (Frame.span (prelude input system
      ++ (write input entries).take k)) = true) :
    open? input system bytes
      = .ok (entries.take k, Frame.span (prelude input system ++ (write input entries).take k)) := by
  have hread : read input (Entry.own input) .same ((write input entries).take k)
      = entries.take k := by
    rw [write, ← List.map_take, ← write,
      read_write input fun e he => h e (List.mem_of_mem_take he)]
  have hlen : ((write input entries).take k).length = (entries.take k).length := by
    simp [write]
  unfold open?
  rw [hdecode]
  simp only [prelude, Prelude.frames, List.cons_append, List.nil_append,
    Prelude.check_frames hsystem]
  simp only [prelude, Prelude.frames, List.cons_append, List.nil_append] at htail
  simp only [hread, hlen, Nat.lt_irrefl, ↓reduceIte, htail]

/-- A journal file cut off at any byte, as when the process dies during a write, opens, and
gives exactly the entries wholly written before the cut: never a refusal, never a wrong entry,
never one out of order. A cut inside the prelude leaves the journal of nothing. -/
theorem open?_cut (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (n : Nat) :
    open? input system ((file input system entries).extract 0 n)
      = .ok (entries.take (Frame.whole (frames input system entries) n - 3),
          if Frame.whole (frames input system entries) n < 3 then 0
          else Frame.span ((frames input system entries).take
            (Frame.whole (frames input system entries) n))) := by
  have hfit := frames_fit input hsystem h
  have hdecode := Frame.decode_take_eq hfit n
  have htail := Frame.unfinished_take hfit n
  have hformer := Kind.formerly_cut .journal (Frame.encode ([Prelude.manifestFrame system
    (Entry.own input), Prelude.schemaFrame (Entry.own input)] ++ write input entries)) n
  rw [← file_one] at hformer
  rw [← file] at hdecode htail
  generalize Frame.whole (frames input system entries) n = m at hdecode htail ⊢
  match m with
  | 0 =>
    unfold open?
    simp [hdecode, hformer, Frame.span] at htail ⊢
    exact htail
  | 1 =>
    unfold open?
    simp [frames, prelude, Prelude.frames] at hdecode htail
    simp [hdecode, hformer, htail]
  | 2 =>
    unfold open?
    simp [frames, prelude, Prelude.frames] at hdecode htail
    simp [hdecode, hformer, htail]
  | k + 3 =>
    have htake : (frames input system entries).take (k + 3)
        = prelude input system ++ (write input entries).take k := by
      simp [frames, prelude, Prelude.frames]
    rw [htake] at hdecode htail
    rw [open?_whole input hsystem h _ k hdecode htail, htake]
    simp only [Nat.add_sub_cancel, Nat.not_lt.mpr (Nat.le_add_left 3 k), ↓reduceIte]

theorem open?_file (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : preludeFits input system = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    open? input system (file input system entries)
      = .ok (entries, (file input system entries).size) := by
  have hfit := frames_fit input hsystem h
  have hlen : (write input entries).length = entries.length := by simp [write]
  have hdecode : Frame.decode (file input system entries)
      = prelude input system ++ (write input entries).take entries.length := by
    rw [file, Frame.decode_encode hfit, List.take_of_length_le (by omega)]; rfl
  have htail : Frame.unfinished (file input system entries)
      (Frame.span (prelude input system ++ (write input entries).take entries.length)) = true := by
    rw [List.take_of_length_le (by omega)]
    exact Frame.unfinished_of_size_le (by rw [file, Frame.size_encode]; exact Nat.le_refl _)
  rw [open?_whole input hsystem h _ _ hdecode htail, List.take_of_length_le (by simp),
    List.take_of_length_le (by omega), file, Frame.size_encode]
  rfl

end Lanes.Journal
