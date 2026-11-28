/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.Log
public import Lanes.Data.Codec
public import Lanes.Durable.Frame

/-!
The journal of a shard as bytes: how its entries (`Lanes/Runtime/Log.lean`) become the bytes
of a file, which files are opened and which refused (`open?`), and that a file cut short by a
crash opens and gives the entries before the cut (`open?_cut`).
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

namespace Entry

/-- Built from codecs that carry their laws, so this one does too. -/
def codec (input : Codec σ.In) : Codec (Entry σ) :=
  (Codec.sum input (Codec.sum Codec.nat (Codec.sum Codec.nat
      (Codec.sum Codec.unit Codec.nat)))).map
    (fun
      | .input x => .inl x
      | .advance now_ms => .inr (.inl now_ms)
      | .batch fuel => .inr (.inr (.inl fuel))
      | .handed => .inr (.inr (.inr (.inl ())))
      | .snapshot index => .inr (.inr (.inr (.inr index))))
    (fun
      | .inl x => some (.input x)
      | .inr (.inl now_ms) => some (.advance now_ms)
      | .inr (.inr (.inl fuel)) => some (.batch fuel)
      | .inr (.inr (.inr (.inl ()))) => some .handed
      | .inr (.inr (.inr (.inr index))) => some (.snapshot index))
    (by intro entry; cases entry <;> rfl)

/-- An entry is one frame on disk, so a torn write loses whole entries and never part of one.
Inside it the entry's records are framed again. -/
def bytes (input : Codec σ.In) (entry : Entry σ) : ByteArray :=
  Frame.encode ((codec input).write entry)

def ofBytes (input : Codec σ.In) (payload : ByteArray) : Option (Entry σ) :=
  match (codec input).read (Frame.decode payload) with
  | some (entry, []) => some entry
  | _ => none

/-- Whether the entry can be framed: no record of it, nor all of it, reaches 4 GiB. -/
def fits (input : Codec σ.In) (entry : Entry σ) : Bool :=
  ((codec input).write entry).all Frame.fits && Frame.fits (bytes input entry)

theorem ofBytes_bytes (input : Codec σ.In) {entry : Entry σ} (h : fits input entry = true) :
    ofBytes input (bytes input entry) = some entry := by
  simp only [fits, Bool.and_eq_true] at h
  have hsound := (codec input).sound entry []
  simp only [List.append_nil] at hsound
  simp [ofBytes, bytes, Frame.decode_encode (Frame.all_fits_iff.mp h.1), hsound]

end Entry

def write (input : Codec σ.In) (entries : List (Entry σ)) : List ByteArray :=
  entries.map (Entry.bytes input)

/-- The entries at the start of `payloads`, up to the first that cannot be read. -/
def read (input : Codec σ.In) : List ByteArray → List (Entry σ)
  | payload :: rest =>
    match Entry.ofBytes input payload with
    | some entry => entry :: read input rest
    | none => []
  | [] => []

theorem read_write (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    read input (write input entries) = entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [write, List.map_cons, read,
      Entry.ofBytes_bytes input (h entry List.mem_cons_self)]
    exact congrArg (entry :: ·) (ih fun e he => h e (List.mem_cons_of_mem _ he))

theorem read_prefix (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) {payloads : List ByteArray}
    (hprefix : payloads <+: write input entries) : read input payloads <+: entries := by
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

/-- The first frame of a journal file. A journal is a list of requests, and means something only
to the step functions that answered them, so `system` is the application's name for those: a
file with another name is refused. -/
def header (system : String) : ByteArray :=
  ("lanes journal 1\n" ++ system).toUTF8

/-- What names a store's files: the application's name for its system and the version of its
types. Version 0 is the name alone, as every journal was named before there were versions, so
those journals are version 0. A file of an older version is read through an upgrade
(`Lanes.Journal.Upgrade`). -/
def label (system : String) (version : Nat) : String :=
  if version = 0 then system else system ++ "\nversion " ++ toString version

theorem label_zero (system : String) : label system 0 = system := by
  simp [label]

theorem header_inj {a b : String} (h : header a = header b) : a = b := by
  have := congrArg String.fromUTF8? h
  rw [header, header, Codec.fromUTF8?_toUTF8, Codec.fromUTF8?_toUTF8] at this
  simpa using this

/-- The system a journal file's first frame names, if it is the header of a journal. -/
def named? (first : ByteArray) : Option String :=
  (String.fromUTF8? first).bind fun text => (text.dropPrefix? "lanes journal 1\n").map (·.toString)

def file (input : Codec σ.In) (system : String) (entries : List (Entry σ)) : ByteArray :=
  Frame.encode (header system :: write input entries)

theorem file_eq (input : Codec σ.In) (system : String) (entries : List (Entry σ)) :
    file input system entries = Frame.one (header system) ++ encode input entries :=
  Frame.encode_cons ..

/-- Why a journal's files are not opened. A refused file is left as it is. -/
inductive Refusal where
  /-- The file is not a journal of `system`: it is the journal of the system `named`, or no
  journal at all. -/
  | foreign (named : Option String)
  /-- An entry is intact on disk and cannot be read: it was written with another codec. -/
  | unreadable (entry : Nat)
  /-- A frame is all there and does not check. -/
  | damaged (byte : Nat)
  /-- The snapshot file does not read back whole as a snapshot of `system`. -/
  | snapshot
  /-- The journal does not continue the snapshot (`resume`). -/
  | apart
  /-- The system's name does not fit in a frame, so no journal can carry it. -/
  | name
  /-- There is no journal, and the store may not begin one (`Disk.start`). -/
  | missing
  deriving DecidableEq, Repr

/--
The entries of a journal file and the bytes that hold them. Bytes after those are a write that
did not finish, which is what the death of the process leaves (`open?_cut`), and may be cut off.
Everything else that is wrong is refused, never repaired: cutting a file at the first thing
that cannot be read would delete a journal that was opened with the wrong codec.
-/
def open? (input : Codec σ.In) (system : String) (bytes : ByteArray) :
    Except Refusal (List (Entry σ) × Nat) :=
  match Frame.decode bytes with
  | [] => if Frame.unfinished bytes 0 then .ok ([], 0) else .error (.damaged 0)
  | first :: payloads =>
    let entries := read input payloads
    let size := Frame.span (first :: payloads)
    if first ≠ header system then .error (.foreign (named? first))
    else if entries.length < payloads.length then .error (.unreadable entries.length)
    else if Frame.unfinished bytes size then .ok (entries, size)
    else .error (.damaged size)

private theorem frames_fit (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : Frame.fits (header system) = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    ∀ p ∈ header system :: write input entries, p.size < 2 ^ 32 := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact Frame.fits_iff.mp hsystem
  · obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hp
    have := h entry hentry
    simp only [Entry.fits, Bool.and_eq_true] at this
    exact Frame.fits_iff.mp this.2

/-- A journal file cut off at any byte, as when the process dies during a write, opens, and
gives exactly the entries wholly written before the cut: never a refusal, never a wrong entry,
never one out of order. -/
theorem open?_cut (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : Frame.fits (header system) = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (n : Nat) :
    open? input system ((file input system entries).extract 0 n)
      = .ok (entries.take (Frame.whole (header system :: write input entries) n - 1),
          Frame.span ((header system :: write input entries).take
            (Frame.whole (header system :: write input entries) n))) := by
  have hfit := frames_fit input hsystem h
  have hdecode := Frame.decode_take_eq hfit n
  have htail := Frame.unfinished_take hfit n
  unfold open? file
  generalize Frame.whole (header system :: write input entries) n = m at hdecode htail ⊢
  cases m with
  | zero =>
    rw [hdecode]
    simpa [Frame.span] using htail
  | succ j =>
    rw [hdecode]
    simp only [List.take_succ_cons] at htail ⊢
    have hread : read input ((write input entries).take j) = entries.take j := by
      rw [write, ← List.map_take, ← write,
        read_write input fun e he => h e (List.mem_of_mem_take he)]
    have hlen : ((write input entries).take j).length = (entries.take j).length := by
      simp [write]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, hread, hlen, Nat.lt_irrefl, htail,
      Nat.add_sub_cancel]

theorem open?_file (input : Codec σ.In) {system : String} {entries : List (Entry σ)}
    (hsystem : Frame.fits (header system) = true)
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    open? input system (file input system entries)
      = .ok (entries, (file input system entries).size) := by
  have hfit := frames_fit input hsystem h
  unfold open?
  rw [file, Frame.decode_encode hfit]
  have hlen : (write input entries).length = entries.length := by simp [write]
  have htail : Frame.unfinished (Frame.encode (header system :: write input entries))
      (Frame.span (header system :: write input entries)) = true :=
    Frame.unfinished_of_size_le (by rw [Frame.size_encode]; exact Nat.le_refl _)
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, read_write input h, hlen, Nat.lt_irrefl,
    htail, Frame.size_encode]

end Lanes.Journal
