/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.KernelSound
public import Lanes.Runtime.Wave
public import Lanes.Durable.Format

/-!
The journal of a shard: everything it asks of its kernel, in order. The kernel is a pure
function of those requests, so replaying a journal gives back the state it describes, and that
is how a shard survives its process (`docs/decisions/` D24).

This file is the pure part: what an entry is, how a journal becomes the bytes of a file, which
files are opened and which refused (`open?`), that a file cut short by a crash opens and gives
the entries before the cut, and that `recover` rebuilds the kernel the entries describe.

A file is in format 2 (`Lanes/Durable/Format.lean`): the prelude, then one frame per entry, whose
payload is the entry's body. An entry is read through the plan from the file's schema to the
reader's, so a journal written with an older schema of the inputs opens.
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

/-- One thing a shard asked of its kernel: an input, a clock reading, a batch of work, or a
mark. Replaying the entries rebuilds the kernel (`Journal.recover_kernel`). -/
inductive Entry (σ : Signature) where
  | input (x : σ.In)
  | advance (now_ms : Nat)
  | batch (fuel : Nat)
  /-- Every output produced so far has been handed over. After a restart, only the outputs
  after the last such mark are handed over again. -/
  | handed
  /-- The kernel was saved here, `index` entries into the shard's history, and every output
  produced so far had been handed over. The entries before this one are then no longer needed,
  and a journal file may have lost them. -/
  | snapshot (index : Nat)

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

/-! Recovery: replay the entries through the kernel. -/

variable [Hashable σ.Id]

def Entry.op? : Entry σ → Option (Kernel.Op σ)
  | .input x => some (.input x)
  | .advance now_ms => some (.advance now_ms)
  | .batch fuel => some (.batch fuel)
  | .handed => none
  | .snapshot _ => some .snapshot

/-- Whether the entry says that every output so far has been handed over. -/
def Entry.marks : Entry σ → Bool
  | .handed | .snapshot _ => true
  | _ => false

def ops (entries : List (Entry σ)) : List (Kernel.Op σ) :=
  entries.filterMap Entry.op?

/-- One entry replayed: the kernel after it, and the outputs not yet known to be handed over. -/
def replay1 {sys : System σ} (acc : Kernel sys × List σ.Out) (entry : Entry σ) :
    Kernel sys × List σ.Out :=
  match acc, entry with
  | (k, _), .handed => (k, [])
  | (k, _), .snapshot _ => (k.image.kernel, [])
  | (k, pending), .advance now_ms => (k.advance now_ms, pending)
  | (k, pending), .input x =>
    match k.accept x with
    | { kernel, outputs, .. } => (kernel, pending ++ outputs)
  | (k, pending), .batch fuel =>
    match k.runBatch fuel with
    | { kernel, outputs, .. } => (kernel, pending ++ outputs)

/-- The kernel a journal describes, and the outputs to hand over again: those produced after
the last `handed` mark. -/
def recover (sys : System σ) (past : List (Entry σ)) : Kernel sys × List σ.Out :=
  past.foldl replay1 (Kernel.boot sys)

/-- `recover` from another start than boot: a kernel and the outputs it has not handed over. A
shard whose kernel was migrated from an older system's starts there (`Lanes.Migration`). -/
def replay {sys : System σ} (start : Kernel sys × List σ.Out) (past : List (Entry σ)) :
    Kernel sys × List σ.Out :=
  past.foldl replay1 start

theorem replay1_handed {sys : System σ} (k : Kernel sys) (pending : List σ.Out) :
    replay1 (k, pending) .handed = (k, []) := rfl

theorem replay1_snapshot {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (index : Nat) :
    replay1 (k, pending) (.snapshot index) = (k.image.kernel, []) := rfl

theorem replay1_advance {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (now_ms : Nat) :
    replay1 (k, pending) (.advance now_ms) = (k.advance now_ms, pending) := rfl

theorem replay1_input {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (x : σ.In) :
    replay1 (k, pending) (.input x) = ((k.accept x).kernel, pending ++ (k.accept x).outputs) := rfl

theorem replay1_batch {sys : System σ} (k : Kernel sys) (pending : List σ.Out) (fuel : Nat) :
    replay1 (k, pending) (.batch fuel)
      = ((k.runBatch fuel).kernel, pending ++ (k.runBatch fuel).outputs) := rfl

private theorem foldl_replay1 {sys : System σ} (past : List (Entry σ)) (k : Kernel sys)
    (pending : List σ.Out) :
    (past.foldl replay1 (k, pending)).1 = (k.exec (ops past)).kernel
      ∧ ∃ handed, pending ++ (k.exec (ops past)).outputs
          = handed ++ (past.foldl replay1 (k, pending)).2 := by
  induction past generalizing k pending with
  | nil => exact ⟨rfl, [], by simp [ops, Kernel.exec]⟩
  | cons entry past ih =>
    cases entry with
    | handed =>
      obtain ⟨hk, handed, hout⟩ := ih k []
      rw [List.foldl_cons, replay1_handed]
      refine ⟨hk, pending ++ handed, ?_⟩
      simp only [List.nil_append] at hout
      simp only [ops, List.filterMap_cons, Entry.op?] at hout ⊢
      rw [List.append_assoc, ← hout]
    | snapshot index =>
      obtain ⟨hk, handed, hout⟩ := ih k.image.kernel []
      rw [List.foldl_cons, replay1_snapshot]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk,
        pending ++ handed, ?_⟩
      simp only [List.nil_append] at hout
      simp only [ops, List.filterMap_cons, Entry.op?, Kernel.exec_cons, Kernel.apply,
        List.nil_append] at hout ⊢
      rw [List.append_assoc, ← hout]
    | advance now_ms =>
      obtain ⟨hk, handed, hout⟩ := ih (k.advance now_ms) pending
      rw [List.foldl_cons, replay1_advance]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk, handed, ?_⟩
      simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hout
    | input x =>
      obtain ⟨hk, handed, hout⟩ := ih (k.accept x).kernel (pending ++ (k.accept x).outputs)
      rw [List.foldl_cons, replay1_input]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk, handed, ?_⟩
      simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc] using hout
    | batch fuel =>
      obtain ⟨hk, handed, hout⟩ := ih (k.runBatch fuel).kernel
        (pending ++ (k.runBatch fuel).outputs)
      rw [List.foldl_cons, replay1_batch]
      refine ⟨by simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply] using hk, handed, ?_⟩
      simpa [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc] using hout

/-- Recovery rebuilds exactly the kernel that the journal's requests lead to from boot. By
`Kernel.exec_reachable` that is a state the semantics reaches by the events those requests
reported, with actors at rest released: the run before the crash, continued. -/
theorem recover_kernel (sys : System σ) (past : List (Entry σ)) :
    (recover sys past).1 = ((Kernel.boot sys).1.exec (ops past)).kernel :=
  (foldl_replay1 past (Kernel.boot sys).1 (Kernel.boot sys).2).1

/-- Replaying from any kernel gives the kernel the entries' requests lead to from it. -/
theorem replay_kernel {sys : System σ} (start : Kernel sys × List σ.Out) (past : List (Entry σ)) :
    (replay start past).1 = (start.1.exec (ops past)).kernel :=
  (foldl_replay1 past start.1 start.2).1

/-- What is handed over again after a restart is the tail of what the run produced: nothing is
invented and nothing is out of order. -/
theorem recover_outputs (sys : System σ) (past : List (Entry σ)) :
    ∃ handed, (Kernel.boot sys).2 ++ ((Kernel.boot sys).1.exec (ops past)).outputs
      = handed ++ (recover sys past).2 :=
  (foldl_replay1 past (Kernel.boot sys).1 (Kernel.boot sys).2).2

/-- Replaying entries with no mark among them keeps every output they produce. -/
theorem replay_unmarked {sys : System σ} (k : Kernel sys) (pending : List σ.Out)
    {rest : List (Entry σ)} (h : ∀ entry ∈ rest, entry.marks = false) :
    rest.foldl replay1 (k, pending)
      = ((k.exec (ops rest)).kernel, pending ++ (k.exec (ops rest)).outputs) := by
  induction rest generalizing k pending with
  | nil => simp [ops, Kernel.exec]
  | cons entry rest ih =>
    have hrest := fun e he => h e (List.mem_cons_of_mem _ he)
    cases entry with
    | handed => simpa [Entry.marks] using h .handed List.mem_cons_self
    | snapshot index => simpa [Entry.marks] using h (.snapshot index) List.mem_cons_self
    | advance now_ms =>
      rw [List.foldl_cons, replay1_advance, ih _ _ hrest]
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply]
    | input x =>
      rw [List.foldl_cons, replay1_input, ih _ _ hrest]
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc]
    | batch fuel =>
      rw [List.foldl_cons, replay1_batch, ih _ _ hrest]
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, List.append_assoc]

/-- What is handed over again after a restart is exactly what was produced after the last
`handed` mark: nothing from before it, and everything since. So an output that was produced and
not marked is never lost, and one that was marked is never repeated. -/
theorem recover_handed (sys : System σ) (past : List (Entry σ)) {rest : List (Entry σ)}
    (h : ∀ entry ∈ rest, entry.marks = false) :
    (recover sys (past ++ .handed :: rest)).2
      = ((recover sys past).1.exec (ops rest)).outputs := by
  rw [recover, List.foldl_append, List.foldl_cons, ← recover]
  obtain ⟨k, pending⟩ := recover sys past
  rw [replay1_handed, replay_unmarked k [] h]
  rfl

/-! Recovery from a saved kernel. The snapshot is a memo of the replay up to its mark, and
`resume_eq_recover` is the theorem that says so. -/

def Entry.savedAt : Entry σ → Option Nat
  | .snapshot index => some index
  | _ => none

/-- The entries after the mark of the snapshot taken at `index`. -/
def since (index : Nat) : List (Entry σ) → Option (List (Entry σ))
  | [] => none
  | entry :: rest => if entry.savedAt = some index then some rest else since index rest

/--
The kernel to start with, given the saved kernel if there is one and the entries in the journal
file. `none` means the two do not belong together, and the shard must not start: the file
begins with the mark of a snapshot that is not there, so its earlier entries are gone, or the
snapshot's mark is not in the file.
-/
def resume (sys : System σ) (saved : Option (Nat × Kernel.Image sys)) (past : List (Entry σ)) :
    Option (Kernel sys × List σ.Out) :=
  match saved, past with
  | none, .snapshot (_ + 1) :: _ => none
  | none, past => some (recover sys past)
  | some (index, image), past =>
    (since index past).map fun rest => rest.foldl replay1 (image.kernel, [])

omit [Hashable σ.Id] in
private theorem since_append (index : Nat) {before : List (Entry σ)} (rest : List (Entry σ))
    (h : ∀ entry ∈ before, entry.savedAt ≠ some index) :
    since index (before ++ .snapshot index :: rest) = some rest := by
  induction before with
  | nil => simp [since, Entry.savedAt]
  | cons entry before ih =>
    rw [List.cons_append, since]
    simp only [h entry List.mem_cons_self, ↓reduceIte]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- `resume_eq_recover` for a history that starts anywhere: the snapshot holds the kernel as
it was after `before`, replayed from `start`. -/
theorem resume_eq_replay (sys : System σ) (start : Kernel sys × List σ.Out)
    (before rest : List (Entry σ)) (index lost : Nat)
    (h : ∀ entry ∈ before, entry.savedAt ≠ some index) :
    resume sys (some (index, (replay start before).1.image))
        (before.drop lost ++ .snapshot index :: rest)
      = some (replay start (before ++ .snapshot index :: rest)) := by
  have hsince := since_append index (before := before.drop lost) rest fun e he =>
    h e (List.mem_of_mem_drop he)
  simp only [resume, hsince, Option.map_some, replay, List.foldl_append, List.foldl_cons]
  generalize before.foldl replay1 start = acc
  obtain ⟨k, pending⟩ := acc
  rfl

/--
Starting from a snapshot gives exactly what replaying the whole history gives: the same kernel
and the same outputs to hand over again. The history is `before`, the mark, then `rest`; the
snapshot holds the kernel as it was after `before`; and the file may have lost any number of
the entries before the mark, which is what cutting a journal does.
-/
theorem resume_eq_recover (sys : System σ) (before rest : List (Entry σ)) (index lost : Nat)
    (h : ∀ entry ∈ before, entry.savedAt ≠ some index) :
    resume sys (some (index, (recover sys before).1.image))
        (before.drop lost ++ .snapshot index :: rest)
      = some (recover sys (before ++ .snapshot index :: rest)) :=
  resume_eq_replay sys (Kernel.boot sys) before rest index lost h

/-! One turn of a shard, as a pure function: everything the shell asks of the kernel between two
looks at its inbox, and what it must write in the journal for it. -/

structure Turn (sys : System σ) where
  kernel : Kernel sys
  events : List (Event σ) := []
  outputs : List σ.Out := []
  entries : List (Entry σ) := []

/--
Take an input if there is one and do up to `fuel` units of work at time `now_ms`. If there is
no input and nothing to do yet, the kernel is left exactly as it was, clock included, and
nothing is journaled: so the journal always describes the kernel (`turn_eq_exec`).
-/
def turn {sys : System σ} (k : Kernel sys) (now_ms : Nat) (input : Option σ.In) (fuel : Nat) :
    Turn sys :=
  if input.isNone && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match input with
    | none =>
      match k.runBatch fuel with
      | { kernel, events, outputs } =>
        { kernel, events, outputs, entries := [.advance clock, .batch fuel] }
    | some x =>
      match k.accept x with
      | { kernel, events := accepted, .. } =>
        match kernel.runBatch fuel with
        | { kernel, events, outputs } =>
          { kernel, events := accepted ++ events, outputs
            entries := [.advance clock, .input x, .batch fuel] }

private theorem advance_clock {sys : System σ} (k : Kernel sys) (now_ms : Nat) :
    k.advance (k.advance now_ms).clock_ms = k.advance now_ms := by
  simp only [Kernel.advance]
  congr 1
  omega

/-- What a turn does is what replaying its journal entries does: the same kernel, the same
events, the same outputs. Nothing is assumed of the clock. -/
theorem turn_eq_exec {sys : System σ} (k : Kernel sys) (now_ms : Nat) (input : Option σ.In)
    (fuel : Nat) :
    (turn k now_ms input fuel).kernel = (k.exec (ops (turn k now_ms input fuel).entries)).kernel
      ∧ (turn k now_ms input fuel).events
          = (k.exec (ops (turn k now_ms input fuel).entries)).events
      ∧ (turn k now_ms input fuel).outputs
          = (k.exec (ops (turn k now_ms input fuel).entries)).outputs := by
  unfold turn
  split
  · exact ⟨rfl, rfl, rfl⟩
  · cases input with
    | none =>
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, Kernel.exec, advance_clock]
    | some x =>
      simp [ops, Entry.op?, Kernel.exec_cons, Kernel.apply, Kernel.exec, advance_clock,
        Kernel.accept]

/-- `turn` for inputs that arrived together: each is accepted, in order, and then up to `fuel`
units of work are done, the steps of different actors worked out as `spread` says
(`Kernel.runWaves`, which is `runBatch`). The journal has `advance`, the inputs and one `batch`. -/
def turnAll {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel : Nat) (spread : Kernel.Spread) : Turn sys :=
  if inputs.isEmpty && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match (k.acceptAll inputs).runWaves spread fuel with
    | { kernel, events, outputs } =>
      { kernel, events := inputs.map .input ++ events, outputs
        entries := .advance clock :: inputs.map .input ++ [.batch fuel] }

theorem turnAll_eq_exec {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel : Nat) (spread : Kernel.Spread) :
    (turnAll k now_ms inputs fuel spread).kernel
        = (k.exec (ops (turnAll k now_ms inputs fuel spread).entries)).kernel
      ∧ (turnAll k now_ms inputs fuel spread).events
          = (k.exec (ops (turnAll k now_ms inputs fuel spread).entries)).events
      ∧ (turnAll k now_ms inputs fuel spread).outputs
          = (k.exec (ops (turnAll k now_ms inputs fuel spread).entries)).outputs := by
  unfold turnAll
  split
  · exact ⟨rfl, rfl, rfl⟩
  · have hops : ∀ c : Nat, ops (.advance c :: inputs.map Entry.input ++ [.batch fuel])
        = .advance c :: (inputs.map Kernel.Op.input ++ [.batch fuel]) := by
      intro c
      simp [ops, Entry.op?, List.filterMap_append, List.filterMap_map, Function.comp_def]
    simp only [hops, Kernel.exec_cons, Kernel.exec_append, Kernel.exec_inputs, Kernel.runWaves_eq,
      Kernel.apply, advance_clock]
    simp [Kernel.exec]

/-- How a turn's waves are spread does not change the turn (`Kernel.runWaves_eq`). -/
theorem turnAll_spread {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel : Nat) (spread : Kernel.Spread) :
    turnAll k now_ms inputs fuel spread = turnAll k now_ms inputs fuel {} := by
  unfold turnAll
  simp only [Kernel.runWaves_eq]

/-- Turn after turn, with the entries each one journals. -/
def turns {sys : System σ} (k : Kernel sys) (fuel : Nat) :
    List (Nat × Option σ.In) → Kernel sys × List (Entry σ)
  | [] => (k, [])
  | (now_ms, input) :: rest =>
    match turn k now_ms input fuel with
    | { kernel, entries, .. } =>
      match turns kernel fuel rest with
      | (kernel, later) => (kernel, entries ++ later)

/-- However many turns a shard takes, at whatever times and with whatever inputs, its kernel is
the one its journal describes. So what `recover` rebuilds after the process dies is the kernel
the shard had when it last finished writing. -/
theorem turns_kernel {sys : System σ} (k : Kernel sys) (fuel : Nat)
    (steps : List (Nat × Option σ.In)) :
    (turns k fuel steps).1 = (k.exec (ops (turns k fuel steps).2)).kernel := by
  induction steps generalizing k with
  | nil => rfl
  | cons step steps ih =>
    obtain ⟨now_ms, input⟩ := step
    have hturn := (turn_eq_exec k now_ms input fuel).1
    show (turns (turn k now_ms input fuel).kernel fuel steps).1
      = (k.exec (ops ((turn k now_ms input fuel).entries
          ++ (turns (turn k now_ms input fuel).kernel fuel steps).2))).kernel
    simp only [ops] at hturn ih ⊢
    rw [ih, List.filterMap_append, Kernel.exec_append, ← hturn]

end Lanes.Journal
