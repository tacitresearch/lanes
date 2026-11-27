/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.KernelSound
public import Lanes.Runtime.Wave
public import Lanes.Data.Codec
public import Lanes.Durable.Frame

/-!
The journal of a shard: everything it asks of its kernel, in order. The kernel is a pure
function of those requests, so replaying a journal gives back the state it describes, and that
is how a shard survives its process (`docs/decisions/` D24).

This file is the pure part: what an entry is, how a journal becomes the bytes of a file, which
files are opened and which refused (`open?`), that a file cut short by a crash opens and gives
the entries before the cut, and that `recover` rebuilds the kernel the entries describe.
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
units of work are done, the steps of different actors worked out on `workers` threads
(`Kernel.runWaves`, which is `runBatch`). The journal has `advance`, the inputs and one `batch`. -/
def turnAll {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel workers : Nat) : Turn sys :=
  if inputs.isEmpty && (k.advance now_ms).wait != .none then { kernel := k }
  else
    let k := k.advance now_ms
    let clock := k.clock_ms
    match (k.acceptAll inputs).runWaves workers fuel with
    | { kernel, events, outputs } =>
      { kernel, events := inputs.map .input ++ events, outputs
        entries := .advance clock :: inputs.map .input ++ [.batch fuel] }

theorem turnAll_eq_exec {sys : System σ} (k : Kernel sys) (now_ms : Nat) (inputs : List σ.In)
    (fuel workers : Nat) :
    (turnAll k now_ms inputs fuel workers).kernel
        = (k.exec (ops (turnAll k now_ms inputs fuel workers).entries)).kernel
      ∧ (turnAll k now_ms inputs fuel workers).events
          = (k.exec (ops (turnAll k now_ms inputs fuel workers).entries)).events
      ∧ (turnAll k now_ms inputs fuel workers).outputs
          = (k.exec (ops (turnAll k now_ms inputs fuel workers).entries)).outputs := by
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
