/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.KernelSound
public import Lanes.Data.Codec
public import Lanes.Data.Frame

/-!
The journal of a shard: everything it asks of its kernel, in order. The kernel is a pure
function of those requests, so replaying a journal gives back the state it describes, and that
is how a shard survives its process (`DECISIONS.md` D24).

This file is the pure part: what an entry is, how a journal becomes the bytes of a file, that
reading the file back gives the entries, or the entries before a cut if the file was cut short,
and that `recover` rebuilds the kernel the entries describe.
-/

@[expose] public section

namespace Lanes.Journal

variable {σ : Signature}

inductive Entry (σ : Signature) where
  | input (x : σ.In)
  | advance (now_ms : Nat)
  | batch (fuel : Nat)
  /-- Every output produced so far has been handed over. After a restart, only the outputs
  after the last such mark are handed over again. -/
  | handed

namespace Entry

/-- Built from codecs that carry their laws, so this one does too. -/
def codec (input : Codec σ.In) : Codec (Entry σ) :=
  (Codec.sum input (Codec.sum Codec.nat (Codec.sum Codec.nat Codec.unit))).map
    (fun
      | .input x => .inl x
      | .advance now_ms => .inr (.inl now_ms)
      | .batch fuel => .inr (.inr (.inl fuel))
      | .handed => .inr (.inr (.inr ())))
    (fun
      | .inl x => some (.input x)
      | .inr (.inl now_ms) => some (.advance now_ms)
      | .inr (.inr (.inl fuel)) => some (.batch fuel)
      | .inr (.inr (.inr ())) => some .handed)
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

/-- A journal file: the entries, a frame each, end to end. -/
def encode (input : Codec σ.In) (entries : List (Entry σ)) : ByteArray :=
  Frame.encode (write input entries)

def decode (input : Codec σ.In) (file : ByteArray) : List (Entry σ) :=
  read input (Frame.decode file)

theorem encode_append (input : Codec σ.In) (a b : List (Entry σ)) :
    encode input (a ++ b) = encode input a ++ encode input b := by
  simp [encode, write, Frame.encode_append]

private theorem write_fits (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    ∀ p ∈ write input entries, p.size < 2 ^ 32 := by
  intro p hp
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hp
  have := h entry hentry
  simp only [Entry.fits, Bool.and_eq_true] at this
  exact Frame.fits_iff.mp this.2

theorem decode_encode (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) :
    decode input (encode input entries) = entries := by
  rw [decode, encode, Frame.decode_encode (write_fits input h), read_write input h]

/-- A journal file cut off at any byte, as when the process dies during a write, reads back as
the entries wholly written before the cut: never a wrong entry, never one out of order. -/
theorem decode_torn (input : Codec σ.In) {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, Entry.fits input entry = true) (n : Nat) :
    decode input ((encode input entries).extract 0 n) <+: entries :=
  read_prefix input h (Frame.decode_take (write_fits input h) n)

/-! Recovery: replay the entries through the kernel. -/

variable [Hashable σ.Id]

def Entry.op? : Entry σ → Option (Kernel.Op σ)
  | .input x => some (.input x)
  | .advance now_ms => some (.advance now_ms)
  | .batch fuel => some (.batch fuel)
  | .handed => none

def ops (entries : List (Entry σ)) : List (Kernel.Op σ) :=
  entries.filterMap Entry.op?

/-- One entry replayed: the kernel after it, and the outputs not yet known to be handed over. -/
def replay1 {sys : System σ} (acc : Kernel sys × List σ.Out) (entry : Entry σ) :
    Kernel sys × List σ.Out :=
  match acc, entry with
  | (k, _), .handed => (k, [])
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

theorem replay1_handed {sys : System σ} (k : Kernel sys) (pending : List σ.Out) :
    replay1 (k, pending) .handed = (k, []) := rfl

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
reported: the run before the crash, continued. -/
theorem recover_kernel (sys : System σ) (past : List (Entry σ)) :
    (recover sys past).1 = ((Kernel.boot sys).1.exec (ops past)).kernel :=
  (foldl_replay1 past (Kernel.boot sys).1 (Kernel.boot sys).2).1

/-- What is handed over again after a restart is the tail of what the run produced: nothing is
invented and nothing is out of order. -/
theorem recover_outputs (sys : System σ) (past : List (Entry σ)) :
    ∃ handed, (Kernel.boot sys).2 ++ ((Kernel.boot sys).1.exec (ops past)).outputs
      = handed ++ (recover sys past).2 :=
  (foldl_replay1 past (Kernel.boot sys).1 (Kernel.boot sys).2).2

end Lanes.Journal
