/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.FileSystem.Basic
public import Lanes.Proof.List.Basic

/-!
# A log a crash may cut, and never scrambles

A file only appended to, and synced from time to time, as a journal, a write-ahead log or Raft's
log is kept. Proved, for a file whose entry is in a directory with nothing a crash could lose
(`SettledDir`): after a crash at any point, the file reads as a prefix of everything appended,
and holds at least everything appended before the last `fsync` (`Log.crash`); with no crash it
reads as everything appended (`Log.read`). The bytes of the last entry may be torn, so a reader
must tell a whole entry from a torn one, by a length and a checksum.

An `io` error is a crash the program sees: after an append or an `fsync` that failed, the file
is as a crash may leave it, and stays so through a crash, but an append after it would follow a
torn entry, or an `fsync` that lost its pages, so the program must stop appending (`Log.failed`).
-/

@[expose] public section

namespace Lanes.FileSystem

namespace Log

inductive Step where
  | append (bytes : Bytes)
  | sync
  deriving DecidableEq, Repr, Hashable

def Step.op (p : Path) : Step → Op
  | .append bytes => .append p bytes
  | .sync => .fsync p

/-- Everything appended, and what was appended before the last `sync`. -/
def written (steps : List Step) : Bytes × Bytes :=
  steps.foldl (fun (all, synced) step => match step with
    | .append bytes => (all ++ bytes, synced)
    | .sync => (all, all)) ([], [])

/-- What a step does to the file. -/
def apply (f : File) : Step → File
  | .append bytes => f.change (.write f.data.length bytes)
  | .sync => f.sync

/-- Writes at the end of a file of `size` bytes, one for each chunk. -/
def writes (size : Nat) : List Bytes → List Change
  | [] => []
  | b :: bs => .write size b :: writes (size + b.length) bs

theorem applyAll_writes (S : Bytes) (bs : List Bytes) :
    applyAll (writes S.length bs) S = S ++ bs.flatten := by
  induction bs generalizing S with
  | nil => simp [writes, applyAll]
  | cons b bs ih =>
    have h := ih (S ++ b)
    have hd : S.drop (S.length + b.length) = [] := List.drop_eq_nil_of_le (by omega)
    simp only [List.length_append] at h
    simp [writes, applyAll, Change.apply, zeros, hd] at h ⊢
    exact h

theorem writes_concat (n : Nat) (bs : List Bytes) (b : Bytes) :
    writes n (bs ++ [b]) = writes n bs ++ [.write (n + bs.flatten.length) b] := by
  induction bs generalizing n with
  | nil => simp [writes]
  | cons c bs ih => simp [writes, ih, Nat.add_assoc]

theorem survive_cons_succ (S : Bytes) (c : Change) (cs : List Change) (kept part : Nat) :
    ({ synced := S, pending := c :: cs } : File).survive (kept + 1) part =
      ({ synced := c.apply S, pending := cs } : File).survive kept part := by
  simp [File.survive, applyAll]

/-- A crash keeps a prefix of the chunks not yet synced. -/
theorem survive_writes (S : Bytes) (bs : List Bytes) (kept part : Nat) :
    ∃ X, ({ synced := S, pending := writes S.length bs } : File).survive kept part = S ++ X ∧
      X <+: bs.flatten := by
  induction bs generalizing S kept with
  | nil => exact ⟨[], by simp [File.survive, writes, applyAll], List.nil_prefix⟩
  | cons b bs ih =>
    cases kept with
    | zero =>
      refine ⟨b.take part, ?_, (List.take_prefix _ _).trans (List.prefix_append _ _)⟩
      simp [File.survive, writes, applyAll, Change.torn, Change.apply, zeros]
    | succ kept =>
      obtain ⟨X, hX, hpre⟩ := ih (S ++ b) kept
      refine ⟨b ++ X, ?_, by simpa using hpre⟩
      have hd : S.drop (S.length + b.length) = [] := List.drop_eq_nil_of_le (by omega)
      simp only [writes, survive_cons_succ]
      simp only [List.length_append] at hX
      simpa [Change.apply, zeros, hd] using hX

/-- The file after each step: what is synced is the original and everything appended before
the last `sync`, and the rest is written at its end, chunk by chunk. -/
theorem shape (F : File) (hF : F.pending = []) (steps : List Step) :
    ∃ bs, (steps.foldl apply F).synced = F.synced ++ (written steps).2 ∧
      (steps.foldl apply F).pending = writes (steps.foldl apply F).synced.length bs ∧
      (written steps).2 ++ bs.flatten = (written steps).1 := by
  induction steps using reverse_induction with
  | nil => exact ⟨[], by simp [written], by simp [hF, writes], by simp [written]⟩
  | append_singleton steps step ih =>
    obtain ⟨bs, hs, hp, hw⟩ := ih
    have hdata : (steps.foldl apply F).data = (steps.foldl apply F).synced ++ bs.flatten := by
      rw [File.data, hp, applyAll_writes]
    cases step with
    | append b =>
      refine ⟨bs ++ [b], ?_, ?_, ?_⟩
      · simpa [apply, File.change, written, List.foldl_append] using hs
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, apply, File.change, hp,
          hdata, List.length_append, writes_concat]
      · simp only [written, List.foldl_append, List.foldl_cons, List.foldl_nil] at hw ⊢
        simp [← hw]
    | sync =>
      refine ⟨[], ?_, by simp [apply, File.sync, writes], by simp [written, List.foldl_append]⟩
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, apply, File.sync, hdata, hs]
      simp only [written] at hw ⊢
      simp [List.foldl_append, ← hw]

theorem data_foldl (F : File) (hF : F.pending = []) (steps : List Step) :
    (steps.foldl apply F).data = F.synced ++ (written steps).1 := by
  obtain ⟨bs, hs, hp, hw⟩ := shape F hF steps
  rw [File.data, hp, applyAll_writes, hs, List.append_assoc, hw]

/-- Through a crash, the file is a prefix of everything appended, and holds what was synced. -/
theorem survive_foldl (F : File) (hF : F.pending = []) (steps : List Step) (kept part : Nat) :
    F.synced ++ (written steps).2 <+: (steps.foldl apply F).survive kept part ∧
      (steps.foldl apply F).survive kept part <+: F.synced ++ (written steps).1 := by
  obtain ⟨bs, hs, hp, hw⟩ := shape F hF steps
  have hf : steps.foldl apply F =
      ⟨F.synced ++ (written steps).2, writes (F.synced ++ (written steps).2).length bs⟩ := by
    rw [← hs, ← hp]
  obtain ⟨X, hX, hpre⟩ := survive_writes (F.synced ++ (written steps).2) bs kept part
  rw [hf, hX]
  refine ⟨List.prefix_append _ _, ?_⟩
  rw [← hw, ← List.append_assoc]
  exact (List.prefix_append_right_inj _).mpr hpre

/-! The steps through the file system. -/

variable {s : Fs} {dir : Path} {d : Nat} {D : Dir} {name : String} {i : Nat}

/-- Where the log is: a file named `name` in a settled directory, with nothing a crash could
lose. -/
structure Ready (s : Fs) (dir : Path) (d : Nat) (D : Dir) (name : String) (i : Nat) (F : File) :
    Prop where
  settled : s.SettledDir dir d D
  entry : D.synced.lookup name = some i
  file : s.node i = some (.file F)
  synced : F.pending = []

variable {F : File}

theorem Ready.ne (h : Ready s dir d D name i F) : i ≠ d := fun heq => by
  have := h.file
  rw [heq, h.settled.node] at this
  cases this

theorem Ready.not_way (h : Ready s dir d D name i F) : i ∉ s.way 0 dir := fun hi => by
  obtain ⟨E, hE, -⟩ := h.settled.way i hi
  rw [h.file] at hE
  cases hE

/-- A file system the steps may have made: the log's inode is `f`, every other is as it was. -/
theorem fileAt_of (h : Ready s dir d D name i F) {s' : Fs} {f : File}
    (hs : ∀ j, j ≠ i → s'.node j = s.node j) (hi : s'.node i = some (.file f)) :
    s'.fileAt (dir ++ [name]) = .ok (i, f) := by
  have hr := h.settled.resolve_of_same fun j hj => hs j fun heq => h.not_way (heq ▸ hj)
  have hd : s'.node d = some (.dir D) := by rw [hs d (Ne.symm h.ne)]; exact h.settled.node
  simp [Fs.fileAt, Fs.find_in hr hd, Dir.entries_of_synced h.settled.synced, h.entry, hi]

theorem run_steps (h : Ready s dir d D name i F) (steps : List Step) {s' : Fs} {f : File}
    (hs : ∀ j, j ≠ i → s'.node j = s.node j) (hi : s'.node i = some (.file f)) :
    (∀ j, j ≠ i → (s'.run (steps.map (·.op (dir ++ [name])))).node j = s.node j) ∧
      (s'.run (steps.map (·.op (dir ++ [name])))).node i = some (.file (steps.foldl apply f)) := by
  induction steps generalizing s' f with
  | nil => exact ⟨hs, hi⟩
  | cons step rest ih =>
    have hat := fileAt_of h hs hi
    have hstep : (s'.step (step.op (dir ++ [name]))).1 = s'.set i (.file (apply f step)) := by
      cases step with
      | append b =>
        simp [Fs.step, Fs.apply, Step.op, Fs.changeFile, hat, bind, Except.bind, pure,
          Except.pure, apply]
      | sync =>
        have hfind : s'.find (dir ++ [name]) = some (i, .file f) := by
          simp only [Fs.fileAt] at hat
          split at hat <;> simp_all
        simp [Fs.step, Fs.apply, Step.op, Fs.sync, hfind, Node.sync, apply]
    simp only [List.map_cons, Fs.run, List.foldl_cons] at ih ⊢
    rw [hstep]
    exact ih (fun j hj => by rw [Fs.node_set_ne _ _ hj]; exact hs j hj) (by simp)

/-- With no crash, the log reads as everything appended. -/
theorem read (h : Ready s dir d D name i F) (steps : List Step) :
    (s.run (steps.map (·.op (dir ++ [name])))).read (dir ++ [name]) =
      some (F.synced ++ (written steps).1) := by
  obtain ⟨hs, hi⟩ := run_steps h steps (fun _ _ => rfl) h.file
  simp [Fs.read, fileAt_of h hs hi, data_foldl F h.synced]

/-- What a crash leaves of a file system the steps may have made. -/
theorem read_crash_of (h : Ready s dir d D name i F) {s' : Fs} {f : File}
    (hs : ∀ j, j ≠ i → s'.node j = s.node j) (hi : s'.node i = some (.file f))
    (c : Nat → Nat × Nat) :
    (s'.crash c).read (dir ++ [name]) = some (f.survive (c i).1 (c i).2) := by
  have hd : s'.node d = some (.dir D) := by rw [hs d (Ne.symm h.ne)]; exact h.settled.node
  rw [Fs.read_crash_child (h.settled.resolve_crash
      (fun j hj => hs j fun heq => h.not_way (heq ▸ hj)) c) hd,
    Dir.survive_of_synced h.settled.synced, h.entry]
  simp [hi, Node.crash, Fs.fileData, File.data, applyAll]

/-- After a crash at any point, the log reads as a prefix of everything appended, and holds
everything appended before the last `fsync`. -/
theorem crash (h : Ready s dir d D name i F) (steps : List Step) (c : Nat → Nat × Nat) :
    ∃ r, ((s.run (steps.map (·.op (dir ++ [name])))).crash c).read (dir ++ [name]) = some r ∧
      F.synced ++ (written steps).2 <+: r ∧ r <+: F.synced ++ (written steps).1 := by
  obtain ⟨hs, hi⟩ := run_steps h steps (fun _ _ => rfl) h.file
  exact ⟨_, read_crash_of h hs hi c, survive_foldl F h.synced steps _ _⟩

/-- An `io` error from the next step leaves the log, now and through a crash, as a crash after
that step may: so a program that stops there loses nothing it synced. -/
theorem failed (h : Ready s dir d D name i F) (steps : List Step) (step : Step) {s' : Fs}
    (hs' : s' ∈ (s.run (steps.map (·.op (dir ++ [name])))).failures (step.op (dir ++ [name])))
    (c : Nat → Nat × Nat) :
    ∃ r, (s'.crash c).read (dir ++ [name]) = some r ∧
      F.synced ++ (written steps).2 <+: r ∧ r <+: F.synced ++ (written (steps ++ [step])).1 := by
  obtain ⟨hs, hi⟩ := run_steps h steps (fun _ _ => rfl) h.file
  generalize s.run (steps.map (·.op (dir ++ [name]))) = s₁ at hs hi hs'
  have hat := fileAt_of h hs hi
  have grow : F.synced ++ (written steps).1 <+: F.synced ++ (written (steps ++ [step])).1 := by
    cases step <;> simp [written, List.foldl_append]
  have hbase := survive_foldl F h.synced steps
  have hset : ∀ f, ∀ j, j ≠ i → (s₁.set i (.file f)).node j = s.node j := fun f j hj => by
    rw [Fs.node_set_ne _ _ hj]; exact hs j hj
  cases step with
  | append b =>
    simp only [Step.op, Fs.failures, hat, List.mem_cons, List.mem_map, List.mem_range] at hs'
    rcases hs' with rfl | ⟨part, -, rfl⟩
    · exact ⟨_, read_crash_of h hs hi c, (hbase _ _).1, (hbase _ _).2.trans grow⟩
    · have hshape := survive_foldl F h.synced (steps ++ [.append (b.take part)]) (c i).1 (c i).2
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hshape
      refine ⟨_, read_crash_of h (hset _) (Fs.node_set_self _ _ _) c, ?_, ?_⟩
      · simpa [written, List.foldl_append, apply] using hshape.1
      · refine (by simpa [written, List.foldl_append, apply] using hshape.2 :
          _ <+: F.synced ++ ((written steps).1 ++ b.take part)).trans ?_
        simpa [written, List.foldl_append] using List.take_prefix _ _
  | sync =>
    have hfind : s₁.find (dir ++ [name]) = some (i, .file (steps.foldl apply F)) := by
      simp only [Fs.fileAt] at hat
      split at hat <;> simp_all
    simp only [Step.op, Fs.failures, hfind, List.mem_cons, List.mem_map] at hs'
    rcases hs' with rfl | ⟨⟨kept, part⟩, -, rfl⟩
    · exact ⟨_, read_crash_of h hs hi c, (hbase _ _).1, (hbase _ _).2.trans grow⟩
    · refine ⟨_, read_crash_of h (hset _) (Fs.node_set_self _ _ _) c, ?_⟩
      have := hbase kept part
      simpa [File.survive, applyAll] using ⟨this.1, this.2.trans grow⟩

end Log

end Lanes.FileSystem
