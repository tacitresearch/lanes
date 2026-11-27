/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Disk

/-!
What a start reads of the two files, when reading may fail. A read gives the file's bytes, says
there is no such file, or fails (`EIO`, and every other error). A failure is not a file that is
not there: a start that took it for one would begin a new journal over the one it could not
read, and lose every entry it held. So a start whose read fails refuses (`Disk.ofReadings`),
and a start that goes on goes on with the files as they are (`Disk.ofReadings_eq`): whatever
the death of the process left, it loads as the kernel the shard had, or the start refuses
(`Disk.Torn.load_readings`), never anything else.

A slow write is not a new fault: the files are, at every moment of it, what dying then would
leave (`Disk.crash`), and the shell hands over nothing a turn produced before its append and
sync return (`Batch.run_sound`). What a slow sync costs is time; that other work waits for it is
the shell's, and is not proved.
-/

@[expose] public section

namespace Lanes.Journal

inductive Reading where
  | absent
  | bytes (b : ByteArray)
  | failed (error : String)

namespace Reading

/-- `r` is what reading the journal of `disk` may give: its bytes, no file only if it has none,
or a failure. -/
def OfJournal (disk : Disk) : Reading → Prop
  | .absent => disk.journal.size = 0
  | .bytes b => b = disk.journal
  | .failed _ => True

/-- And of its snapshot. -/
def OfSnapshot (disk : Disk) : Reading → Prop
  | .absent => disk.snapshot = none
  | .bytes b => disk.snapshot = some b
  | .failed _ => True

end Reading

namespace Disk

/-- The files as the readings show them, or the first failure. -/
def ofReadings (journal snapshot : Reading) : Except String Disk :=
  match journal, snapshot with
  | .failed e, _ | _, .failed e => .error e
  | j, s =>
    .ok { journal := match j with | .bytes b => b | _ => .empty
          snapshot := match s with | .bytes b => some b | _ => none }

theorem eq_empty_of_size {b : ByteArray} (h : b.size = 0) : b = .empty := by
  obtain ⟨data⟩ := b
  simp only [ByteArray.size] at h
  simp only [Array.eq_empty_of_size_eq_zero h]
  rfl

/-- Readings that do not fail show the files as they are. -/
theorem ofReadings_eq {disk d : Disk} {journal snapshot : Reading} (hj : journal.OfJournal disk)
    (hs : snapshot.OfSnapshot disk) (h : ofReadings journal snapshot = .ok d) : d = disk := by
  cases journal <;> cases snapshot <;>
    simp only [ofReadings, Except.ok.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [Reading.OfJournal, Reading.OfSnapshot] at hj hs <;>
    cases disk <;> simp_all [eq_empty_of_size]

variable {σ : Signature} {sys : System σ} [Hashable σ.Id] {input : Codec σ.In}
  {c : Kernel.Image.Codecs sys} {system : String} {start : Kernel sys × List σ.Out}
  {history : List (Entry σ)} {disk : Disk}

/-- Whatever the death of the process left, a start whose reads do not fail loads the kernel
the shard had, and one whose reads fail refuses: no committed entry is lost to a read error. -/
theorem Torn.load_readings (h : Torn sys (start := start) input c system history disk)
    {journal snapshot : Reading} (hj : journal.OfJournal disk) (hs : snapshot.OfSnapshot disk)
    {d : Disk} (hread : ofReadings journal snapshot = .ok d) :
    d.load sys input (some c) system = .ok (replay start history) := by
  rw [ofReadings_eq hj hs hread]
  exact h.load

end Disk

end Lanes.Journal
