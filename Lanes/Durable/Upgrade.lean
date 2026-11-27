/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Disk
public import Lanes.Durable.Migration

/-!
A start that finds the files of an older version of the system. It loads them as that version
did, through its own codecs and step functions, so the kernel is the one the old shard had
(`Disk.Torn.load`). It migrates that kernel (`Lanes.Migration`), saves it under the new name as a
snapshot whose mark carries the old history's length, and replaces the journal by one that
starts at that mark. Nothing is replayed through the new step functions.

`Upgrade.begin_crash`: wherever the process dies during those two writes, the next start gives
the same migrated kernel. `Upgrade.holds`: once they are done, the files are those of a running
shard (`Disk.Holds`) whose history starts from the migrated kernel, so every theorem about
turns, saves and deaths goes on from there, and `Upgrade.inv_load` says what the migration's
proof gives at every later start.
-/

@[expose] public section

namespace Lanes.Journal

open Kernel (Image)

variable {σ : Signature}

/-- How to read the files of an older version: that version's system, the label its files
carry, its codecs, and the migration from it. -/
structure Upgrade (sys : System σ) where
  {σ₀ : Signature}
  old : System σ₀
  [hashable : Hashable σ₀.Id]
  /-- The label of the old version's files (`Journal.label`). -/
  system : String
  input : Codec σ₀.In
  actors : Option (Image.Codecs old) := none
  migration : Migration old sys

attribute [instance] Upgrade.hashable

/-- What a start that migrates goes on with, and what it writes. -/
structure Upgraded (sys : System σ) where
  /-- The length of the old history, which is the place of the new journal's first mark. -/
  index : Nat
  /-- The migrated kernel, as the new snapshot holds it. -/
  image : Image sys
  /-- The old outputs not yet handed over, migrated. They are handed over before the writes. -/
  pending : List σ.Out
  writes : List Write

/-- What a start found. -/
inductive Begun (sys : System σ) where
  | found (found : Disk.Found sys)
  | upgraded (upgraded : Upgraded sys)

namespace Upgrade

variable {sys : System σ}

/-- Whether this upgrade reads a journal whose first frame is `first`. -/
def reads (u : Upgrade sys) (first : ByteArray) : Bool :=
  first == header u.system

/-- Save the migrated kernel under the new name, then begin the journal at its mark. -/
def writes (input : Codec σ.In) (c : Image.Codecs sys) (system : String) (index : Nat)
    (image : Image sys) : List Write :=
  [.putSnapshot (saved c system index image), .putJournal (file input system [.snapshot index])]

variable [Hashable σ.Id]

def upgraded (u : Upgrade sys) (input : Codec σ.In) (c : Image.Codecs sys) (system : String)
    (index : Nat) (old : Kernel u.old × List u.σ₀.Out) : Upgraded sys :=
  let image := (u.migration.kernel old.1).image
  { index, image, pending := old.2.map u.migration.output
    writes := writes input c system index image }

/-- Files of the old version give the old kernel, migrated. A snapshot already under the new
name is a migration whose journal was not yet replaced: it is finished. -/
def start (u : Upgrade sys) (input : Codec σ.In) (c : Image.Codecs sys) (system : String)
    (disk : Disk) : Except Refusal (Upgraded sys) :=
  match disk.snapshot.bind (saved? c system) with
  | some (index, image) =>
    .ok { index, image, pending := [], writes := [.putJournal (file input system [.snapshot index])] }
  | none =>
    match disk.read u.input u.actors u.system with
    | .error refusal => .error refusal
    | .ok found =>
      match resume u.old found.saved found.past with
      | some old => .ok (u.upgraded input c system found.index old)
      | none => .error .apart

end Upgrade

namespace Disk

variable {sys : System σ}

/-- A start: the files of this version as `start` reads them or, when the journal is another
system's, the first upgrade that reads it. An upgrade needs the codecs of the actors, since it
saves. -/
def begin (input : Codec σ.In) (actors : Option (Image.Codecs sys)) (system : String)
    (create : Bool) (upgrades : List (Upgrade sys)) [Hashable σ.Id] (disk : Disk) :
    Except Refusal (Begun sys) :=
  match disk.start input actors system create with
  | .error (.foreign named) =>
    match actors, (Frame.decode disk.journal).head?.bind fun first => upgrades.find? (·.reads first) with
    | some c, some u => (u.start input c system disk).map .upgraded
    | _, _ => .error (.foreign named)
  | result => result.map .found

end Disk

namespace Begun

variable {sys : System σ} [Hashable σ.Id]

/-- The kernel a start goes on with, and the outputs it hands over. -/
def load : Begun sys → Except Refusal (Kernel sys × List σ.Out)
  | .found f =>
    match resume sys f.saved f.past with
    | some start => .ok start
    | none => .error .apart
  | .upgraded up => .ok (up.image.kernel, up.pending)

/-- What the shell is given: a migrated start is a journal of one mark and its snapshot. -/
def toFound : Begun sys → Disk.Found sys
  | .found f => f
  | .upgraded up =>
    { past := [.snapshot up.index], saved := some (up.index, up.image), size := 0 }

/-- The shell resumes from what it is given and hands over the pending outputs first, which is
what `load` says. -/
theorem resume_upgraded (up : Upgraded sys) :
    resume sys (Begun.upgraded up).toFound.saved (Begun.upgraded up).toFound.past
      = some (up.image.kernel, []) := by
  simp [toFound, resume, since, Entry.savedAt]

end Begun

/-! The theorems. The old shard's files are what its death may leave (`Disk.Torn`) of a history
that started at boot, and its journal has at least its header. -/

theorem Entry.fits_handed (input : Codec σ.In) : Entry.fits input .handed = true := by
  have h0 := Char.utf8Size_le_four (Nat.digitChar 0)
  have h1 := Char.utf8Size_le_four (Nat.digitChar 1)
  have r0 : (Nat.repr 0).utf8ByteSize = (Nat.digitChar 0).utf8Size := by
    rw [Nat.repr_of_lt (by decide), String.utf8ByteSize_singleton]
  have r1 : (Nat.repr 1).utf8ByteSize = (Nat.digitChar 1).utf8Size := by
    rw [Nat.repr_of_lt (by decide), String.utf8ByteSize_singleton]
  simp only [Entry.fits, Entry.bytes, Entry.codec, Codec.map, Codec.sum, Codec.unit, Codec.nat,
    Frame.fits, Frame.encode, Frame.one, toString, String.toUTF8_eq_toByteArray]
  simp [String.size_toByteArray, Frame.fits, r0, r1]
  omega

namespace Disk

variable {sys : System σ} {input : Codec σ.In} {actors : Option (Image.Codecs sys)}
  {system : String} {disk : Disk} {found : Found sys}

theorem open?_of_read (h : disk.read input actors system = .ok found) :
    open? input system disk.journal = .ok (found.past, found.size) := by
  unfold read at h
  split at h
  · split at h
    · cases h
    · next past size hopen =>
      split at h
      · split at h
        · cases h
          exact hopen
        · cases h
      · cases h
        exact hopen
  · cases h

/-- A journal whose header names another system is refused as that system's, whatever its
snapshot. -/
theorem start_foreign {named : String} {payloads : List ByteArray} (create : Bool)
    (hheader : Frame.fits (header system) = true) (hne : named ≠ system)
    (hdecode : Frame.decode disk.journal = header named :: payloads) :
    disk.start input actors system create = .error (.foreign (named? (header named))) := by
  have hdiff : header named ≠ header system := fun h => hne (header_inj h)
  simp [start, read, hheader, open?, hdecode, hdiff]

end Disk

namespace Upgrade

variable {sys : System σ} [Hashable σ.Id] {input : Codec σ.In} {c : Image.Codecs sys}
  {system : String} {create : Bool} {upgrades : List (Upgrade sys)} {u : Upgrade sys}
  {c₀ : Image.Codecs u.old} {history : List (Entry u.σ₀)} {disk : Disk}

/-- The files of the old version give the kernel the old shard had, migrated, and the outputs it
had not handed over, migrated. -/
theorem start_torn (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hactors : u.actors = some c₀) (hne : u.system ≠ system) :
    u.start input c system disk
      = .ok (u.upgraded input c system history.length (recover u.old history)) := by
  obtain ⟨found, hread, hindex⟩ := hold.read
  have hload := hold.load
  rw [Disk.load, hread] at hload
  have hresume : resume u.old found.saved found.past = some (recover u.old history) := by
    cases hres : resume u.old found.saved found.past with
    | none => simp [hres] at hload
    | some s =>
      simp only [hres, Except.ok.injEq] at hload
      rw [hload]
      rfl
  have hnone : disk.snapshot.bind (saved? c system) = none := by
    obtain ⟨lost, mark, more, n, hkept, -, -, -, hsnapshot⟩ := hold
    rw [hsnapshot]
    cases mark with
    | none => rfl
    | some index =>
      simp only [memo, Option.map_some, Option.bind_some]
      exact saved?_other c₀ c hne index _ (hkept.marked index rfl).2.2
  simp only [start, hnone, hactors, hread, hresume, hindex]

omit [Hashable σ.Id] in
/-- The first frame of a journal the old shard began. -/
theorem decode_torn (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hstarted : Frame.decode disk.journal ≠ []) :
    ∃ payloads, Frame.decode disk.journal = header u.system :: payloads := by
  obtain ⟨found, hread, -⟩ := hold.read
  have hopen := Disk.open?_of_read hread
  unfold open? at hopen
  split at hopen
  · next hnil => exact absurd hnil hstarted
  · next first payloads hcons =>
    by_cases hfirst : first = header u.system
    · exact ⟨payloads, hfirst ▸ hcons⟩
    · simp [hfirst] at hopen

/-- A start on the old version's files migrates them. -/
theorem begin_torn (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hactors : u.actors = some c₀) (hne : u.system ≠ system)
    (hheader : Frame.fits (header system) = true) (hstarted : Frame.decode disk.journal ≠ [])
    (hfind : upgrades.find? (·.reads (header u.system)) = some u) :
    Disk.begin input (some c) system create upgrades disk
      = .ok (.upgraded (u.upgraded input c system history.length (recover u.old history))) := by
  obtain ⟨payloads, hdecode⟩ := decode_torn hold hstarted
  simp only [Disk.begin, Disk.start_foreign create hheader hne hdecode, hdecode, List.head?_cons,
    Option.bind_some, hfind, start_torn hold hactors hne, Except.map]

/-- Wherever the process dies during the two writes of a migration, the next start gives the
same migrated kernel: before the first, by migrating again, and the outputs to hand over with
it; after it, from the snapshot under the new name, with nothing to hand over, since those
outputs were handed over before the first write. Never a refusal. -/
theorem begin_crash (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hactors : u.actors = some c₀) (hne : u.system ≠ system)
    (hheader : Frame.fits (header system) = true) (hstarted : Frame.decode disk.journal ≠ [])
    (hfind : upgrades.find? (·.reads (header u.system)) = some u)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : (savedRecords c system history.length
      (u.migration.kernel (recover u.old history).1).image).all Frame.fits = true)
    (done part : Nat) :
    (Disk.begin input (some c) system create upgrades
        (disk.crash (u.upgraded input c system history.length (recover u.old history)).writes
          done part)).bind Begun.load
      = .ok ((u.migration.kernel (recover u.old history).1).image.kernel,
          if done = 0 then (recover u.old history).2.map u.migration.output else []) := by
  obtain ⟨payloads, hdecode⟩ := decode_torn hold hstarted
  match done with
  | 0 =>
    show (Disk.begin input (some c) system create upgrades disk).bind Begun.load = _
    rw [begin_torn hold hactors hne hheader hstarted hfind]
    rfl
  | 1 =>
    have hstart := Disk.start_foreign (input := input) (actors := some c)
      (disk := { disk with snapshot := some (saved c system history.length
        (u.migration.kernel (recover u.old history).1).image) }) create hheader hne hdecode
    simp only [upgraded, writes, Disk.crash, Disk.apply] at hstart ⊢
    simp [Disk.begin, hstart, hdecode, hfind, start, saved?_saved c system _ _ hsaved, Except.map]
    rfl
  | done + 2 =>
    rw [Disk.crash_of_length_le _ (by simp [upgraded, writes])]
    have hopen := open?_file input (entries := [Entry.snapshot history.length]) hheader
      (by simpa using hmark)
    have hsize : (file input system [Entry.snapshot history.length]).size ≠ 0 := by
      simp [file, Frame.size_encode, Frame.span]
    simp [upgraded, writes, Disk.apply, Disk.begin, Disk.start, Disk.read, hheader, hopen,
      saved?_saved c system _ _ hsaved, hsize, Except.map]
    simp [Except.bind, Begun.load, resume, since, Entry.savedAt]

/-- The history of a shard that started from a migrated kernel, up to its first mark: as many
entries that change nothing as the old history had, so that the mark carries its place in the
old history and no request id the old shard gave is given again (D29). -/
def past (index : Nat) : List (Entry σ) :=
  List.replicate index .handed ++ [.snapshot index]

omit [Hashable σ.Id] in
private theorem replay_handed {sys : System σ} [Hashable σ.Id] (k : Kernel sys) (n : Nat) :
    replay (k, []) (List.replicate n (Entry.handed : Entry σ)) = (k, []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact ih

omit [Hashable σ.Id] in
private theorem placed_past {index i j : Nat}
    (h : (past index : List (Entry σ))[i]? = some (.snapshot j)) : j = i := by
  simp only [past, List.getElem?_append, List.length_replicate] at h
  split at h
  · simp [List.getElem?_replicate] at h
  · next hi =>
    have hzero : i - index = 0 := by
      cases hk : i - index with
      | zero => rfl
      | succ k => simp [hk] at h
    simp [hzero] at h
    omega

/-- Once the two writes are done, the files are those of a running shard whose history starts
from the migrated kernel. So the theorems of `Disk.Holds` and `Disk.Torn` go on from here:
whatever turns and saves it does, and wherever it dies, it loads as the kernel its history
leads to from the migrated one. -/
theorem holds (k : Kernel sys) (index : Nat) (hheader : Frame.fits (header system) = true)
    (hmark : Entry.fits input (.snapshot index) = true)
    (hsaved : (savedRecords c system index k.image).all Frame.fits = true) (disk : Disk) :
    Disk.Holds sys (start := (k, [])) input c system (past index)
      ((writes input c system index k.image).foldl Disk.apply disk) := by
  have htake : (past index : List (Entry σ)).take index = List.replicate index .handed := by
    simp [past]
  have hdrop : (past index : List (Entry σ)).drop index = [.snapshot index] := by
    simp [past]
  refine ⟨index, some index, ?_, ?_, ?_⟩
  · exact {
      header := hheader
      entries := by
        intro e he
        simp only [past, List.mem_append, List.mem_replicate, List.mem_singleton] at he
        rcases he with ⟨-, rfl⟩ | rfl
        · exact Entry.fits_handed input
        · exact hmark
      placed := fun _ _ h => placed_past h
      cut := .inr (by simp [past])
      marked := by
        rintro _ ⟨rfl⟩
        exact ⟨by simp [past], Nat.le_refl _, by rw [htake, replay_handed]; exact hsaved⟩
      saved := nofun }
  · simp [writes, Disk.apply, hdrop]
  · simp [writes, Disk.apply, memo, htake, replay_handed]

/-- What the migration's proof gives at every later start. The files are what the death of the
process may leave of a shard that started from the migrated kernel, after any history: they
load, and every actor of the kernel they load as satisfies the migration's invariant. -/
theorem inv_load {later : List (Entry σ)} {disk' : Disk}
    (h : Disk.Torn sys (start := (u.migration.kernel (recover u.old history).1, [])) input c
      system later disk') :
    ∃ k outputs, disk'.load sys input (some c) system = .ok (k, outputs)
      ∧ ∀ j, u.migration.inv j (k.cell j).state := by
  refine ⟨_, _, h.load, fun j => ?_⟩
  have hkernel := replay_kernel (u.migration.kernel (recover u.old history).1, []) later
  simp only [replay] at hkernel
  rw [hkernel]
  refine Kernel.exec_inductive _ _ u.migration.keeps (fun j => ?_) j
  rw [recover_kernel]
  exact u.migration.inv_migrated _ j

end Upgrade

end Lanes.Journal
