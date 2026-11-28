/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Disk
public import Lanes.Durable.Migration
public import Lanes.Durable.OutputId

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

/-- Whether this upgrade reads a journal whose manifest names `named`. -/
def reads (u : Upgrade sys) (named : String) : Bool :=
  u.system == named

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
    match actors, named.bind fun named => upgrades.find? (·.reads named) with
    | some c, some u => (u.start input c system disk).map .upgraded
    | _, _ => .error (.foreign named)
  | result => result.map .found

end Disk

namespace Upgrade

variable {sys : System σ}

/-- The origins, in the older history, of the outputs an older version's files owe: those that
`start` migrates into `Upgraded.pending`, in order (`Journal.resumeIds`). The old history keeps
its places, so an output it owed keeps its id across the migration. -/
def owed (upgrades : List (Upgrade sys)) (disk : Disk) : List Origin :=
  match (named? disk.journal).bind fun named => upgrades.find? (·.reads named) with
  | none => []
  | some u =>
    match disk.read u.input u.actors u.system with
    | .error _ => []
    | .ok found =>
      match resumeIds u.old found.saved found.past with
      | some (_, _, pending) => pending.map Prod.fst
      | none => []

/-- The migrated outputs with their origins. Should the two lists not match, which `owed` rules
out, each output takes the place of the new journal's mark. -/
def label {α : Type} (index : Nat) (origins : List Origin) (pending : List α) : List (Origin × α) :=
  if origins.length = pending.length then origins.zip pending else tag (index + 1) pending

/-- Labelling hands over every migrated output, in order. -/
theorem label_snd {α : Type} (index : Nat) (origins : List Origin) (pending : List α) :
    (label index origins pending).map Prod.snd = pending := by
  unfold label
  split
  · next h => exact List.map_snd_zip (by omega)
  · exact tag_snd _ _ _

end Upgrade

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
that started at boot, and its journal has at least its prelude. -/

theorem Entry.fits_handed (input : Codec σ.In) : Entry.fits input .handed = true := by
  simp [Entry.fits, Entry.write, Body.encode, Entry.schema, Schema.Of.map, Schema.Of.variants,
    Schema.Ctors.cons, Schema.Fields.cons, Schema.Fields.nil, Body.write, Body.writeAt,
    Body.writeNum, Body.writeFields, Body.natBytes, Body.writeNat, Frame.fits, Kind.limits,
    Body.within]

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

/-- A journal whose manifest names another system is refused as that system's, whatever its
snapshot. -/
theorem start_foreign {named : String} {s : Schema} {payloads : List ByteArray} (create : Bool)
    (hheader : preludeFits input system = true) (hne : named ≠ system)
    (hold : Prelude.fits .journal named s = true)
    (hdecode : Frame.decode disk.journal = Prelude.frames .journal named s ++ payloads) :
    disk.start input actors system create = .error (.foreign (some named)) := by
  simp [start, read, hheader, open?, hdecode, Prelude.frames, Prelude.check_other hold hne]

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
/-- The prelude of a journal the old shard began, once it is whole. -/
theorem decode_torn (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hstarted : 3 ≤ (Frame.decode disk.journal).length) :
    ∃ payloads, Frame.decode disk.journal = prelude u.input u.system ++ payloads := by
  obtain ⟨lost, mark, more, n, hkept, hmore, -, hjournal, -⟩ := hold
  have hfits : ∀ entry ∈ history.drop lost ++ more, Entry.fits u.input entry = true :=
    fun entry hentry => (List.mem_append.mp hentry).elim
      (fun hk => hkept.entries entry (List.mem_of_mem_drop hk)) (hmore entry)
  rw [hjournal, file, Frame.decode_take_eq (frames_fit u.input hkept.prelude hfits)] at hstarted ⊢
  generalize Frame.whole (frames u.input u.system (history.drop lost ++ more)) n = w at hstarted ⊢
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 3 := ⟨w - 3, by simp [frames, prelude, Prelude.frames] at hstarted; omega⟩
  exact ⟨(write u.input (history.drop lost ++ more)).take k, by simp [frames, prelude, Prelude.frames]⟩

/-- A start on the old version's files migrates them. -/
theorem begin_torn (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hactors : u.actors = some c₀) (hne : u.system ≠ system)
    (hheader : preludeFits input system = true) (hstarted : 3 ≤ (Frame.decode disk.journal).length)
    (hfind : upgrades.find? (·.reads u.system) = some u) :
    Disk.begin input (some c) system create upgrades disk
      = .ok (.upgraded (u.upgraded input c system history.length (recover u.old history))) := by
  obtain ⟨payloads, hdecode⟩ := decode_torn hold hstarted
  have hfit : Prelude.fits .journal u.system (Entry.own u.input) = true := by
    obtain ⟨_, _, _, _, hkept, -⟩ := hold
    exact hkept.prelude
  simp only [Disk.begin, Disk.start_foreign create hheader hne hfit hdecode, Option.bind_some,
    hfind, start_torn hold hactors hne, Except.map]

/-- Wherever the process dies during the two writes of a migration, the next start gives the
same migrated kernel: before the first, by migrating again, and the outputs to hand over with
it; after it, from the snapshot under the new name, with nothing to hand over, since those
outputs were handed over before the first write. Never a refusal. -/
theorem begin_crash (hold : Disk.Torn u.old u.input c₀ u.system history disk)
    (hactors : u.actors = some c₀) (hne : u.system ≠ system)
    (hheader : preludeFits input system = true) (hstarted : 3 ≤ (Frame.decode disk.journal).length)
    (hfind : upgrades.find? (·.reads u.system) = some u)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : savedFits c system history.length
      (u.migration.kernel (recover u.old history).1).image = true)
    (done part : Nat) :
    (Disk.begin input (some c) system create upgrades
        (disk.crash (u.upgraded input c system history.length (recover u.old history)).writes
          done part)).bind Begun.load
      = .ok ((u.migration.kernel (recover u.old history).1).image.kernel,
          if done = 0 then (recover u.old history).2.map u.migration.output else []) := by
  obtain ⟨payloads, hdecode⟩ := decode_torn hold hstarted
  have hfit : Prelude.fits .journal u.system (Entry.own u.input) = true := by
    obtain ⟨_, _, _, _, hkept, -⟩ := hold
    exact hkept.prelude
  match done with
  | 0 =>
    show (Disk.begin input (some c) system create upgrades disk).bind Begun.load = _
    rw [begin_torn hold hactors hne hheader hstarted hfind]
    rfl
  | 1 =>
    have hstart := Disk.start_foreign (input := input) (actors := some c)
      (disk := { disk with snapshot := some (saved c system history.length
        (u.migration.kernel (recover u.old history).1).image) }) create hheader hne hfit hdecode
    simp only [upgraded, writes, Disk.crash, Disk.apply] at hstart ⊢
    simp [Disk.begin, hstart, hfind, start, saved?_saved c system _ _ hsaved, Except.map]
    rfl
  | done + 2 =>
    rw [Disk.crash_of_length_le _ (by simp [upgraded, writes])]
    have hfits : ∀ entry ∈ [Entry.snapshot history.length], Entry.fits input entry = true := by
      simpa using hmark
    have hopen := open?_file input hheader hfits
    have hsize : (file input system [Entry.snapshot history.length]).size ≠ 0 := by
      simp [file, Frame.size_encode, Frame.span, frames, prelude, Prelude.frames]
    have hcurrent : (Frame.decode (file input system [Entry.snapshot history.length])).take 3
        = prelude input system := by
      rw [file, Frame.decode_encode (frames_fit input hheader hfits)]
      simp [frames, prelude, Prelude.frames]
    simp [upgraded, writes, Disk.apply, Disk.begin, Disk.start, Disk.read, hheader, hopen,
      savedOpen?_saved c system _ _ hsaved, hsize, hcurrent, Except.map]
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
theorem holds (k : Kernel sys) (index : Nat) (hheader : preludeFits input system = true)
    (hmark : Entry.fits input (.snapshot index) = true)
    (hsaved : savedFits c system index k.image = true) (disk : Disk) :
    Disk.Holds sys (start := (k, [])) input c system (past index)
      ((writes input c system index k.image).foldl Disk.apply disk) := by
  have htake : (past index : List (Entry σ)).take index = List.replicate index .handed := by
    simp [past]
  have hdrop : (past index : List (Entry σ)).drop index = [.snapshot index] := by
    simp [past]
  refine ⟨index, some index, ?_, ?_, ?_⟩
  · exact {
      prelude := hheader
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
