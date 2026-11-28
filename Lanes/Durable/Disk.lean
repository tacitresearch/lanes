/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Durable.Snapshot

/-!
The two files of a shard, its journal and its snapshot, as data, and everything a shard does
with them as pure functions: what it reads at a start (`Disk.read`, `Disk.load`), what it writes
to repair a journal whose last write did not finish (`Disk.mend`), for a turn (`appendWrites`)
and for a save (`saveWrites`). The process may die between any two writes and in the middle of
an append (`Disk.crash`). The theorems say that whatever it leaves loads, and gives the kernel
the shard had (`Disk.Torn.load`, `Disk.Holds.append_crash`, `Disk.Holds.save_crash`).

`Disk.Holds` is what the files of a running shard are and `Disk.Torn` what its death may make
of them. A start mends the second into the first (`Disk.Torn.mend`), and a turn and a save keep
the first when they finish (`Disk.Holds.append`, `Disk.Holds.save`), so the theorems cover a
shard that is started, works, saves and dies any number of times.

What is left to the adapter is to do one write as `Disk.apply` says it is done.
-/

@[expose] public section

namespace Lanes.Journal

open Kernel (Image)

variable {σ : Signature}

/-- The journal file and the snapshot file. A journal that is not there has no bytes. -/
structure Disk where
  journal : ByteArray := .empty
  snapshot : Option ByteArray := none

inductive Write where
  | append (bytes : ByteArray)
  | putSnapshot (bytes : ByteArray)
  | putJournal (bytes : ByteArray)

namespace Disk

def apply (disk : Disk) : Write → Disk
  | .append bytes => { disk with journal := disk.journal ++ bytes }
  | .putSnapshot bytes => { disk with snapshot := some bytes }
  | .putJournal bytes => { disk with journal := bytes }

/-- The disk if the process dies after `done` of `writes` and, when the next is an append,
after `part` of its bytes. An append is the only write that is done in part: the others are a
rename. With `done` the number of writes or more, every write is done. -/
def crash (disk : Disk) : List Write → Nat → Nat → Disk
  | [], _, _ => disk
  | .append bytes :: _, 0, part => disk.apply (.append (bytes.extract 0 part))
  | _ :: _, 0, _ => disk
  | write :: rest, done + 1, part => (disk.apply write).crash rest done part

variable {sys : System σ}

/-- What the files give at a start. -/
structure Found (sys : System σ) where
  past : List (Entry σ)
  saved : Option (Nat × Image sys)
  /-- The bytes of the journal that hold `past`. What comes after them is a write that did not
  finish. -/
  size : Nat
  /-- Whether the journal begins with the prelude this binary writes, so that it may append to
  it. One written with an older schema, or by another Lanes, is written again (`mend`). -/
  current : Bool := true

/-- How many entries the shard's history has. A journal that was cut starts with the mark of
the save that cut it, and the mark carries its place in the history. -/
def Found.index (found : Found sys) : Nat :=
  match found.past with
  | .snapshot index :: rest => index + 1 + rest.length
  | past => past.length

def read (input : Codec σ.In) (actors : Option (Image.Codecs sys)) (system : String)
    (disk : Disk) : Except Refusal (Found sys) :=
  if preludeFits input system then
    match open? input system disk.journal with
    | .error refusal => .error refusal
    | .ok (past, size) =>
      let current := size == 0 || (Frame.decode disk.journal).take 3 == prelude input system
      match actors, disk.snapshot with
      | some c, some bytes =>
        match savedOpen? c system bytes with
        | .ok saved => .ok { past, saved, size, current }
        | .error refusal => .error refusal
      | _, _ => .ok { past, saved := none, size, current }
  else .error .name

/-- What a start goes on with. A journal that is not there, or has not its header, is the
journal of a shard that has done nothing, and the start begins it (`mend`). A shard that has
made promises it must keep, a vote, is another matter: its journal gone is those promises
forgotten, so its store says that it may not begin one, and the start is refused. -/
def start (input : Codec σ.In) (actors : Option (Image.Codecs sys)) (system : String)
    (create : Bool) (disk : Disk) : Except Refusal (Found sys) :=
  match disk.read input actors system with
  | .error refusal => .error refusal
  | .ok found => if found.size = 0 ∧ ¬create then .error .missing else .ok found

/-- A start that goes on goes on with what `read` found, so what is proved of `read` and
`load` is proved of every start. -/
theorem read_of_start {input : Codec σ.In} {actors : Option (Image.Codecs sys)}
    {system : String} {create : Bool} {disk : Disk} {found : Found sys}
    (h : disk.start input actors system create = .ok found) :
    disk.read input actors system = .ok found := by
  unfold start at h
  split at h
  · cases h
  · next hread =>
    split at h
    · cases h
    · cases h
      exact hread

/-- A journal with nothing in it gets its prelude; one with the prelude of another schema or
another Lanes is written again with this binary's, since what this binary appends is written with
its own schema; and a write that did not finish is cut off, since an entry appended after it
could never be read. `found` is what `read` found. -/
def mend (input : Codec σ.In) (system : String) (disk : Disk) (found : Found sys) : List Write :=
  if found.size = 0 then [.putJournal (Frame.encode (prelude input system))]
  else if !found.current then [.putJournal (file input system found.past)]
  else if found.size < disk.journal.size then [.putJournal (disk.journal.extract 0 found.size)]
  else []

variable [Hashable σ.Id]

/-- The kernel a shard starts with, and the outputs it hands over again. -/
def load (sys : System σ) (input : Codec σ.In) (actors : Option (Image.Codecs sys))
    (system : String) (disk : Disk) : Except Refusal (Kernel sys × List σ.Out) :=
  match disk.read input actors system with
  | .error refusal => .error refusal
  | .ok found =>
    match resume sys found.saved found.past with
    | some start => .ok start
    | none => .error .apart

end Disk

def appendWrites (input : Codec σ.In) (entries : List (Entry σ)) : List Write :=
  [.append (encode input entries)]

/-- A save marks the journal, then puts the snapshot in place, then replaces the journal by one
that starts at the mark. -/
def saveWrites {sys : System σ} (input : Codec σ.In) (c : Image.Codecs sys) (system : String)
    (index : Nat) (image : Image sys) : List Write :=
  appendWrites input [.snapshot index] ++ [.putSnapshot (saved c system index image),
    .putJournal (file input system [.snapshot index])]

/-! What the files must be for a shard with a given history, and that the death of the process
leaves them so. -/

variable {sys : System σ} [Hashable σ.Id] {input : Codec σ.In} {c : Image.Codecs sys}
  {system : String} {history : List (Entry σ)} {lost : Nat} {mark : Option Nat}
  {start : Kernel sys × List σ.Out}

theorem recover_snapshot (sys : System σ) (history : List (Entry σ)) (index : Nat) :
    recover sys (history ++ [.snapshot index]) = ((recover sys history).1.image.kernel, []) := by
  simp only [recover, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact replay1_snapshot ..

/-- A turn journals no mark, so `Disk.Holds.append` covers what it writes. -/
theorem turn_unmarked (k : Kernel sys) (now_ms : Nat) (x : Option σ.In) (fuel : Nat) :
    ∀ entry ∈ (turn k now_ms x fuel).entries, entry.savedAt = none := by
  unfold turn
  split
  · nofun
  · cases x <;> simp [Entry.savedAt]

/-- A store without codecs never saves, so its journal holds its whole history and no mark.
Cut at any byte, it loads as the kernel that the entries wholly written lead to. -/
theorem Disk.load_cut {entries : List (Entry σ)} (hsystem : preludeFits input system = true)
    (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hunmarked : ∀ entry ∈ entries, entry.savedAt = none) (n : Nat)
    (snapshot : Option ByteArray) :
    Disk.load sys input none system
        { journal := (file input system entries).extract 0 n, snapshot }
      = .ok (recover sys
          (entries.take (Frame.whole (frames input system entries) n - 3))) := by
  simp only [Disk.load, Disk.read, hsystem, ↓reduceIte, open?_cut input hsystem hfits n]
  generalize hpast : entries.take _ = past
  have hpast : ∀ entry ∈ past, entry.savedAt = none :=
    fun entry hentry => hunmarked entry (List.mem_of_mem_take (hpast ▸ hentry))
  cases past with
  | nil => rfl
  | cons entry rest => cases entry <;> first | rfl | simp [Entry.savedAt] at hpast

/-- The snapshot file of a shard whose kernel was last saved at the mark `mark`: the kernel as
it was after the entries before the mark. -/
def memo (c : Image.Codecs sys) (system : String) (history : List (Entry σ)) (mark : Option Nat)
    (start : Kernel sys × List σ.Out := Kernel.boot sys) : Option ByteArray :=
  mark.map fun index => saved c system index (replay start (history.take index)).1.image

/-- What makes a journal that has lost the first `lost` entries of `history`, with a snapshot
taken at `mark`, enough to rebuild the kernel. -/
structure Kept (input : Codec σ.In) (c : Image.Codecs sys) (system : String)
    (history : List (Entry σ)) (lost : Nat) (mark : Option Nat) (start : Kernel sys × List σ.Out) :
    Prop where
  prelude : preludeFits input system = true
  entries : ∀ entry ∈ history, Entry.fits input entry = true
  /-- A mark carries its place in the history, so no two are alike. -/
  placed : ∀ i index, history[i]? = some (Entry.snapshot index) → index = i
  /-- The journal starts at the start of the history or at a mark. -/
  cut : lost = 0 ∨ history[lost]? = some (Entry.snapshot lost)
  /-- The mark of the snapshot is in the journal. -/
  marked : ∀ index, mark = some index →
    history[index]? = some (Entry.snapshot index) ∧ lost ≤ index
      ∧ savedFits c system index (replay start (history.take index)).1.image
        = true
  /-- A journal that was cut, or a history that does not start at boot, has its snapshot. -/
  saved : mark = none → lost = 0 ∧ start = Kernel.boot sys

namespace Disk

/-- The files of a running shard whose history is `history`: a whole journal of its entries
from some point on, and the snapshot that stands for the entries before. -/
def Holds (sys : System σ) [Hashable σ.Id] (input : Codec σ.In) (c : Image.Codecs sys)
    (system : String) (history : List (Entry σ)) (disk : Disk)
    (start : Kernel sys × List σ.Out := Kernel.boot sys) : Prop :=
  ∃ lost mark, Kept (start := start) input c system history lost mark
    ∧ disk.journal = file input system (history.drop lost)
    ∧ disk.snapshot = memo (start := start) c system history mark

/-- What the death of the process may leave of files that held `history`: the journal goes on
with entries `more` and is cut at byte `n`, before the first of them ends. -/
def Torn (sys : System σ) [Hashable σ.Id] (input : Codec σ.In) (c : Image.Codecs sys)
    (system : String) (history : List (Entry σ)) (disk : Disk)
    (start : Kernel sys × List σ.Out := Kernel.boot sys) : Prop :=
  ∃ lost mark more n, Kept (start := start) input c system history lost mark
    ∧ (∀ entry ∈ more, Entry.fits input entry = true)
    ∧ (history.drop lost ++ more).take
        (Frame.whole (frames input system (history.drop lost ++ more)) n - 3)
      = history.drop lost
    ∧ disk.journal = (file input system (history.drop lost ++ more)).extract 0 n
    ∧ disk.snapshot = memo (start := start) c system history mark

end Disk

namespace Kept

theorem lost_le (h : Kept (start := start) input c system history lost mark) : lost ≤ history.length := by
  rcases h.cut with rfl | hcut
  · exact Nat.zero_le _
  · exact Nat.le_of_lt (List.getElem?_eq_some_iff.mp hcut).1

omit [Hashable σ.Id] in
private theorem split {index : Nat} {entry : Entry σ} (h : history[index]? = some entry) :
    history = history.take index ++ entry :: history.drop (index + 1) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]

private theorem resume_none
    (h : Kept (start := Kernel.boot sys) input c system history lost mark) :
    resume sys none history = some (recover sys history) := by
  cases history with
  | nil => rfl
  | cons entry rest =>
    cases entry with
    | snapshot index =>
      obtain rfl := h.placed 0 index rfl
      rfl
    | _ => rfl

/-- The snapshot and the journal that is left give what the whole history gives. -/
theorem resume (h : Kept (start := start) input c system history lost mark) :
    resume sys (mark.map fun index => (index, (replay start (history.take index)).1.image))
      (history.drop lost) = some (replay start history) := by
  cases mark with
  | none =>
    obtain ⟨hlost, rfl⟩ := h.saved rfl
    rw [hlost]
    exact h.resume_none
  | some index =>
    obtain ⟨hmark, hle, _⟩ := h.marked index rfl
    have hlt := (List.getElem?_eq_some_iff.mp hmark).1
    have hdrop : history.drop lost
        = (history.take index).drop lost ++ .snapshot index :: history.drop (index + 1) := by
      conv => lhs; rw [split hmark]
      exact List.drop_append_of_le_length (by rw [List.length_take]; omega)
    have hold : ∀ entry ∈ history.take index, entry.savedAt ≠ some index := by
      intro entry hentry hsaved
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentry
      rw [List.getElem?_take] at hi
      split at hi
      · cases entry <;> simp only [Entry.savedAt, Option.some.injEq, reduceCtorEq] at hsaved
        subst hsaved
        have := h.placed i _ hi
        omega
      · cases hi
    rw [hdrop, Option.map_some]
    conv => rhs; rw [split hmark]
    exact resume_eq_replay sys start _ _ index lost hold

theorem index (h : Kept (start := start) input c system history lost mark) (saved : Option (Nat × Image sys))
    (size : Nat) :
    Disk.Found.index { past := history.drop lost, saved, size } = history.length := by
  rcases h.cut with rfl | hcut
  · cases history with
    | nil => rfl
    | cons entry rest =>
      cases entry with
      | snapshot index =>
        obtain rfl := h.placed 0 index rfl
        simp [Disk.Found.index]
        omega
      | _ => rfl
  · obtain ⟨hlt, hentry⟩ := List.getElem?_eq_some_iff.mp hcut
    simp only [Disk.Found.index, List.drop_eq_getElem_cons hlt, hentry, List.length_drop]
    omega

theorem memo_append (h : Kept (start := start) input c system history lost mark) (entries : List (Entry σ)) :
    memo (start := start) c system (history ++ entries) mark = memo (start := start) c system history mark := by
  cases mark with
  | none => rfl
  | some index =>
    have hlt := (List.getElem?_eq_some_iff.mp (h.marked index rfl).1).1
    simp only [memo, Option.map_some, List.take_append_of_le_length (Nat.le_of_lt hlt)]

/-- The history may go on with entries whose marks, if any, carry their place. -/
theorem extend (h : Kept (start := start) input c system history lost mark) {entries : List (Entry σ)}
    (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hplaced : ∀ i index, entries[i]? = some (.snapshot index) → index = history.length + i) :
    Kept (start := start) input c system (history ++ entries) lost mark where
  prelude := h.prelude
  entries entry hentry := (List.mem_append.mp hentry).elim (h.entries entry) (hfits entry)
  placed i index hi := by
    rw [List.getElem?_append] at hi
    split at hi
    · exact h.placed i index hi
    · have := hplaced _ index hi
      omega
  cut := h.cut.imp id fun hcut => by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hcut).1, hcut]
  marked index hindex := by
    obtain ⟨hmark, hle, hsaved⟩ := h.marked index hindex
    have hlt := (List.getElem?_eq_some_iff.mp hmark).1
    rw [List.getElem?_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact ⟨hmark, hle, hsaved⟩
  saved := h.saved

omit [Hashable σ.Id] in
private theorem placed_unmarked {entries : List (Entry σ)}
    (h : ∀ entry ∈ entries, entry.savedAt = none) (i index : Nat)
    (hi : entries[i]? = some (.snapshot index)) : index = history.length + i := by
  simpa [Entry.savedAt] using h _ (List.mem_of_getElem? hi)

omit [Hashable σ.Id] in
private theorem placed_mark (i index : Nat)
    (hi : ([.snapshot history.length] : List (Entry σ))[i]? = some (.snapshot index)) :
    index = history.length + i := by
  cases i with
  | zero => simpa [eq_comm] using hi
  | succ i => simp at hi

/-- The kernel is saved at the end of the history, and the journal is not cut yet. -/
private theorem save (h : Kept (start := start) input c system history lost mark)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : savedFits c system history.length (replay start history).1.image
      = true) :
    Kept (start := start) input c system (history ++ [.snapshot history.length]) lost (some history.length) :=
  { h.extend (by simpa using hmark) placed_mark with
    marked := by
      rintro _ ⟨rfl⟩
      exact ⟨by simp, h.lost_le, by rw [List.take_left]; exact hsaved⟩
    saved := nofun }

/-- The journal is cut at the mark of the save. -/
private theorem saveCut (h : Kept (start := start) input c system history lost mark)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : savedFits c system history.length (replay start history).1.image
      = true) :
    Kept (start := start) input c system (history ++ [.snapshot history.length]) history.length
      (some history.length) :=
  { h.save hmark hsaved with
    cut := .inr (by simp)
    marked := by
      rintro _ ⟨rfl⟩
      exact ⟨by simp, Nat.le_refl _, by rw [List.take_left]; exact hsaved⟩
    saved := nofun }

end Kept

namespace Disk

variable {disk : Disk}

theorem crash_of_length_le (disk : Disk) {writes : List Write} {done : Nat}
    (h : writes.length ≤ done) (part : Nat) :
    disk.crash writes done part = writes.foldl apply disk := by
  induction writes generalizing disk done with
  | nil => rfl
  | cons write rest ih =>
    cases done with
    | zero => simp at h
    | succ done => cases write <;> exact ih _ (by simpa using h)

theorem Holds.torn (h : Holds sys (start := start) input c system history disk) :
    Torn sys (start := start) input c system history disk := by
  obtain ⟨lost, mark, hkept, hjournal, hsnapshot⟩ := h
  have hlen : (frames input system (history.drop lost)).length = (history.drop lost).length + 3 := by
    simp [frames, prelude, Prelude.frames, write]
  refine ⟨lost, mark, [], (file input system (history.drop lost)).size, hkept, nofun, ?_, ?_,
    hsnapshot⟩
  · rw [List.append_nil]
    exact List.take_of_length_le (by
      have := (Frame.le_whole_iff (payloads := frames input system (history.drop lost))
        (k := (history.drop lost).length + 3) (file input system (history.drop lost)).size
        (by omega)).mpr
          (Nat.le_of_eq (by rw [List.take_of_length_le (by omega)]; rfl))
      omega)
  · rw [List.append_nil, hjournal, ByteArray.extract_zero_size]

/-- A new shard has no files. -/
theorem torn_nil (h : preludeFits input system = true) : Torn sys input c system [] {} :=
  ⟨0, none, [], 0, ⟨h, nofun, nofun, .inl rfl, nofun, fun _ => ⟨rfl, rfl⟩⟩, nofun, rfl,
    by simp [ByteArray.extract_same], rfl⟩

/-- The bytes a start keeps of a journal cut where its first `whole` frames end. -/
def keptOf (frames : List ByteArray) (whole : Nat) : Nat :=
  if whole < 3 then 0 else Frame.span (frames.take whole)

omit [Hashable σ.Id] in
private theorem current_cut {entries : List (Entry σ)}
    (hfit : ∀ p ∈ frames input system entries, p.size < 2 ^ 32) (n : Nat) :
    (keptOf (frames input system entries) (Frame.whole (frames input system entries) n) == 0
      || (Frame.decode ((file input system entries).extract 0 n)).take 3
        == prelude input system) = true := by
  rw [file, Frame.decode_take_eq hfit n, List.take_take]
  unfold keptOf
  generalize Frame.whole (frames input system entries) n = w
  by_cases hw : w < 3
  · simp [hw]
  · have : min 3 w = 3 := by omega
    simp [this, frames, prelude, Prelude.frames]

private theorem read_torn (h : Kept (start := start) input c system history lost mark) {more : List (Entry σ)}
    {n : Nat} (hmore : ∀ entry ∈ more, Entry.fits input entry = true)
    (hcut : (history.drop lost ++ more).take
        (Frame.whole (frames input system (history.drop lost ++ more)) n - 3)
      = history.drop lost)
    (hjournal : disk.journal = (file input system (history.drop lost ++ more)).extract 0 n)
    (hsnapshot : disk.snapshot = memo (start := start) c system history mark) :
    disk.read input (some c) system = .ok {
      past := history.drop lost
      saved := mark.map fun index => (index, (replay start (history.take index)).1.image)
      size := keptOf (frames input system (history.drop lost ++ more))
        (Frame.whole (frames input system (history.drop lost ++ more)) n) } := by
  have hfits : ∀ entry ∈ history.drop lost ++ more, Entry.fits input entry = true :=
    fun entry hentry => (List.mem_append.mp hentry).elim
      (fun hkept => h.entries entry (List.mem_of_mem_drop hkept)) (hmore entry)
  have hcurrent := current_cut (input := input) (system := system)
    (Journal.frames_fit input h.prelude hfits) n
  rw [← hjournal] at hcurrent
  simp only [read, h.prelude, ↓reduceIte, hjournal, open?_cut input h.prelude hfits n, hcut,
    hsnapshot]
  rw [← hjournal]
  unfold keptOf at hcurrent
  simp only [hcurrent]
  cases mark with
  | none => rfl
  | some index => simp [memo, keptOf, savedOpen?_saved c system index _ (h.marked index rfl).2.2]

/-- Whatever the death of the process leaves loads, and gives the kernel the shard had and the
outputs it had not marked as handed over: never a refusal, never another kernel. -/
theorem Torn.load (h : Torn sys (start := start) input c system history disk) :
    disk.load sys input (some c) system = .ok (replay start history) := by
  obtain ⟨lost, mark, more, n, hkept, hmore, hcut, hjournal, hsnapshot⟩ := h
  rw [Disk.load, read_torn hkept hmore hcut hjournal hsnapshot]
  simp only [hkept.resume]

/-- At a start the files give the number of entries in the history, which is the index of the
next mark. -/
theorem Torn.read (h : Torn sys (start := start) input c system history disk) :
    ∃ found, disk.read input (some c) system = .ok found ∧ found.index = history.length := by
  obtain ⟨lost, mark, more, n, hkept, hmore, hcut, hjournal, hsnapshot⟩ := h
  exact ⟨_, read_torn hkept hmore hcut hjournal hsnapshot, hkept.index _ _⟩

/-- Mending what the death of the process left gives the files of a running shard with the
same history. -/
theorem Torn.mend (h : Torn sys (start := start) input c system history disk) {found : Found sys}
    (hread : disk.read input (some c) system = .ok found) :
    Holds sys (start := start) input c system history
      ((disk.mend input system found).foldl apply disk) := by
  obtain ⟨lost, mark, more, n, hkept, hmore, hcut, hjournal, hsnapshot⟩ := h
  obtain rfl := Except.ok.inj ((read_torn hkept hmore hcut hjournal hsnapshot).symm.trans hread)
  have hmended : disk.journal.extract 0 (Frame.span
        ((frames input system (history.drop lost ++ more)).take
          (Frame.whole (frames input system (history.drop lost ++ more)) n)))
      = Frame.encode ((frames input system (history.drop lost ++ more)).take
          (Frame.whole (frames input system (history.drop lost ++ more)) n)) := by
    rw [hjournal]
    exact Frame.extract_take_whole _ n
  simp only [Disk.mend, keptOf]
  generalize Frame.whole (frames input system (history.drop lost ++ more)) n = whole
    at hcut hmended ⊢
  by_cases hw : whole < 3
  · have hnone : history.drop lost = [] := by
      rw [show whole - 3 = 0 by omega] at hcut
      simpa using hcut.symm
    simp only [hw, ↓reduceIte, List.foldl_cons, List.foldl_nil]
    exact ⟨lost, mark, hkept, by simp [apply, hnone, file_eq, encode, write],
      by simpa [apply] using hsnapshot⟩
  · obtain ⟨kept, rfl⟩ : ∃ kept, whole = kept + 3 := ⟨whole - 3, by omega⟩
    have htake : (frames input system (history.drop lost ++ more)).take (kept + 3)
        = frames input system (history.drop lost) := by
      simp only [frames, prelude, Prelude.frames, List.cons_append, List.nil_append,
        List.take_succ_cons, write, ← List.map_take]
      rw [Nat.add_sub_cancel] at hcut
      rw [hcut]
    simp only [htake] at hmended ⊢
    have hsize : Frame.span (frames input system (history.drop lost)) ≠ 0 := by
      simp [Frame.span, frames, prelude, Prelude.frames]
    simp only [hw, hsize, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    split
    · exact ⟨lost, mark, hkept, hmended, hsnapshot⟩
    · rename_i hwhole
      exact ⟨lost, mark, hkept,
        (Frame.extract_of_size_le (Nat.le_of_not_lt hwhole)).symm.trans hmended, hsnapshot⟩

omit [Hashable σ.Id] in
theorem length_mend_le (input : Codec σ.In) (system : String) (disk : Disk) (found : Found sys) :
    (disk.mend input system found).length ≤ 1 := by
  unfold Disk.mend
  split
  · simp
  · split
    · simp
    · split <;> simp

/-- And dying while mending leaves what was there or what mending gives. -/
theorem Torn.mend_crash (h : Torn sys (start := start) input c system history disk) {found : Found sys}
    (hread : disk.read input (some c) system = .ok found) (done part : Nat) :
    Torn sys (start := start) input c system history
      (disk.crash (disk.mend input system found) done part) := by
  cases done with
  | zero =>
    have hsame : disk.crash (disk.mend input system found) 0 part = disk := by
      unfold Disk.mend
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    rw [hsame]
    exact h
  | succ done =>
    rw [crash_of_length_le _ (Nat.le_trans (length_mend_le ..) (Nat.le_add_left 1 done))]
    exact (h.mend hread).torn

private theorem journal_append (hkept : Kept (start := start) input c system history lost mark)
    (hjournal : disk.journal = file input system (history.drop lost))
    (entries : List (Entry σ)) :
    disk.journal ++ encode input entries
      = file input system ((history ++ entries).drop lost) := by
  rw [hjournal, List.drop_append_of_le_length hkept.lost_le, file_eq, file_eq, encode_append,
    ByteArray.append_assoc]

private theorem holds_append (hkept : Kept (start := start) input c system history lost mark)
    (hjournal : disk.journal = file input system (history.drop lost))
    (hsnapshot : disk.snapshot = memo (start := start) c system history mark) {entries : List (Entry σ)}
    (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hplaced : ∀ i index, entries[i]? = some (.snapshot index) → index = history.length + i) :
    Holds sys (start := start) input c system (history ++ entries) (disk.apply (.append (encode input entries))) :=
  ⟨lost, mark, hkept.extend hfits hplaced, journal_append hkept hjournal entries,
    (hkept.memo_append entries).symm ▸ hsnapshot⟩

private theorem torn_append (hkept : Kept (start := start) input c system history lost mark)
    (hjournal : disk.journal = file input system (history.drop lost))
    (hsnapshot : disk.snapshot = memo (start := start) c system history mark) {entries : List (Entry σ)}
    (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hplaced : ∀ i index, entries[i]? = some (.snapshot index) → index = history.length + i)
    (part : Nat) :
    Torn sys (start := start) input c system (history ++ entries.take (Frame.whole (write input entries) part))
      (disk.apply (.append ((encode input entries).extract 0 part))) := by
  obtain ⟨w, hw⟩ : ∃ w, w = Frame.whole (write input entries) part := ⟨_, rfl⟩
  rw [← hw]
  have hdrop : (history ++ entries.take w).drop lost = history.drop lost ++ entries.take w :=
    List.drop_append_of_le_length hkept.lost_le
  have hall : history.drop lost ++ entries.take w ++ entries.drop w
      = history.drop lost ++ entries := by
    rw [List.append_assoc, List.take_append_drop]
  have hwhole : Frame.whole (frames input system (history.drop lost ++ entries))
      ((file input system (history.drop lost)).size + part)
        = (history.drop lost).length + 3 + w := by
    have hframes : frames input system (history.drop lost ++ entries)
        = frames input system (history.drop lost) ++ write input entries := by
      simp [frames, write, List.append_assoc]
    rw [hframes, file, Frame.size_encode, Frame.whole_append, hw]
    simp [frames, prelude, Prelude.frames, write]
  refine ⟨lost, mark, entries.drop w, (file input system (history.drop lost)).size + part,
    hkept.extend (fun entry hentry => hfits entry (List.mem_of_mem_take hentry)) ?_,
    fun entry hentry => hfits entry (List.mem_of_mem_drop hentry), ?_, ?_,
    (hkept.memo_append _).symm ▸ hsnapshot⟩
  · intro i index hi
    rw [List.getElem?_take] at hi
    split at hi
    · exact hplaced i index hi
    · cases hi
  · rw [hdrop, hall, hwhole, Nat.add_right_comm, Nat.add_sub_cancel, List.take_length_add_append]
  · rw [hdrop, hall]
    show disk.journal ++ _ = _
    rw [hjournal, file_eq (entries := _ ++ _), encode_append, ← ByteArray.append_assoc, ← file_eq,
      ByteArray.extract_append, Frame.extract_of_size_le (Nat.le_add_right ..), Nat.zero_sub,
      Nat.add_sub_cancel_left]

/-- The mark of a save is in the history once all its bytes are written. -/
private theorem torn_mark (hkept : Kept (start := start) input c system history lost mark)
    (hjournal : disk.journal = file input system (history.drop lost))
    (hsnapshot : disk.snapshot = memo (start := start) c system history mark)
    (hfits : ∀ entry ∈ [Entry.snapshot history.length], Entry.fits input entry = true)
    (part : Nat) :
    Torn sys (start := start) input c system
      (history ++ if part < (encode input [.snapshot history.length]).size then []
        else [.snapshot history.length])
      (disk.apply (.append ((encode input [.snapshot history.length]).extract 0 part))) := by
  have htorn := torn_append hkept hjournal hsnapshot hfits Kept.placed_mark part
  have hsize : (encode input [.snapshot history.length]).size
      = 20 + (Entry.bytes input (.snapshot history.length)).size := by
    simp [encode, write]
  by_cases hpart : part < (encode input [.snapshot history.length]).size
  · have hnone : Frame.whole (write input [.snapshot history.length]) part = 0 := by
      simp [write, Frame.whole]
      omega
    rw [hnone] at htorn
    simpa [hpart] using htorn
  · have hone : Frame.whole (write input [.snapshot history.length]) part = 1 := by
      simp [write, Frame.whole]
      omega
    rw [hone] at htorn
    simpa [hpart] using htorn

/-- A turn's append, done whole, leaves the files of a running shard. -/
theorem Holds.append (h : Holds sys (start := start) input c system history disk) {entries : List (Entry σ)}
    (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hunmarked : ∀ entry ∈ entries, entry.savedAt = none) :
    Holds sys (start := start) input c system (history ++ entries)
      ((appendWrites input entries).foldl apply disk) := by
  obtain ⟨lost, mark, hkept, hjournal, hsnapshot⟩ := h
  exact holds_append hkept hjournal hsnapshot hfits (Kept.placed_unmarked hunmarked)

/-- If the process dies at any byte of a turn's append, the history has grown by the entries
wholly written, and by no others. -/
theorem Holds.append_crash (h : Holds sys (start := start) input c system history disk)
    {entries : List (Entry σ)} (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hunmarked : ∀ entry ∈ entries, entry.savedAt = none) (done part : Nat) :
    Torn sys (start := start) input c system
      (history ++ if done = 0 then entries.take (Frame.whole (write input entries) part)
        else entries)
      (disk.crash (appendWrites input entries) done part) := by
  obtain ⟨lost, mark, hkept, hjournal, hsnapshot⟩ := h
  cases done with
  | zero => exact torn_append hkept hjournal hsnapshot hfits (Kept.placed_unmarked hunmarked) part
  | succ done =>
    exact (holds_append hkept hjournal hsnapshot hfits (Kept.placed_unmarked hunmarked)).torn

/-- A save, done whole, leaves the files of a running shard whose history ends with the mark:
its kernel is then the one the saved image restores (`recover_snapshot`). -/
theorem Holds.save (h : Holds sys (start := start) input c system history disk)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : savedFits c system history.length (replay start history).1.image
      = true) :
    Holds sys (start := start) input c system (history ++ [.snapshot history.length])
      ((saveWrites input c system history.length (replay start history).1.image).foldl apply
        disk) := by
  obtain ⟨lost, mark, hkept, -, -⟩ := h
  exact ⟨history.length, some history.length, hkept.saveCut hmark hsaved,
    by simp [saveWrites, appendWrites, apply], by simp [saveWrites, appendWrites, apply, memo]⟩

/-- If the process dies anywhere in a save, at any byte of the mark or between two of the three
writes, the history is what it was, or, once the mark is wholly written, what it was and the
mark. -/
theorem Holds.save_crash (h : Holds sys (start := start) input c system history disk)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : savedFits c system history.length (replay start history).1.image
      = true) (done part : Nat) :
    Torn sys (start := start) input c system
      (history ++ if done = 0 ∧ part < (encode input [.snapshot history.length]).size then []
        else [.snapshot history.length])
      (disk.crash (saveWrites input c system history.length (replay start history).1.image) done
        part) := by
  have hwhole := h.save hmark hsaved
  obtain ⟨lost, mark, hkept, hjournal, hsnapshot⟩ := h
  have hfits : ∀ entry ∈ [Entry.snapshot history.length], Entry.fits input entry = true := by
    simpa using hmark
  match done with
  | 0 =>
    show Torn sys (start := start) input c system _
      (disk.apply (.append ((encode input [.snapshot history.length]).extract 0 part)))
    simpa using torn_mark hkept hjournal hsnapshot hfits part
  | 1 =>
    simpa [saveWrites, appendWrites, crash] using
      (holds_append hkept hjournal hsnapshot hfits Kept.placed_mark).torn
  | 2 =>
    simpa [saveWrites, appendWrites, crash] using Holds.torn ⟨lost, some history.length,
      hkept.save hmark hsaved, journal_append hkept hjournal _, by simp [apply, memo]⟩
  | done + 3 =>
    rw [crash_of_length_le _ (by simp [saveWrites, appendWrites])]
    simpa using hwhole.torn

/-- A shard that dies at any byte of a turn's append starts again with the kernel that the
entries wholly written lead to. -/
theorem Holds.load_append_crash (h : Holds sys (start := start) input c system history disk)
    {entries : List (Entry σ)} (hfits : ∀ entry ∈ entries, Entry.fits input entry = true)
    (hunmarked : ∀ entry ∈ entries, entry.savedAt = none) (done part : Nat) :
    (disk.crash (appendWrites input entries) done part).load sys input (some c) system
      = .ok (replay start (history ++ if done = 0
          then entries.take (Frame.whole (write input entries) part) else entries)) :=
  (h.append_crash hfits hunmarked done part).load

/-- A shard that dies anywhere in a save starts again with the kernel it had or, once the mark
is wholly written, with the kernel the saved image restores (`recover_snapshot`): never a
refusal, never another kernel. -/
theorem Holds.load_save_crash (h : Holds sys (start := start) input c system history disk)
    (hmark : Entry.fits input (.snapshot history.length) = true)
    (hsaved : savedFits c system history.length (replay start history).1.image
      = true) (done part : Nat) :
    (disk.crash (saveWrites input c system history.length (replay start history).1.image) done
        part).load sys input (some c) system
      = .ok (replay start (history
          ++ if done = 0 ∧ part < (encode input [.snapshot history.length]).size then []
            else [.snapshot history.length])) :=
  (h.save_crash hmark hsaved done part).load

end Disk

end Lanes.Journal
