/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# A file system that may lose power

Files and directories as a value (`Fs`), the calls a program makes (`Op`) and what each does
(`Fs.step`), what an error that hides its outcome may leave (`Fs.failures`), and what a loss of
power may leave (`Fs.crash`, every outcome listed by `Fs.crashes`, `Fs.crash_mem_crashes`).

A file is an inode: what is on the disk for sure (`synced`) and the changes made since its last
`fsync` (`pending`). A directory is the same for its entries: each change to them (a create, a
rename, a delete) is a batch of entries set or removed at once. A loss of power keeps these
rules, the model's assumptions, which Linux's ext4 gives and POSIX does not promise:

- an `fsync` of a file puts its contents and size on the disk, and an `fsync` of a directory its
  entries; nothing else does;
- of a file's changes since its last `fsync`, a crash keeps the first few, in the order they were
  made, and may tear the next to any prefix of its bytes (`File.survive`);
- of a directory's changes since its last `fsync`, a crash keeps the first few, in order, each
  whole (`Dir.survive`): a rename is atomic, and is durable once its directories are synced;
  a file created and not yet in a synced directory may vanish with its contents;
- directories do not keep each other's order.

An `fsync` that fails may leave the file as any crash would, and on the disk (`Fs.failures`):
Linux may drop the pages it could not write and report it once, so a second `fsync` proves
nothing.
-/

@[expose] public section

namespace Lanes.FileSystem

abbrev Bytes := List UInt8

/-- Names from the root: `["var", "log", "app.log"]` is `/var/log/app.log`. -/
abbrev Path := List String

/-- `l` with `a` bound to `v`, or `a` unbound when `v` is `none`. -/
def put {α β : Type} [BEq α] (l : List (α × β)) (a : α) : Option β → List (α × β)
  | some b => (a, b) :: l.filter (·.1 != a)
  | none => l.filter (·.1 != a)

/-- A change to a file's bytes. An append is a write at the end of the file as it is when it is
made: the changes kept by a crash are kept in order, so the end is the same then. -/
inductive Change where
  /-- Bytes written at `offset`; a file shorter than that is first filled with zeros. -/
  | write (offset : Nat) (bytes : Bytes)
  /-- The file cut, or filled with zeros, to `size` bytes. -/
  | truncate (size : Nat)
  deriving DecidableEq, Repr, Hashable

def zeros (n : Nat) : Bytes := List.replicate n 0

/-- A write of no bytes changes nothing, past the end of the file too. -/
def Change.apply : Change → Bytes → Bytes
  | .write _ [], data => data
  | .write offset bytes, data =>
    data.take offset ++ zeros (offset - data.length) ++ bytes ++ data.drop (offset + bytes.length)
  | .truncate size, data => data.take size ++ zeros (size - data.length)

@[simp] theorem Change.apply_write_end (data bytes : Bytes) :
    (Change.write data.length bytes).apply data = data ++ bytes := by
  cases bytes with
  | nil => simp [Change.apply]
  | cons b bs => simp [Change.apply, zeros]

@[simp] theorem Change.apply_write_nil (bytes : Bytes) : (Change.write 0 bytes).apply [] = bytes :=
  Change.apply_write_end [] bytes

/-- The change torn after `part` bytes. A truncation is not torn. -/
def Change.torn : Change → Nat → Change
  | .write offset bytes, part => .write offset (bytes.take part)
  | .truncate size, _ => .truncate size

/-- How many bytes the change may be torn after. -/
def Change.size : Change → Nat
  | .write _ bytes => bytes.length
  | .truncate _ => 0

def applyAll (changes : List Change) (data : Bytes) : Bytes :=
  changes.foldl (fun data c => c.apply data) data

structure File where
  synced : Bytes := []
  pending : List Change := []
  deriving DecidableEq, Repr, Hashable

namespace File

/-- What a read sees. -/
def data (f : File) : Bytes := applyAll f.pending f.synced

def change (f : File) (c : Change) : File := { f with pending := f.pending ++ [c] }

def sync (f : File) : File := { synced := f.data, pending := [] }

/-- What a crash leaves: the first `kept` changes, and the next torn after `part` bytes. -/
def survive (f : File) (kept part : Nat) : Bytes :=
  let before := applyAll (f.pending.take kept) f.synced
  match f.pending[kept]? with
  | some c => (c.torn part).apply before
  | none => before

end File

abbrev Entries := List (String × Nat)

/-- Entries set (to an inode) or removed (`none`) at once. -/
abbrev Batch := List (String × Option Nat)

def applyBatch (entries : Entries) (batch : Batch) : Entries :=
  batch.foldl (fun entries (name, inode) => put entries name inode) entries

structure Dir where
  synced : Entries := []
  pending : List Batch := []
  deriving DecidableEq, Repr, Hashable

namespace Dir

/-- What a listing and a lookup see. -/
def entries (d : Dir) : Entries := d.pending.foldl applyBatch d.synced

def add (d : Dir) (batch : Batch) : Dir := { d with pending := d.pending ++ [batch] }

def sync (d : Dir) : Dir := { synced := d.entries, pending := [] }

/-- What a crash leaves: the first `kept` batches. -/
def survive (d : Dir) (kept : Nat) : Entries := (d.pending.take kept).foldl applyBatch d.synced

end Dir

inductive Node where
  | file (f : File)
  | dir (d : Dir)
  deriving DecidableEq, Repr, Hashable

/-- Every inode, by number, the root being `0`. An inode no entry names is never seen again;
it is kept, so that numbers are never reused. -/
structure Fs where
  nodes : List (Nat × Node) := [(0, .dir {})]
  deriving DecidableEq, Repr, Hashable

inductive Error where
  | notFound
  | alreadyExists
  | notDir
  | isDir
  | notEmpty
  /-- The root deleted, or a directory moved into itself. -/
  | invalid
  /-- Anything else the operating system reports. It says nothing of whether the call took
  effect (`Fs.failures`). -/
  | io
  deriving DecidableEq, Repr, Hashable

/-- A call. The bytes are a list in the model and a `ByteArray` in the binding
(`Lanes/Outside/IO/FileSystem.lean`), which performs `Op.map ByteArray.toList` of what it is
given. -/
inductive Op (B : Type := Bytes) where
  | read (path : Path)
  | write (path : Path) (offset : Nat) (bytes : B)
  | append (path : Path) (bytes : B)
  /-- Create an empty file, or empty the file there. -/
  | create (path : Path)
  | truncate (path : Path) (size : Nat)
  | mkdir (path : Path)
  /-- Over a file, or an empty directory, that is there. -/
  | rename (src dst : Path)
  /-- A file, or an empty directory. -/
  | delete (path : Path)
  | list (path : Path)
  /-- Of a file, its contents; of a directory, its entries. -/
  | fsync (path : Path)
  deriving DecidableEq, Repr, Hashable

inductive Answer (B : Type := Bytes) where
  | done
  | bytes (b : B)
  /-- A directory's names, sorted. -/
  | names (names : List String)
  | failed (e : Error)
  deriving DecidableEq, Repr, Hashable

def Op.map {B C : Type} (f : B → C) : Op B → Op C
  | .read p => .read p
  | .write p offset bytes => .write p offset (f bytes)
  | .append p bytes => .append p (f bytes)
  | .create p => .create p
  | .truncate p size => .truncate p size
  | .mkdir p => .mkdir p
  | .rename src dst => .rename src dst
  | .delete p => .delete p
  | .list p => .list p
  | .fsync p => .fsync p

def Answer.map {B C : Type} (f : B → C) : Answer B → Answer C
  | .done => .done
  | .bytes b => .bytes (f b)
  | .names ns => .names ns
  | .failed e => .failed e

/-- A path's directory and last name. The root has neither. -/
def parentOf (p : Path) : Except Error (Path × String) :=
  match p.getLast? with
  | some name => .ok (p.dropLast, name)
  | none => .error .invalid

def sortNames (names : List String) : List String :=
  names.mergeSort fun a b => decide (a ≤ b)

namespace Node

def crash : Node → Nat × Nat → Node
  | .file f, (kept, part) => .file { synced := f.survive kept part }
  | .dir d, (kept, _) => .dir { synced := d.survive kept }

/-- Every way a crash may leave the node, as arguments of `crash`. -/
def choices : Node → List (Nat × Nat)
  | .file f => (List.range (f.pending.length + 1)).flatMap fun kept =>
      (List.range ((f.pending[kept]?.map Change.size).getD 0 + 1)).map (kept, ·)
  | .dir d => (List.range (d.pending.length + 1)).map (·, 0)

def sync : Node → Node
  | .file f => .file f.sync
  | .dir d => .dir d.sync

end Node

namespace Fs

def node (s : Fs) (i : Nat) : Option Node := s.nodes.lookup i

def set (s : Fs) (i : Nat) (n : Node) : Fs := { nodes := put s.nodes i (some n) }

/-- A number no inode has. -/
def fresh (s : Fs) : Nat := s.nodes.foldr (fun p m => max p.1 m) 0 + 1

def entriesOf (s : Fs) (i : Nat) : Option Entries :=
  match s.node i with
  | some (.dir d) => some d.entries
  | _ => none

def child (s : Fs) (i : Nat) (name : String) : Option Nat :=
  (s.entriesOf i).bind (·.lookup name)

def resolveFrom (s : Fs) (i : Nat) : Path → Option Nat
  | [] => some i
  | name :: rest => (s.child i name).bind (s.resolveFrom · rest)

/-- The directories whose entries `resolveFrom i p` reads. -/
def way (s : Fs) (i : Nat) : Path → List Nat
  | [] => []
  | name :: rest => i :: match s.child i name with
    | some j => s.way j rest
    | none => []

def resolve (s : Fs) (p : Path) : Option Nat := s.resolveFrom 0 p

def find (s : Fs) (p : Path) : Option (Nat × Node) :=
  (s.resolve p).bind fun i => (s.node i).map (i, ·)

def fileAt (s : Fs) (p : Path) : Except Error (Nat × File) :=
  match s.find p with
  | some (i, .file f) => .ok (i, f)
  | some (_, .dir _) => .error .isDir
  | none => .error .notFound

def dirAt (s : Fs) (p : Path) : Except Error (Nat × Dir) :=
  match s.find p with
  | some (i, .dir d) => .ok (i, d)
  | some (_, .file _) => .error .notDir
  | none => .error .notFound

/-- What a read of `p` gives, if it is a file. -/
def read (s : Fs) (p : Path) : Option Bytes :=
  match s.fileAt p with
  | .ok (_, f) => some f.data
  | .error _ => none

def changeFile (s : Fs) (p : Path) (c : File → Change) : Except Error (Fs × Answer) := do
  let (i, f) ← s.fileAt p
  return (s.set i (.file (f.change (c f))), .done)

/-- A new inode `node` named `p`. -/
def link (s : Fs) (p : Path) (node : Node) : Except Error (Fs × Answer) := do
  let (dir, name) ← parentOf p
  let (d, D) ← s.dirAt dir
  let n := s.fresh
  return ((s.set n node).set d (.dir (D.add [(name, some n)])), .done)

def create (s : Fs) (p : Path) : Except Error (Fs × Answer) :=
  match s.find p with
  | some (i, .file f) => .ok (s.set i (.file (f.change (.truncate 0))), .done)
  | some (_, .dir _) => .error .isDir
  | none => s.link p (.file {})

def mkdir (s : Fs) (p : Path) : Except Error (Fs × Answer) :=
  match s.find p with
  | some _ => .error .alreadyExists
  | none => s.link p (.dir {})

def delete (s : Fs) (p : Path) : Except Error (Fs × Answer) := do
  let (dir, name) ← parentOf p
  let (d, D) ← s.dirAt dir
  let unlinked := (s.set d (.dir (D.add [(name, none)])), Answer.done)
  match s.find p with
  | some (_, .file _) => return unlinked
  | some (_, .dir E) => if E.entries.isEmpty then return unlinked else .error .notEmpty
  | none => .error .notFound

/-- Whether `node` may be renamed over what `dst` names. -/
def replaces (node : Node) : Option (Nat × Node) → Except Error Unit
  | none => .ok ()
  | some (_, .file _) => match node with
    | .file _ => .ok ()
    | .dir _ => .error .notDir
  | some (_, .dir E) => match node with
    | .file _ => .error .isDir
    | .dir _ => if E.entries.isEmpty then .ok () else .error .notEmpty

def rename (s : Fs) (src dst : Path) : Except Error (Fs × Answer) := do
  let (sdir, a) ← parentOf src
  let (ddir, b) ← parentOf dst
  let (sd, SD) ← s.dirAt sdir
  let (dd, DD) ← s.dirAt ddir
  let some (i, node) := s.find src | .error .notFound
  if src = dst then return (s, .done)
  if node matches .dir _ ∧ src <+: dst then .error .invalid
  replaces node (s.find dst)
  if sd = dd then return (s.set sd (.dir (SD.add [(a, none), (b, some i)])), .done)
  return ((s.set sd (.dir (SD.add [(a, none)]))).set dd (.dir (DD.add [(b, some i)])), .done)

def sync (s : Fs) (p : Path) : Except Error (Fs × Answer) :=
  match s.find p with
  | some (i, node) => .ok (s.set i node.sync, .done)
  | none => .error .notFound

/-- What `op` does when the operating system reports no error of its own (`Error.io`). -/
def apply (s : Fs) : Op → Except Error (Fs × Answer)
  | .read p => do let (_, f) ← s.fileAt p; return (s, .bytes f.data)
  | .write p offset bytes => s.changeFile p fun _ => .write offset bytes
  | .append p bytes => s.changeFile p fun f => .write f.data.length bytes
  | .create p => s.create p
  | .truncate p size => s.changeFile p fun _ => .truncate size
  | .mkdir p => s.mkdir p
  | .rename src dst => s.rename src dst
  | .delete p => s.delete p
  | .list p => do let (_, D) ← s.dirAt p; return (s, .names (sortNames (D.entries.map (·.1))))
  | .fsync p => s.sync p

/-- The file system after `op` and its answer. A call refused changes nothing. -/
def step (s : Fs) (op : Op) : Fs × Answer :=
  match s.apply op with
  | .ok r => r
  | .error e => (s, .failed e)

/-- The file system after `ops`, in order. -/
def run (s : Fs) (ops : List Op) : Fs := ops.foldl (fun s op => (s.step op).1) s

/-- What a crash leaves, given how far each inode's changes got (`Node.crash`). -/
def crash (s : Fs) (choice : Nat → Nat × Nat) : Fs :=
  { nodes := s.nodes.map fun (i, n) => (i, n.crash (choice i)) }

/-- Every file system a crash may leave. -/
def crashes (s : Fs) : List Fs :=
  (s.nodes.foldr (fun (i, n) rest => n.choices.flatMap fun ch => rest.map ((i, n.crash ch) :: ·))
    [[]]).map ({ nodes := · })

/-- What an `io` error from `op` may leave: the call not made, made, or anything between. A
write may be done in part; a rename, a create, a delete or a truncation is done or not; an
`fsync` may leave the inode as a crash would, and on the disk. -/
def failures (s : Fs) : Op → List Fs
  | .read _ | .list _ => [s]
  | .write p offset bytes => match s.fileAt p with
    | .ok (i, f) => s :: (List.range (bytes.length + 1)).map fun part =>
        s.set i (.file (f.change (.write offset (bytes.take part))))
    | .error _ => [s]
  | .append p bytes => match s.fileAt p with
    | .ok (i, f) => s :: (List.range (bytes.length + 1)).map fun part =>
        s.set i (.file (f.change (.write f.data.length (bytes.take part))))
    | .error _ => [s]
  | .fsync p => match s.find p with
    | some (i, n) => s :: n.choices.map fun ch => s.set i (n.crash ch)
    | none => [s]
  | op => [s, (s.step op).1]

end Fs

/-! Lookups after `put`, `set` and `crash`. -/

theorem lookup_filter_ne {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List (α × β)) (a b : α) :
    (l.filter (·.1 != a)).lookup b = if b = a then none else l.lookup b := by
  induction l with
  | nil => simp [List.lookup]
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : k = a
    · subst hk
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih]
      by_cases hb : b = k
      · simp [hb]
      · simp [hb, List.lookup, beq_eq_false_iff_ne.mpr hb]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hk, not_false_eq_true, ↓reduceIte,
        List.lookup, ih]
      by_cases hb : b = a
      · subst hb
        simp [beq_eq_false_iff_ne.mpr (Ne.symm hk)]
      · simp [hb]

@[simp] theorem lookup_put_self {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List (α × β)) (a : α)
    (v : Option β) : (put l a v).lookup a = v := by
  cases v <;> simp [put, lookup_filter_ne]

theorem lookup_put_ne {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List (α × β)) {a b : α}
    (v : Option β) (h : b ≠ a) : (put l a v).lookup b = l.lookup b := by
  cases v <;> simp [put, List.lookup, lookup_filter_ne, h, beq_eq_false_iff_ne.mpr h]

theorem put_put {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List (α × β)) (a : α) (v : β)
    (w : Option β) : put (put l a (some v)) a w = put l a w := by
  have hf : ((l.filter (·.1 != a)).filter (·.1 != a)) = l.filter (·.1 != a) := by
    rw [List.filter_filter]; simp
  cases w <;> simp [put, hf]

namespace Fs

@[simp] theorem node_set_self (s : Fs) (i : Nat) (n : Node) : (s.set i n).node i = some n := by
  simp [set, node]

theorem node_set_ne (s : Fs) {i j : Nat} (n : Node) (h : j ≠ i) : (s.set i n).node j = s.node j :=
  lookup_put_ne s.nodes (some n) h

@[simp] theorem set_set (s : Fs) (i : Nat) (n m : Node) : (s.set i n).set i m = s.set i m := by
  simp [set, put_put]

private theorem lt_fresh_of_lookup {l : List (Nat × Node)} {i : Nat} {n : Node}
    (h : l.lookup i = some n) : i < l.foldr (fun p m => max p.1 m) 0 + 1 := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons x xs ih =>
    simp only [List.lookup] at h
    split at h
    · next heq =>
      have := beq_iff_eq.mp heq
      simp only [List.foldr_cons]
      omega
    · simp only [List.foldr_cons]
      have := ih h
      omega

@[simp] theorem node_fresh (s : Fs) : s.node s.fresh = none := by
  cases h : s.node s.fresh with
  | none => rfl
  | some n => exact absurd (lt_fresh_of_lookup h) (Nat.lt_irrefl _)

theorem fresh_ne {s : Fs} {i : Nat} {n : Node} (h : s.node i = some n) : s.fresh ≠ i := by
  intro heq
  simp [← heq] at h

theorem node_crash (s : Fs) (c : Nat → Nat × Nat) (i : Nat) :
    (s.crash c).node i = (s.node i).map (·.crash (c i)) := by
  simp only [crash, node]
  induction s.nodes with
  | nil => simp [List.lookup]
  | cons x xs ih =>
    obtain ⟨k, n⟩ := x
    simp only [List.map_cons, List.lookup]
    split <;> simp_all

theorem entriesOf_set_ne (s : Fs) {i j : Nat} (n : Node) (h : j ≠ i) :
    (s.set i n).entriesOf j = s.entriesOf j := by
  simp [entriesOf, node_set_ne _ _ h]

/-- What `resolveFrom` reads is the entries of the directories on its way, and nothing else. -/
theorem resolveFrom_congr {s s' : Fs} {i : Nat} {p : Path}
    (h : ∀ j ∈ s.way i p, s'.entriesOf j = s.entriesOf j) :
    s'.resolveFrom i p = s.resolveFrom i p ∧ s'.way i p = s.way i p := by
  induction p generalizing i with
  | nil => simp [resolveFrom, way]
  | cons name rest ih =>
    have hc : s'.child i name = s.child i name := by
      simp only [child, h i (by simp [way])]
    simp only [resolveFrom, way, hc]
    cases hj : s.child i name with
    | none => simp
    | some j =>
      have := ih (i := j) fun k hk => h k (by simp [way, hj, hk])
      simp [this]

theorem resolveFrom_append (s : Fs) (i : Nat) (p q : Path) :
    s.resolveFrom i (p ++ q) = (s.resolveFrom i p).bind (s.resolveFrom · q) := by
  induction p generalizing i with
  | nil => simp [resolveFrom]
  | cons name rest ih =>
    simp only [List.cons_append, resolveFrom]
    cases s.child i name <;> simp [ih]

theorem find_child {s : Fs} {dir : Path} {d : Nat} (h : s.resolve dir = some d) (name : String) :
    s.find (dir ++ [name]) = (s.child d name).bind fun i => (s.node i).map (i, ·) := by
  simp only [find, resolve] at h ⊢
  rw [resolveFrom_append, h]
  simp only [Option.bind_some, resolveFrom]
  cases s.child d name <;> simp

/-- An inode with no change since its last `fsync` comes through a crash as it was. -/
theorem _root_.Lanes.FileSystem.Node.crash_of_synced_file {f : File} (h : f.pending = []) (ch : Nat × Nat) :
    (Node.file f).crash ch = .file f := by
  obtain ⟨synced, pending⟩ := f
  simp only at h
  subst h
  simp [Node.crash, File.survive, applyAll]

theorem _root_.Lanes.FileSystem.Node.crash_of_synced_dir {d : Dir} (h : d.pending = []) (ch : Nat × Nat) :
    (Node.dir d).crash ch = .dir d := by
  obtain ⟨synced, pending⟩ := d
  simp only at h
  subst h
  simp [Node.crash, Dir.survive]

theorem entriesOf_crash (s : Fs) (c : Nat → Nat × Nat) (i : Nat) :
    (s.crash c).entriesOf i = match s.node i with
      | some (.dir d) => some (d.survive (c i).1)
      | _ => none := by
  simp only [entriesOf, node_crash]
  cases s.node i with
  | none => rfl
  | some n => cases n <;> simp [Node.crash, Dir.entries]

theorem _root_.Lanes.FileSystem.Dir.survive_of_synced {D : Dir} (h : D.pending = []) (kept : Nat) :
    D.survive kept = D.synced := by
  simp [Dir.survive, h]

theorem _root_.Lanes.FileSystem.Dir.survive_all (D : Dir) : D.survive D.pending.length = D.entries := by
  simp [Dir.survive, Dir.entries]

@[simp] theorem _root_.Lanes.FileSystem.Dir.survive_sync (D : Dir) (kept : Nat) :
    D.sync.survive kept = D.entries := by
  simp [Dir.survive, Dir.sync]

theorem _root_.Lanes.FileSystem.Dir.entries_of_synced {D : Dir} (h : D.pending = []) : D.entries = D.synced := by
  simp [Dir.entries, h]

theorem _root_.Lanes.FileSystem.File.data_of_synced {f : File} (h : f.pending = []) : f.data = f.synced := by
  simp [File.data, applyAll, h]

theorem child_eq {s : Fs} {d : Nat} {D : Dir} (h : s.node d = some (.dir D)) (name : String) :
    s.child d name = D.entries.lookup name := by
  simp [child, entriesOf, h]

/-- The file at `p`, as a read sees it. -/
def fileData : Option Node → Option Bytes
  | some (.file f) => some f.data
  | _ => none

theorem read_child {s : Fs} {dir : Path} {d : Nat} {D : Dir} (hr : s.resolve dir = some d)
    (hd : s.node d = some (.dir D)) (name : String) :
    s.read (dir ++ [name]) = (D.entries.lookup name).bind fun i => fileData (s.node i) := by
  simp only [read, fileAt, find_child hr, child_eq hd]
  cases D.entries.lookup name with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    cases s.node i with
    | none => rfl
    | some n => cases n <;> rfl

theorem read_crash_child {s : Fs} {c : Nat → Nat × Nat} {dir : Path} {d : Nat} {D : Dir}
    (hr : (s.crash c).resolve dir = some d) (hd : s.node d = some (.dir D)) (name : String) :
    (s.crash c).read (dir ++ [name]) = ((D.survive (c d).1).lookup name).bind fun i =>
      fileData ((s.node i).map (·.crash (c i))) := by
  have hd' : (s.crash c).node d = some (.dir { synced := D.survive (c d).1 }) := by
    simp [node_crash, hd, Node.crash]
  rw [read_child hr hd']
  simp [Dir.entries, node_crash]

theorem _root_.Lanes.FileSystem.parentOf_append (dir : Path) (name : String) : parentOf (dir ++ [name]) = .ok (dir, name) := by
  simp [parentOf]

theorem find_dir {s : Fs} {dir : Path} {d : Nat} {D : Dir} (hr : s.resolve dir = some d)
    (hd : s.node d = some (.dir D)) : s.find dir = some (d, .dir D) := by
  simp [find, hr, hd]

theorem dirAt_dir {s : Fs} {dir : Path} {d : Nat} {D : Dir} (hr : s.resolve dir = some d)
    (hd : s.node d = some (.dir D)) : s.dirAt dir = .ok (d, D) := by
  simp [dirAt, find_dir hr hd]

theorem find_in {s : Fs} {dir : Path} {d : Nat} {D : Dir} (hr : s.resolve dir = some d)
    (hd : s.node d = some (.dir D)) (name : String) :
    s.find (dir ++ [name]) = (D.entries.lookup name).bind fun i => (s.node i).map (i, ·) := by
  rw [find_child hr, child_eq hd]

theorem _root_.Lanes.FileSystem.lookup_applyBatch_of_ne {entries : Entries} {batch : Batch} {name : String}
    (h : ∀ e ∈ batch, e.1 ≠ name) : (applyBatch entries batch).lookup name = entries.lookup name := by
  induction batch generalizing entries with
  | nil => rfl
  | cons e rest ih =>
    simp only [applyBatch, List.foldl_cons] at ih ⊢
    rw [ih fun e he => h e (List.mem_cons_of_mem _ he),
      lookup_put_ne _ _ (Ne.symm (h e List.mem_cons_self))]

theorem _root_.Lanes.FileSystem.lookup_batches_of_ne {entries : Entries} {batches : List Batch} {name : String}
    (h : ∀ b ∈ batches, ∀ e ∈ b, e.1 ≠ name) :
    (batches.foldl applyBatch entries).lookup name = entries.lookup name := by
  induction batches generalizing entries with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.foldl_cons]
    rw [ih fun b hb => h b (List.mem_cons_of_mem _ hb),
      lookup_applyBatch_of_ne (h b List.mem_cons_self)]

@[simp] theorem _root_.Lanes.FileSystem.lookup_applyBatch_concat (entries : Entries) (batch : Batch) (name : String)
    (v : Option Nat) : (applyBatch entries (batch ++ [(name, v)])).lookup name = v := by
  simp [applyBatch]

/-- `dir` names the directory `d`, and neither `d` nor a directory on the way to it has a change
to its entries that a crash could lose. The way does not pass through `d`. -/
structure SettledDir (s : Fs) (dir : Path) (d : Nat) (D : Dir) : Prop where
  resolve : s.resolve dir = some d
  node : s.node d = some (.dir D)
  synced : D.pending = []
  way : ∀ j ∈ s.way 0 dir, ∃ E : Dir, s.node j = some (.dir E) ∧ E.pending = []
  once : d ∉ s.way 0 dir

namespace SettledDir

variable {s s' : Fs} {dir : Path} {d : Nat} {D : Dir}

/-- What changes no inode on the way to `dir` leaves `dir` naming `d`. -/
theorem resolve_of_same (h : s.SettledDir dir d D) (hs : ∀ j ∈ s.way 0 dir, s'.node j = s.node j) :
    s'.resolve dir = some d := by
  have := (resolveFrom_congr (s := s) (s' := s') (i := 0) (p := dir) fun j hj => by
    simp [entriesOf, hs j hj]).1
  show s'.resolveFrom 0 dir = some d
  rw [this]
  exact h.resolve

/-- And so does a crash after it. -/
theorem resolve_crash (h : s.SettledDir dir d D) (hs : ∀ j ∈ s.way 0 dir, s'.node j = s.node j)
    (c : Nat → Nat × Nat) : (s'.crash c).resolve dir = some d := by
  have := (resolveFrom_congr (s := s) (s' := s'.crash c) (i := 0) (p := dir) fun j hj => by
    obtain ⟨E, hE, hp⟩ := h.way j hj
    rw [entriesOf_crash, hs j hj, hE]
    simp [entriesOf, hE, Dir.survive_of_synced hp, Dir.entries_of_synced hp]).1
  show (s'.crash c).resolveFrom 0 dir = some d
  rw [this]
  exact h.resolve

/-- What changes no inode on the way to `dir`, and leaves `d` a directory with nothing a crash
could lose, leaves `dir` settled. -/
theorem of_same (h : s.SettledDir dir d D) (hs : ∀ j ∈ s.way 0 dir, s'.node j = s.node j)
    {D' : Dir} (hd : s'.node d = some (.dir D')) (hp : D'.pending = []) :
    s'.SettledDir dir d D' := by
  have hway := (resolveFrom_congr (s := s) (s' := s') (i := 0) (p := dir) fun j hj => by
    simp [entriesOf, hs j hj]).2
  refine ⟨h.resolve_of_same hs, hd, hp, fun j hj => ?_, by rw [hway]; exact h.once⟩
  rw [hway] at hj
  rw [hs j hj]
  exact h.way j hj

end SettledDir

end Fs

/-! Every crash is one `crashes` lists, so a test that checks them all checks every crash. -/

namespace Node

/-- Arguments of `crash` past the end of what may be kept give the same as the last listed. -/
def clamp : Node → Nat × Nat → Nat × Nat
  | .file f, (kept, part) =>
    if kept < f.pending.length then (kept, min part ((f.pending[kept]?.map Change.size).getD 0))
    else (f.pending.length, 0)
  | .dir d, (kept, _) => (min kept d.pending.length, 0)

theorem torn_min (c : Change) (part : Nat) : c.torn (min part c.size) = c.torn part := by
  cases c with
  | write offset bytes =>
    simp only [Change.torn, Change.size, Change.write.injEq, true_and]
    rcases Nat.le_total part bytes.length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]
  | truncate => rfl

theorem crash_clamp (n : Node) (ch : Nat × Nat) : n.crash (n.clamp ch) = n.crash ch := by
  obtain ⟨kept, part⟩ := ch
  cases n with
  | file f =>
    simp only [clamp]
    split
    · next hk =>
      simp only [crash, File.survive, List.getElem?_eq_getElem hk, Option.map_some,
        Option.getD_some, torn_min]
    · next hk =>
      have hk : f.pending.length ≤ kept := by omega
      simp [crash, File.survive, List.take_of_length_le hk, List.getElem?_eq_none hk]
  | dir d =>
    simp only [clamp, crash, Dir.survive]
    rcases Nat.le_total kept d.pending.length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]

theorem clamp_mem (n : Node) (ch : Nat × Nat) : n.clamp ch ∈ n.choices := by
  obtain ⟨kept, part⟩ := ch
  cases n with
  | file f =>
    simp only [clamp, choices, List.mem_flatMap, List.mem_range, List.mem_map]
    split
    · next hk => exact ⟨kept, by omega, _, by omega, rfl⟩
    · exact ⟨f.pending.length, by omega, 0, by omega, rfl⟩
  | dir d =>
    simp only [clamp, choices, List.mem_map, List.mem_range]
    exact ⟨_, by omega, rfl⟩

end Node

theorem Fs.crash_mem_crashes (s : Fs) (c : Nat → Nat × Nat) : s.crash c ∈ s.crashes := by
  simp only [crash, crashes, List.mem_map]
  refine ⟨_, ?_, rfl⟩
  induction s.nodes with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨i, n⟩ := x
    simp only [List.map_cons, List.foldr_cons, List.mem_flatMap, List.mem_map]
    exact ⟨n.clamp (c i), Node.clamp_mem n (c i), _, ih, by rw [Node.crash_clamp]⟩

end Lanes.FileSystem
