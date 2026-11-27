/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Runtime.IO.Shell
public import Lanes.Durable.Upgrade

/-!
The files of a journal. What they mean, which are refused, what a shard writes to them and in
what order are pure functions with their theorems (`Lanes/Durable/Disk.lean`): whenever the
process dies, the files it leaves load as the kernel it had. Trusted here: locking, reading the
two files, and that a write does what `Journal.Disk.apply` and `Journal.Disk.crash` say. That
is: bytes appended and flushed stay, an append that did not finish leaves some of its first
bytes and nothing else, and a rename replaces a file at once.

Every write that is flushed is also synced to the disk before the next begins (`fsync`, bound in
`native/lanes.c`): an append, a file written beside its target before it is renamed, and the
directory after the rename. So the files left by a loss of power are files the process could
have left by dying, and the theorems cover both.
-/

public section

namespace Lanes.Journal

variable {σ : Signature}

/-- Where a shard keeps its journal and how its inputs are written. -/
structure Store (sys : System σ) where
  path : System.FilePath
  input : Codec σ.In
  /-- The application's name for the system. A journal written under another name is refused. -/
  system : String := ""
  /-- The version of the system's types and step functions. The files carry it with the name
  (`Journal.label`); a file of version 0 carries the name alone, as every file did before
  there were versions. -/
  version : Nat := 0
  /-- The older versions this store reads, each with its system, its codecs and the migration
  from it (`Journal.Upgrade`). A start that finds the files of one migrates them and saves, so
  the store needs `actors`. -/
  upgrades : List (Upgrade sys) := []
  /-- How the actors are written down. With it the shard saves its kernel from time to time,
  beside the journal as `.snapshot`, and cuts the journal; without it the journal only grows. -/
  actors : Option (Kernel.Image.Codecs sys) := none
  /-- Whether a journal that is not there is begun. Without it a start that finds none is
  refused, which is what a shard that must not come back having forgotten needs. -/
  create : Bool := true

/-- A label as a person reads it: the name, then the version if there is one. -/
private def shown (label : String) : String :=
  label.replace "\nversion " ", version "

private def Refusal.explain (system : String) (upgrades : Bool) : Refusal → String
  | .foreign (some named) =>
    s!"it is the journal of \"{shown named}\", not of \"{shown system}\""
      ++ if upgrades then ", and no upgrade reads it" else ""
  | .foreign none => "it is not a journal"
  | .unreadable entry =>
    s!"entry {entry} is intact and cannot be read, so it was written with another codec"
  | .damaged byte => s!"it is damaged at byte {byte}"
  | .snapshot => "its snapshot cannot be read"
  | .apart => "it does not continue its snapshot"
  | .name => "the system's name is too long for a journal"
  | .missing => "it is not there, and this store may not begin one"

/-- Wait until what has been written to the file or directory at `path` is on the disk. -/
@[extern "lanes_fsync"]
opaque fsync (path : @& String) : IO Unit

private def syncDir (path : System.FilePath) : IO Unit :=
  fsync ((path.parent.getD ".").toString)

private def read? (path : System.FilePath) : IO (Option ByteArray) := do
  if ← path.pathExists then some <$> IO.FS.readBinFile path else pure none

private def replace (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let scratch := path.addExtension "tmp"
  IO.FS.writeBinFile scratch bytes
  fsync scratch.toString
  IO.FS.rename scratch path
  syncDir path

/-- One write, done as `Disk.apply` says. Without `flush` an append may be lost with the
process, and comes before whatever is appended after it. -/
private def perform (path : System.FilePath) (handle : IO.Ref IO.FS.Handle) (flush : Bool) :
    Write → IO Unit
  | .append bytes => do
    (← handle.get).write bytes
    if flush then
      (← handle.get).flush
      fsync path.toString
  | .putSnapshot bytes => replace (path.addExtension "snapshot") bytes
  | .putJournal bytes => do
    replace path bytes
    handle.set (← IO.FS.Handle.mk path .append)

/--
Lock the journal, read it, and open it for appending. The lock is a file beside the journal and
is taken before anything is read, so a second process cannot start on a journal that another is
still writing. It is held until the log is closed.

What the files give and whether they are refused is `Disk.begin`; a refused file is left as it
is. What is then written is `Disk.mend`, and a write that did not finish is kept beside the
journal as `.cut`; or, for the files of an older version, the migration's writes, which the
shard performs once it has handed over the old outputs (`Log.migrate`). A turn writes
`appendWrites` and a save `saveWrites`.
-/
def Store.open {sys : System σ} [Hashable σ.Id] (store : Store sys) : IO (Log sys) := do
  let system := label store.system store.version
  if !store.upgrades.isEmpty && store.actors.isNone then
    throw (IO.userError "lanes: a store that reads older versions needs the codecs of its actors")
  let lock ← IO.FS.Handle.mk (store.path.addExtension "lock") .append
  unless ← lock.tryLock do
    throw (IO.userError s!"lanes: the journal {store.path} is in use by another process")
  try
    let disk : Disk := { journal := (← read? store.path).getD .empty
                         snapshot := ← read? (store.path.addExtension "snapshot") }
    let begun ← match disk.begin store.input store.actors system store.create store.upgrades with
      | .ok begun => pure begun
      | .error refusal =>
        throw (IO.userError s!"lanes: the journal {store.path} is refused: \
          {refusal.explain system !store.upgrades.isEmpty}")
    let handle ← IO.mkRef (← IO.FS.Handle.mk store.path .append)
    let mut migrate : IO Unit := pure ()
    let mut pending : List σ.Out := []
    match begun with
    | .found found =>
      if found.size < disk.journal.size then
        IO.FS.writeBinFile (store.path.addExtension "cut")
          (disk.journal.extract found.size disk.journal.size)
      syncDir store.path
      (disk.mend system found.size).forM (perform store.path handle true)
    | .upgraded upgraded =>
      if let some actors := store.actors then
        unless (savedRecords actors system upgraded.index upgraded.image).all Frame.fits
            && Entry.fits store.input (.snapshot upgraded.index) do
          throw (IO.userError "lanes: an actor is too large to save")
      pending := upgraded.pending
      migrate := upgraded.writes.forM (perform store.path handle true)
    let found := begun.toFound
    let count ← IO.mkRef found.index
    let write := fun (flush : Bool) (entries : List (Entry σ)) => do
      unless entries.all (Entry.fits store.input) do
        throw (IO.userError "lanes: an input is too large to journal")
      (appendWrites store.input entries).forM (perform store.path handle flush)
      count.modify (· + entries.length)
    let save := fun (actors : Kernel.Image.Codecs sys) (image : Kernel.Image sys) => do
      let index ← count.get
      unless (savedRecords actors system index image).all Frame.fits
          && Entry.fits store.input (.snapshot index) do
        throw (IO.userError "lanes: an actor is too large to save")
      (saveWrites store.input actors system index image).forM
        (perform store.path handle true)
      count.modify (· + 1)
    return {
      past := found.past, saved := found.saved, index := found.index, pending, migrate
      append := write true
      note := write false
      save := store.actors.map save
      close := do (← handle.get).flush; lock.unlock }
  catch e =>
    lock.unlock
    throw e

end Lanes.Journal
