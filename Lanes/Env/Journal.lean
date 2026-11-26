/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Runtime
public import Lanes.Actors.Disk

/-!
The files of a journal. What they mean, which are refused, what a shard writes to them and in
what order are pure functions with their theorems (`Lanes/Actors/Disk.lean`): whenever the
process dies, the files it leaves load as the kernel it had. Trusted here: locking, reading the
two files, and that a write does what `Journal.Disk.apply` and `Journal.Disk.crash` say. That
is: bytes appended and flushed stay, an append that did not finish leaves some of its first
bytes and nothing else, and a rename replaces a file at once.

A flush hands the bytes to the operating system, so a journal survives the death of the
process. Lean's `IO` has no `fsync`, so it does not yet survive loss of power.
-/

public section

namespace Lanes.Journal

variable {σ : Signature}

/-- Where a shard keeps its journal and how its inputs are written. -/
structure Store (sys : System σ) where
  path : System.FilePath
  input : Codec σ.In
  /-- The application's name for the system and the version of its step functions. A journal
  written under another name is refused. -/
  system : String := ""
  /-- How the actors are written down. With it the shard saves its kernel from time to time,
  beside the journal as `.snapshot`, and cuts the journal; without it the journal only grows. -/
  actors : Option (Kernel.Image.Codecs sys) := none

private def Refusal.explain : Refusal → String
  | .foreign => "it is not a journal of this system"
  | .unreadable entry =>
    s!"entry {entry} is intact and cannot be read, so it was written with another codec"
  | .damaged byte => s!"it is damaged at byte {byte}"
  | .snapshot => "its snapshot cannot be read"
  | .apart => "it does not continue its snapshot"
  | .name => "the system's name is too long for a journal"

private def read? (path : System.FilePath) : IO (Option ByteArray) := do
  if ← path.pathExists then some <$> IO.FS.readBinFile path else pure none

private def replace (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let scratch := path.addExtension "tmp"
  IO.FS.writeBinFile scratch bytes
  IO.FS.rename scratch path

/-- One write, done as `Disk.apply` says. Without `flush` an append may be lost with the
process, and comes before whatever is appended after it. -/
private def perform (path : System.FilePath) (handle : IO.Ref IO.FS.Handle) (flush : Bool) :
    Write → IO Unit
  | .append bytes => do
    (← handle.get).write bytes
    if flush then (← handle.get).flush
  | .putSnapshot bytes => replace (path.addExtension "snapshot") bytes
  | .putJournal bytes => do
    replace path bytes
    handle.set (← IO.FS.Handle.mk path .append)

/--
Lock the journal, read it, and open it for appending. The lock is a file beside the journal and
is taken before anything is read, so a second process cannot start on a journal that another is
still writing. It is held until the log is closed.

What the files give and whether they are refused is `Disk.read`; a refused file is left as it
is. What is then written is `Disk.mend`, and a write that did not finish is kept beside the
journal as `.cut`. A turn writes `appendWrites` and a save `saveWrites`.
-/
def Store.open {sys : System σ} (store : Store sys) : IO (Log sys) := do
  let lock ← IO.FS.Handle.mk (store.path.addExtension "lock") .append
  unless ← lock.tryLock do
    throw (IO.userError s!"lanes: the journal {store.path} is in use by another process")
  try
    let disk : Disk := { journal := (← read? store.path).getD .empty
                         snapshot := ← read? (store.path.addExtension "snapshot") }
    let found ← match disk.read store.input store.actors store.system with
      | .ok found => pure found
      | .error refusal =>
        throw (IO.userError s!"lanes: the journal {store.path} is refused: {refusal.explain}")
    if found.size < disk.journal.size then
      IO.FS.writeBinFile (store.path.addExtension "cut")
        (disk.journal.extract found.size disk.journal.size)
    let handle ← IO.mkRef (← IO.FS.Handle.mk store.path .append)
    (disk.mend store.system found.size).forM (perform store.path handle true)
    let count ← IO.mkRef found.index
    let write := fun (flush : Bool) (entries : List (Entry σ)) => do
      unless entries.all (Entry.fits store.input) do
        throw (IO.userError "lanes: an input is too large to journal")
      (appendWrites store.input entries).forM (perform store.path handle flush)
      count.modify (· + entries.length)
    let save := fun (actors : Kernel.Image.Codecs sys) (image : Kernel.Image sys) => do
      let index ← count.get
      unless (savedRecords actors store.system index image).all Frame.fits
          && Entry.fits store.input (.snapshot index) do
        throw (IO.userError "lanes: an actor is too large to save")
      (saveWrites store.input actors store.system index image).forM
        (perform store.path handle true)
      count.modify (· + 1)
    return {
      past := found.past, saved := found.saved, index := found.index
      append := write true
      note := write false
      save := store.actors.map save
      close := do (← handle.get).flush; lock.unlock }
  catch e =>
    lock.unlock
    throw e

end Lanes.Journal
