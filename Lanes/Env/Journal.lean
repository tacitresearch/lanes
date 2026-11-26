/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Runtime
public import Lanes.Actors.Snapshot

/-!
The journal's file. Which files are opened, what a file cut short gives, and what is refused
are `Lanes.Journal.open?`, a pure function with its theorems; so is what a snapshot file means
(`Lanes.Journal.saved?`). Trusted here: locking, reading the files, cutting off a write that did
not finish, appending, flushing, and the order in which a snapshot replaces the journal's past.

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

private def cut (path : System.FilePath) (size : Nat) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .readWrite
  let mut left := size
  while left > 0 do
    let chunk ← handle.read (min left 65536).toUSize
    if chunk.isEmpty then throw (IO.userError s!"lanes: the journal {path} shrank while open")
    left := left - chunk.size
  handle.truncate

private def replace (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let scratch := path.addExtension "tmp"
  IO.FS.writeBinFile scratch bytes
  IO.FS.rename scratch path

/--
Lock the journal, read it, and open it for appending. The lock is a file beside the journal and
is taken before anything is read, so a second process cannot start on a journal that another is
still writing. It is held until the log is closed.

A write that did not finish is cut off, since an entry appended after it could never be read,
and is kept beside the journal as `.cut`. A file that is damaged, or is another system's, or
was written with another codec, is refused and left as it is.

A save marks the journal, then puts the snapshot in place, then replaces the journal by one
that starts at the mark. The process may die between any two of these: the snapshot in place
always has its mark in the journal, which is what `Journal.resume` needs.
-/
def Store.open {sys : System σ} (store : Store sys) : IO (Log sys) := do
  let lock ← IO.FS.Handle.mk (store.path.addExtension "lock") .append
  unless ← lock.tryLock do
    throw (IO.userError s!"lanes: the journal {store.path} is in use by another process")
  try
    let bytes ← if ← store.path.pathExists then IO.FS.readBinFile store.path else pure .empty
    let (past, size) ← match open? store.input store.system bytes with
      | .ok found => pure found
      | .error refusal =>
        throw (IO.userError s!"lanes: the journal {store.path} is refused: {refusal.explain}")
    let snapshot := store.path.addExtension "snapshot"
    let saved ← match store.actors with
      | some actors =>
        if ← snapshot.pathExists then
          match saved? actors store.system (← IO.FS.readBinFile snapshot) with
          | some found => pure (some found)
          | none => throw (IO.userError s!"lanes: the snapshot {snapshot} is refused")
        else pure none
      | none => pure none
    if size < bytes.size then
      IO.FS.writeBinFile (store.path.addExtension "cut") (bytes.extract size bytes.size)
      cut store.path size
    let handle ← IO.mkRef (← IO.FS.Handle.mk store.path .append)
    if size == 0 then
      unless Frame.fits (header store.system) do
        throw (IO.userError "lanes: the system's name is too long for a journal")
      (← handle.get).write (Frame.one (header store.system))
      (← handle.get).flush
    let first := match past with
      | .snapshot index :: _ => index
      | _ => 0
    let count ← IO.mkRef (first + past.length)
    let write := fun (entries : List (Entry σ)) => do
      unless entries.all (Entry.fits store.input) do
        throw (IO.userError "lanes: an input is too large to journal")
      (← handle.get).write (encode store.input entries)
      count.modify (· + entries.length)
    let save := fun (actors : Kernel.Image.Codecs sys) (image : Kernel.Image sys) => do
      let index ← count.get
      unless (savedRecords actors store.system index image).all Frame.fits do
        throw (IO.userError "lanes: an actor is too large to save")
      write [.snapshot index]
      (← handle.get).flush
      replace snapshot (Journal.saved actors store.system index image)
      replace store.path (file store.input store.system [.snapshot index])
      handle.set (← IO.FS.Handle.mk store.path .append)
    return {
      past, saved
      index := first + past.length
      append := fun entries => do write entries; (← handle.get).flush
      note := write
      save := store.actors.map save
      close := do (← handle.get).flush; lock.unlock }
  catch e =>
    lock.unlock
    throw e

end Lanes.Journal
