/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Runtime

/-!
The journal's file. Which files are opened, what a file cut short gives, and what is refused
are `Lanes.Journal.open?`, a pure function with its theorems. Trusted here: locking, reading the
file, cutting off a write that did not finish, appending, and flushing.

A flush hands the bytes to the operating system, so a journal survives the death of the
process. Lean's `IO` has no `fsync`, so it does not yet survive loss of power.
-/

public section

namespace Lanes.Journal

variable {σ : Signature}

/-- Where a shard keeps its journal and how its inputs are written. -/
structure Store (σ : Signature) where
  path : System.FilePath
  input : Codec σ.In
  /-- The application's name for the system and the version of its step functions. A journal
  written under another name is refused. -/
  system : String := ""

private def Refusal.explain : Refusal → String
  | .foreign => "it is not a journal of this system"
  | .unreadable entry =>
    s!"entry {entry} is intact and cannot be read, so it was written with another codec"
  | .damaged byte => s!"it is damaged at byte {byte}"

private def cut (path : System.FilePath) (size : Nat) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .readWrite
  let mut left := size
  while left > 0 do
    let chunk ← handle.read (min left 65536).toUSize
    if chunk.isEmpty then throw (IO.userError s!"lanes: the journal {path} shrank while open")
    left := left - chunk.size
  handle.truncate

/--
Lock the journal, read it, and open it for appending. The lock is a file beside the journal and
is taken before anything is read, so a second process cannot start on a journal that another is
still writing. It is held until the log is closed.

A write that did not finish is cut off, since an entry appended after it could never be read,
and is kept beside the journal as `.cut`. A file that is damaged, or is another system's, or
was written with another codec, is refused and left as it is.
-/
def Store.open (store : Store σ) : IO (Log σ) := do
  let lock ← IO.FS.Handle.mk (store.path.addExtension "lock") .append
  unless ← lock.tryLock do
    throw (IO.userError s!"lanes: the journal {store.path} is in use by another process")
  try
    let bytes ← if ← store.path.pathExists then IO.FS.readBinFile store.path else pure .empty
    let (past, size) ← match open? store.input store.system bytes with
      | .ok found => pure found
      | .error refusal =>
        throw (IO.userError s!"lanes: the journal {store.path} is refused: {refusal.explain}")
    if size < bytes.size then
      IO.FS.writeBinFile (store.path.addExtension "cut") (bytes.extract size bytes.size)
      cut store.path size
    let handle ← IO.FS.Handle.mk store.path .append
    if size == 0 then
      unless Frame.fits (header store.system) do
        throw (IO.userError "lanes: the system's name is too long for a journal")
      handle.write (Frame.one (header store.system))
      handle.flush
    let write := fun (entries : List (Entry σ)) => do
      unless entries.all (Entry.fits store.input) do
        throw (IO.userError "lanes: an input is too large to journal")
      handle.write (encode store.input entries)
    return {
      past
      append := fun entries => do write entries; handle.flush
      note := write
      close := do handle.flush; lock.unlock }
  catch e =>
    lock.unlock
    throw e

end Lanes.Journal
