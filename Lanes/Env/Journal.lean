/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Runtime

/-!
The journal's file. What a file means, and that a cut file reads as a prefix, is proved in
`Lanes.Journal`. Trusted here: reading the file at start, appending to it, and flushing.

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

/--
Read the journal, leave on disk exactly the entries read, and open it for appending. A torn or
damaged tail is cut off here, not left in place: an entry appended after it could never be
read. The file is locked until the log is closed, so two shards cannot share a journal.
-/
def Store.open (store : Store σ) : IO (Log σ) := do
  let file ← if ← store.path.pathExists then IO.FS.readBinFile store.path else pure .empty
  let past := decode store.input file
  let clean := encode store.input past
  if clean != file then
    let scratch := store.path.withExtension "tmp"
    IO.FS.writeBinFile scratch clean
    IO.FS.rename scratch store.path
  let handle ← IO.FS.Handle.mk store.path .append
  unless ← handle.tryLock do
    throw (IO.userError s!"lanes: the journal {store.path} is in use by another process")
  let write := fun (entries : List (Entry σ)) => do
    unless entries.all (Entry.fits store.input) do
      throw (IO.userError "lanes: an input is too large to journal")
    handle.write (encode store.input entries)
  return {
    past
    append := fun entries => do write entries; handle.flush
    note := write
    close := do handle.flush; handle.unlock }

end Lanes.Journal
