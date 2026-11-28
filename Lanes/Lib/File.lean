/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.IO.FileSystem

/-!
A file replaced whole, so that it survives a loss of power: written beside its target, synced,
renamed over it, and its directory synced. It runs `Replace.plan`, which is proved against the
file system model (`Lanes/Outside/FileSystem/Replace.lean`), through the binding
`Lanes/Outside/IO/FileSystem.lean` (`TRUSTED.md`).
-/

public section

namespace Lanes.File

export Lanes.FileSystem.IO (fsync)

/-- Replace the file at `path` with `text`: when this returns, the file holds `text`, and a death
or a loss of power at any moment leaves it holding either `text` or what it held before
(`Replace.crash`, `Replace.failed`). The new bytes are written to `path` with the extension
`.tmp` first. -/
def replace (path : System.FilePath) (text : String) : IO Unit := do
  let some name := path.fileName | throw (IO.userError s!"{path} names no file")
  FileSystem.IO.replace (path.parent.getD ".") [] name (name ++ ".tmp") text.toUTF8

end Lanes.File
