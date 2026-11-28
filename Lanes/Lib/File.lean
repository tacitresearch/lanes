/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
A file replaced whole, so that it survives a loss of power: written beside its target, synced,
renamed over it, and its directory synced. `fsync` is the operating system's, bound in
`native/lanes.c` (`TRUSTED.md`).
-/

public section

namespace Lanes.File

/-- Wait until what was written to the file or directory at `path` is on the disk. -/
@[extern "lanes_fsync"]
opaque fsync (path : @& String) : IO Unit

/-- Replace the file at `path` with `text`: when this returns, the file holds `text`, and a death
or a loss of power at any moment leaves it holding either `text` or what it held before. -/
def replace (path : System.FilePath) (text : String) : IO Unit := do
  let scratch := path.addExtension "tmp"
  IO.FS.writeFile scratch text
  fsync scratch.toString
  IO.FS.rename scratch path
  fsync ((path.parent.getD ".").toString)

end Lanes.File
