/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.FileSystem.Replace

/-!
# The file system's calls, performed

`FileSystem.IO.perform root op` makes the call `op.map ByteArray.toList` of the model
(`Lanes/Outside/FileSystem/Basic.lean`) on the directory `root`, with Lean's `IO.FS` and the
calls it lacks bound in `native/lanes.c`: `fsync`, a write at an offset or at the end of a file
that is there, and a truncation. It decides nothing: an error is read back as the model's
`Error`, and anything the model does not name is `io`.

`FileSystem.IO.replace` runs `Replace.plan`, stopping at the first error, so what is proved of
the plan (`Replace.crash`, `Replace.failed`, `Replace.done`) holds of it as far as the operating
system keeps the model's assumptions (`TRUSTED.md`).
-/

public section

namespace Lanes.FileSystem.IO

/-- Wait until what was written to the file or directory at `path` is on the disk. -/
@[extern "lanes_fsync"]
opaque fsync (path : @& String) : IO Unit

/-- Write `bytes` at `offset`, or at the end when `append`, into the file at `path`, which must
be there. -/
@[extern "lanes_write_at"]
opaque writeAt (path : @& String) (append : Bool) (offset : UInt64) (bytes : @& ByteArray) :
  IO Unit

/-- Cut the file at `path`, or fill it with zeros, to `size` bytes. -/
@[extern "lanes_truncate"]
opaque truncate (path : @& String) (size : UInt64) : IO Unit

def pathOf (root : System.FilePath) (p : Path) : System.FilePath :=
  p.foldl (fun path name => path / System.FilePath.mk name) root

/-- The model's reading of an error. `EISDIR` and `ENOTDIR` have the same numbers on Linux and
macOS. -/
def errorOf : IO.Error → Error
  | .noFileOrDirectory .. => .notFound
  | .alreadyExists .. => .alreadyExists
  | .inappropriateType _ 21 _ => .isDir
  | .inappropriateType _ 20 _ => .notDir
  | .unsatisfiedConstraints .. => .notEmpty
  | .invalidArgument .. => .invalid
  | _ => .io

/-- A file, or else an empty directory: `unlink` refuses a directory (`EISDIR` on Linux, `EPERM`
on macOS), and then `rmdir` is asked. -/
private def remove (path : System.FilePath) : IO Unit := do
  match ← (IO.FS.removeFile path).toBaseIO with
  | .ok () => pure ()
  | .error e => if ← path.isDir then IO.FS.removeDir path else throw e

private def names (path : System.FilePath) : IO (List String) := do
  return sortNames ((← path.readDir).toList.map (·.fileName))

private def create (path : System.FilePath) : IO Unit := do
  let _ ← IO.FS.Handle.mk path .write

private def run (root : System.FilePath) : Op ByteArray → IO (Answer ByteArray)
  | .read p => return .bytes (← IO.FS.readBinFile (pathOf root p))
  | .write p offset bytes => do
    writeAt (pathOf root p).toString false offset.toUInt64 bytes; return .done
  | .append p bytes => do writeAt (pathOf root p).toString true 0 bytes; return .done
  | .create p => do create (pathOf root p); return .done
  | .truncate p size => do truncate (pathOf root p).toString size.toUInt64; return .done
  | .mkdir p => do IO.FS.createDir (pathOf root p); return .done
  | .rename src dst => do IO.FS.rename (pathOf root src) (pathOf root dst); return .done
  | .delete p => do remove (pathOf root p); return .done
  | .list p => return .names (← names (pathOf root p))
  | .fsync p => do fsync (pathOf root p).toString; return .done

/-- Make the call `op` in the directory `root`. -/
def perform (root : System.FilePath) (op : Op ByteArray) : IO (Answer ByteArray) := do
  match ← (run root op).toBaseIO with
  | .ok answer => return answer
  | .error e => return .failed (errorOf e)

/-- Replace the file `name` of the directory `dir` under `root` by `bytes` (`Replace.plan`). A
file `tmp` left by an earlier crash is removed first; any other error stops the plan and is
thrown. -/
def replace (root : System.FilePath) (dir : Path) (name tmp : String) (bytes : ByteArray) :
    IO Unit := do
  for op in Replace.plan dir name tmp bytes do
    match op, ← perform root op with
    | _, .failed .notFound => if !(op matches .delete _) then failed op .notFound
    | _, .failed e => failed op e
    | _, _ => pure ()
where
  failed (op : Op ByteArray) (e : Error) : IO Unit :=
    throw (IO.userError s!"replacing {pathOf root (dir ++ [name])}: {repr (op.map (·.size))} \
      failed: {repr e}")

end Lanes.FileSystem.IO
