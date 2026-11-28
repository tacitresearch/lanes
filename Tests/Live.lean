/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
What the live tests share: a group of them run so that one that throws is a failure of its own,
a deadline, and scratch files.
-/

namespace Tests.Live

open Lanes Std Std.Async

def safely (name : String) (test : Async (List (String × Bool))) : IO (List (String × Bool)) := do
  try test.block
  catch e => return [(s!"{name}: threw {e}", false)]

def throws {α : Type} (action : Async α) : Async Bool := do
  try discard action; return false
  catch _ => return true

def within {α : Type} (ms : Nat) (action : Async α) : Async (Option α) :=
  Async.race (some <$> action) (do Async.sleep (.ofNat ms); return none)

/-- A path for a scratch file no other test uses. -/
def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  return s!"{dir}/lanes-{name}-{← IO.monoNanosNow}"

def remove (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then IO.FS.removeFile path

end Tests.Live
