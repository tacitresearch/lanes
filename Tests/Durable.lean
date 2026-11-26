/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-!
A durable shard: the bank with a journal. It is stopped and started, its journal is cut short,
and a child process running it is killed with SIGKILL in the middle of its work. Each time the
shard comes back in the state its journal describes, with nothing it had acknowledged missing.
-/

namespace Tests.Durable

open Lanes Std Std.Async Examples.Bank

abbrev Bank3 := bank (Fin 3) 100

def store (path : System.FilePath) : Journal.Store (sig (Fin 3)) :=
  { path, input := Request.codec Codec.fin }

def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.getEnv "TMPDIR").getD "/tmp"
  return s!"{dir}/lanes-{name}-{← IO.monoNanosNow}.journal"

def balances (rt : Runtime Bank3) : Async (List Int) :=
  (List.finRange 3).mapM fun a => return (← rt.state a).balance

def start (path : System.FilePath) (seen : IO.Ref (Array Nat)) : Async (Runtime Bank3) := do
  Runtime.start Bank3 {} (fun out => seen.modify (·.push out.req)) (some (← (store path).open))

def restartTest : Async (List (String × Bool)) := do
  let path ← scratch "restart"
  let first ← IO.mkRef #[]
  let rt ← start path first
  for n in [0:20] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  let before ← balances rt
  rt.stop
  let second ← IO.mkRef #[]
  let rt ← start path second
  rt.idle
  let after ← balances rt
  rt.input (.transfer ⟨100, 1, 2, 5⟩)
  rt.idle
  let later ← balances rt
  rt.stop
  IO.FS.removeFile path
  return [
    ("durable: a shard started again from its journal is in the state it was in",
      before == [40, 160, 100] && after == before),
    ("durable: outputs already handed over are not handed over again",
      (← first.get).size == 20 && (← second.get) == #[100]),
    ("durable: it goes on from there", later == [40, 155, 105]) ]

/-- Cut the journal at `keep` bytes, as a write torn by a crash would, start on it, do one more
transfer, and start once more. -/
def torn (file : ByteArray) (keep : Nat) : Async Bool := do
  let path ← scratch s!"torn{keep}"
  IO.FS.writeBinFile path (file.extract 0 keep)
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  rt.idle
  let recovered ← balances rt
  rt.input (.transfer ⟨500, 2, 0, 7⟩)
  rt.idle
  rt.stop
  let rt ← start path seen
  rt.idle
  let again ← balances rt
  rt.stop
  IO.FS.removeFile path
  let moved := 100 - recovered[0]!
  return recovered.sum == 300 && moved % 3 == 0 && moved ≤ 60 && recovered[1]! == 100 + moved
    && again == [recovered[0]! + 7, recovered[1]!, recovered[2]! - 7]

def tornTest : Async (List (String × Bool)) := do
  let path ← scratch "whole"
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  for n in [0:20] do rt.input (.transfer ⟨n, 0, 1, 3⟩)
  rt.idle
  rt.stop
  let file ← IO.FS.readBinFile path
  IO.FS.removeFile path
  let cuts := [0, 1, 9, file.size / 3, file.size / 2, file.size - 9, file.size - 1, file.size]
  let results ← cuts.mapM (torn file)
  return [("durable: a journal cut anywhere recovers a state it passed through, and what is "
    ++ "written after the cut is kept", results.all (·))]

/-- Run by `lanesTest journal-child path`: a bank that works until it is killed, and says on
standard output which requests it has answered. -/
def child (path : System.FilePath) : IO Unit := do
  let out ← IO.getStdout
  let work : Async Unit := do
    let rt ← Runtime.start Bank3 {} (fun response => do
      out.putStrLn (toString response.req)
      out.flush) (some (← (store path).open))
    for n in [0:1000000] do
      rt.input (.transfer ⟨n, Fin.ofNat 3 n, Fin.ofNat 3 (n + 1), 1⟩)
  work.block

def killTest : Async (List (String × Bool)) := do
  let path ← scratch "kill"
  let process ← IO.Process.spawn {
    cmd := (← IO.appPath).toString, args := #["journal-child", path.toString], stdout := .piped }
  let mut acknowledged : Array Nat := #[]
  for _ in [0:300] do
    if let some req := (← process.stdout.getLine).trimAscii.toString.toNat? then
      acknowledged := acknowledged.push req
  process.kill
  discard process.wait
  let log ← (store path).open
  let replayed := (Kernel.boot Bank3).1.exec (Journal.ops log.past)
  let answered := replayed.outputs.map (·.req)
  log.close
  let seen ← IO.mkRef #[]
  let rt ← start path seen
  rt.idle
  let recovered ← balances rt
  rt.stop
  IO.FS.removeFile path
  return [
    ("durable: after SIGKILL, every request the bank had answered is in its journal",
      acknowledged.size == 300 && acknowledged.all (answered.contains ·)),
    ("durable: after SIGKILL, the bank comes back in the state the journal describes",
      recovered.sum == 300
        && recovered == (List.finRange 3).map fun a => (replayed.kernel.cell a).state.balance) ]

def tests : IO (List (String × Bool)) := do
  return (← restartTest.block) ++ (← tornTest.block) ++ (← killTest.block)

end Tests.Durable
