/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Three nodes as three processes (`raftNode`), talked to over HTTP like any client would. The
leader is killed with SIGKILL, twice, and brought back from its journal in between, so the
second leader's death leaves a majority only if the first came back with what it had. Run by
`lake exe raftProcs`, which needs `raftNode` built beside it.
-/

open Lanes Std Std.Async

/-- The status and body of one HTTP exchange, or `none` if the node did not answer. -/
def call (port : UInt16) (method path : String) (body : String := "") :
    Async (Option (Nat × String)) := do
  try
    let socket ← TCP.Socket.Client.mk
    socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
    socket.send (s!"{method} {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n"
      ++ s!"Content-Type: text/plain\r\nContent-Length: {body.utf8ByteSize}\r\n\r\n{body}").toUTF8
    let mut received := ByteArray.empty
    repeat
      match ← socket.recv? 4096 with
      | some bytes => received := received ++ bytes
      | none => break
    socket.close
    let text := (String.fromUTF8? received).getD ""
    let status := ((text.splitOn " ")[1]?.bind String.toNat?).getD 0
    return some (status, ((text.splitOn "\r\n\r\n")[1]?).getD "")
  catch _ => return none

structure Cluster where
  dir : System.FilePath
  base : Nat
  nodes : Array (Option (IO.Process.Child { stdout := .piped }))

def httpPort (c : Cluster) (k : Nat) : UInt16 := (c.base + k).toUInt16

def spawn (c : Cluster) (k : Nat) : IO Cluster := do
  let node := (← IO.appPath).parent.getD "." / "raftNode"
  let child ← IO.Process.spawn {
    cmd := node.toString
    args := #[toString k, toString (c.base + k), (c.dir / s!"node{k}.journal").toString]
      ++ (Array.range 3).map fun i => toString (c.base + 10 + i)
    stdout := .piped }
  discard child.stdout.getLine
  return { c with nodes := c.nodes.set! k (some child) }

def kill (c : Cluster) (k : Nat) : IO Cluster := do
  if let some (some child) := c.nodes[k]? then
    child.kill
    discard child.wait
  return { c with nodes := c.nodes.set! k none }

/-- Write through whichever node answers, trying each in turn for a few seconds. -/
def put (c : Cluster) (key value : String) : Async (Option Nat) := do
  for _ in [0:8] do
    for k in [0:3] do
      if (c.nodes[k]?.join).isSome then
        if let some (200, _) ← call (httpPort c k) "PUT" s!"/kv/{key}" value then return some k
    Async.sleep 300
  return none

def get (c : Cluster) (key : String) : Async (Option String) := do
  for _ in [0:8] do
    for k in [0:3] do
      if (c.nodes[k]?.join).isSome then
        if let some (200, value) ← call (httpPort c k) "GET" s!"/kv/{key}" then return some value
    Async.sleep 300
  return none

def run : IO (List (String × Bool)) := do
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/raft-procs-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let mut c : Cluster := { dir, base := 20000 + (← IO.monoNanosNow) % 20000, nodes := #[none, none, none] }
  for k in [0:3] do c ← spawn c k
  let first ← (put c "a" "1").block
  let readA ← (get c "a").block
  let some leader := first | return [("procs: a leader answers a write", false)]
  c ← kill c leader
  let second ← (put c "b" "2").block
  let afterFirstDeath ← (do return (← get c "a", ← get c "b") : Async _).block
  c ← spawn c leader
  let some next := second | return [("procs: the other two go on", false)]
  IO.sleep 1500
  c ← kill c next
  let third ← (put c "c" "3").block
  let all ← (do return [← get c "a", ← get c "b", ← get c "c"] : Async _).block
  for k in [0:3] do c ← kill c k
  IO.FS.removeDirAll dir
  return [
    ("procs: a leader answers a write and a read over HTTP", first.isSome && readA == some "1"),
    ("procs: with the leader killed, another node answers, with what was written before",
      second.isSome && second != first && afterFirstDeath == (some "1", some "2")),
    ("procs: with the second leader killed too, the first one back from its journal makes a "
      ++ "majority that has everything",
      third.isSome && third != second && all == [some "1", some "2", some "3"]) ]

def main : IO UInt32 := do
  let results ← run
  for (name, ok) in results do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  let failed := results.countP (!·.2)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  (← IO.getStdout).flush
  IO.Process.exit (if failed == 0 then 0 else 1)
