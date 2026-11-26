/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Three `raftNode` processes on this machine, for the tests that treat them as a client and an
operator would: HTTP in, signals, and the files they leave. `raftProcs` and `raftChaos` are
built on it, and need `raftNode` built beside them.
-/

namespace Harness

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

abbrev Node := IO.Process.Child { stdin := .null, stdout := .null, stderr := .inherit }

structure Cluster where
  dir : System.FilePath
  base : Nat
  /-- Small, so that a short test sees journals cut many times. -/
  snapshotEvery : Nat
  nodes : Array (Option Node) := #[none, none, none]
  /-- The node that answered last, asked first: another lets a request run into its deadline. -/
  answered : IO.Ref Nat

def Cluster.new (name : String) (snapshotEvery : Nat) : IO Cluster := do
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/{name}-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  return { dir, base := 20000 + (← IO.monoNanosNow) % 20000, snapshotEvery
           answered := ← IO.mkRef 0 }

namespace Cluster

def httpPort (c : Cluster) (k : Nat) : UInt16 := (c.base + k).toUInt16

def journal (c : Cluster) (k : Nat) : System.FilePath := c.dir / s!"node{k}.journal"

def snapshot (c : Cluster) (k : Nat) : System.FilePath := (c.journal k).addExtension "snapshot"

def up (c : Cluster) (k : Nat) : Bool := (c.nodes[k]?.join).isSome

/-- What `raftNode` is given for node `k`, after `new` if it is the node's first start. -/
def args (c : Cluster) (k : Nat) (journal : System.FilePath := c.journal k) : Array String :=
  #["--snapshot-every", toString c.snapshotEvery, toString k, toString (c.base + k),
      journal.toString]
    ++ (Array.range 3).map fun i => toString (c.base + 10 + i)

def binary : IO System.FilePath :=
  return (← IO.appPath).parent.getD "." / "raftNode"

/-- The exit code of a `raftNode` that ends by itself within five seconds, as one that refuses
to start does. One that is still running then is killed. -/
def exitCode (args : Array String) : IO (Option UInt32) := do
  let child ← IO.Process.spawn
    { cmd := (← binary).toString, args, stdin := .null, stdout := .null, stderr := .null }
  for _ in [0:100] do
    if let some code ← child.tryWait then return some code
    IO.sleep 50
  child.kill
  discard child.wait
  return none

/-- Start node `k` and wait until it listens. `false` if it ended, or did not listen in ten
seconds. -/
def spawn (c : Cluster) (k : Nat) (new : Bool := false) : IO (Cluster × Bool) := do
  let child : Node ← IO.Process.spawn
    { cmd := (← binary).toString, args := (if new then #["new"] else #[]) ++ c.args k
      stdin := .null, stdout := .null, stderr := .inherit }
  for _ in [0:500] do
    if (← child.tryWait).isSome then return (c, false)
    if (← (call (c.httpPort k) "GET" "/").block).isSome then
      return ({ c with nodes := c.nodes.set! k (some child) }, true)
    IO.sleep 20
  child.kill
  discard child.wait
  return (c, false)

def signal (c : Cluster) (k : Nat) (name : String) : IO Unit := do
  if let some (some child) := c.nodes[k]? then
    discard <| IO.Process.output { cmd := "kill", args := #[s!"-{name}", toString child.pid] }

/-- SIGKILL. -/
def kill (c : Cluster) (k : Nat) : IO Cluster := do
  if let some (some child) := c.nodes[k]? then
    child.kill
    discard child.wait
  return { c with nodes := c.nodes.set! k none }

def killAll (c : Cluster) : IO Cluster :=
  (List.range 3).foldlM kill c

/-- Ask each running node in turn, for a few seconds, until one gives an answer `accept` takes. -/
def ask {α : Type} (c : Cluster) (method path body : String)
    (accept : Nat × String → Option α) : Async (Option (Nat × α)) := do
  for _ in [0:12] do
    let last ← c.answered.get
    for k in last :: (List.range 3).filter (· != last) do
      if c.up k then
        if let some answer ← call (c.httpPort k) method path body then
          if let some a := accept answer then
            c.answered.set k
            return some (k, a)
    Async.sleep 250
  return none

/-- Write through whichever node answers. The node that did. -/
def put (c : Cluster) (key value : String) : Async (Option Nat) := do
  let answer ← c.ask "PUT" s!"/kv/{key}" value fun (status, _) =>
    if status == 200 then some () else none
  return answer.map (·.1)

/-- Read through whichever node answers: the value, or `none` for a key never written. `none`
outside if no node answered. -/
def get (c : Cluster) (key : String) : Async (Option (Option String)) := do
  let answer ← c.ask "GET" s!"/kv/{key}" "" fun (status, body) =>
    if status == 200 then some (some body)
    else if status == 404 && body == "no such key\n" then some none
    else none
  return answer.map (·.2)

end Cluster

/-- A signature for reading a journal's marks without knowing what its inputs are. -/
abbrev blind : Signature where
  Id := Unit
  Msg _ := Unit
  In := Unit

structure Shape where
  /-- How many entries of the node's history the file no longer holds: where it was last cut. -/
  cutAt : Nat := 0
  entries : Nat := 0
  bytes : Nat := 0

/-- A journal file begins with its header, and a cut one goes on with the mark of the save that
cut it. -/
def shape (file : ByteArray) : Shape :=
  match Frame.decode file with
  | _ :: first :: rest =>
    let cutAt := match Journal.Entry.ofBytes (σ := blind) Codec.unit first with
      | some (.snapshot index) => index
      | _ => 0
    { cutAt, entries := rest.length + 1, bytes := file.size }
  | _ => { bytes := file.size }

def Cluster.shape (c : Cluster) (k : Nat) : IO Shape :=
  return Harness.shape (← IO.FS.readBinFile (c.journal k))

def report (results : List (String × Bool)) : IO UInt32 := do
  for (name, ok) in results do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  let failed := results.countP (!·.2)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  (← IO.getStdout).flush
  IO.Process.exit (if failed == 0 then 0 else 1)

end Harness
