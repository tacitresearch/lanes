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

/-- How long one exchange with a node may take. A node answers within its gate's deadline, 1.5 s,
if only with `504`. -/
def exchange_ms : Nat := 5000

/-- What a node sent before it closed the connection, or `none` if it could not be reached or had
not closed it after `deadline_ms`. The socket is closed whoever wins the race, which ends the
read that lost it. -/
def converse (port : UInt16) (method path body : String) (deadline_ms : Nat := exchange_ms) :
    Async (Option ByteArray) := do
  let socket ← try TCP.Socket.Client.mk catch _ => return none
  let attempt : Async (Option ByteArray) := do
    try
      socket.connect (.v4 ⟨.ofParts 127 0 0 1, port⟩)
      socket.send (s!"{method} {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n"
        ++ s!"Content-Type: text/plain\r\nContent-Length: {body.utf8ByteSize}\r\n\r\n{body}").toUTF8
      let mut received := ByteArray.empty
      repeat
        match ← socket.recv? 4096 with
        | some bytes => received := received ++ bytes
        | none => break
      return some received
    catch _ => return none
  let patience := (fun _ => (none : Option ByteArray)) <$> Async.sleep (.ofNat deadline_ms)
  try Async.race attempt patience
  finally try socket.close catch _ => pure ()

/-- A response is an answer only when all of it arrived: a node killed while it sends leaves a
status line that says `200` and less body than it announced. -/
def answer? (received : ByteArray) : Option (Nat × String) := do
  let response ← Http.Response.parse received
  return (response.status, ← String.fromUTF8? response.body)

/-- The status and body of one HTTP exchange, or `none` if the node did not answer by the
deadline. -/
def call (port : UInt16) (method path : String) (body : String := "")
    (deadline_ms : Nat := exchange_ms) : Async (Option (Nat × String)) :=
  return (← converse port method path body deadline_ms).bind answer?

abbrev Node := IO.Process.Child { stdin := .null, stdout := .piped, stderr := .inherit }

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

/-- The key the nodes share, in the environment `raftNode` reads it from. -/
def env : Array (String × Option String) :=
  #[("RAFT_KV_KEY", some "the key of the tests' raft nodes")]

def binary : IO System.FilePath :=
  return (← IO.appPath).parent.getD "." / "raftNode"

/-- The exit code of a `raftNode` that ends by itself within five seconds, as one that refuses
to start does. One that is still running then is killed. -/
def exitCode (args : Array String) : IO (Option UInt32) := do
  let child ← IO.Process.spawn
    { cmd := (← binary).toString, args, env, stdin := .null, stdout := .null, stderr := .null }
  for _ in [0:100] do
    if let some code ← child.tryWait then return some code
    IO.sleep 50
  child.kill
  discard child.wait
  return none

/-- Start node `k` and wait for the line it prints once it listens. `false` if it ended, or
printed nothing in ten seconds. -/
def spawn (c : Cluster) (k : Nat) (new : Bool := false) : IO (Cluster × Bool) := do
  let child : Node ← IO.Process.spawn
    { cmd := (← binary).toString, args := (if new then #["new"] else #[]) ++ c.args k, env
      stdin := .null, stdout := .piped, stderr := .inherit }
  let line ← IO.asTask (prio := .dedicated) child.stdout.getLine
  for _ in [0:500] do
    if ← IO.hasFinished line then break
    IO.sleep 20
  if (← IO.hasFinished line) && (line.get.toOption.any (·.startsWith "raft-kv node")) then
    return ({ c with nodes := c.nodes.set! k (some child) }, true)
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

/-- Three new nodes. Their ports are a guess, which another program on this machine may have
made too: when a node cannot have its own, the guess is made again. -/
def launch (name : String) (snapshotEvery : Nat) : IO (Option Cluster) := do
  for _ in [0:3] do
    let mut c ← Cluster.new name snapshotEvery
    let mut started := true
    for k in [0:3] do
      if started then
        let (next, listening) ← c.spawn k (new := true)
        c := next
        started := listening
    if started then return some c
    discard c.killAll
    IO.FS.removeDirAll c.dir
  return none

/-- How long a client goes on asking the nodes for one answer before it gives up. An answer has
taken up to 5 s with the machine idle and 10 s with four times as many busy threads as cores.
`raftProcs` gives up on at most ten requests before it ends, which keeps it within the 300 s
that `scripts/mutants.py` allows it. -/
def patience_ms : Nat := 20000

/-- Ask each running node in turn until one gives an answer `accept` takes, or `patience_ms` has
passed, which is said on the standard output. -/
def ask {α : Type} (c : Cluster) (method path body : String)
    (accept : Nat × String → Option α) : Async (Option (Nat × α)) := do
  let until_ms := (← IO.monoMsNow) + patience_ms
  repeat
    let last ← c.answered.get
    for k in last :: (List.range 3).filter (· != last) do
      let now_ms ← IO.monoMsNow
      if c.up k && now_ms < until_ms then
        let deadline_ms := min exchange_ms (until_ms - now_ms)
        if let some answer ← call (c.httpPort k) method path body deadline_ms then
          if let some a := accept answer then
            c.answered.set k
            return some (k, a)
    if (← IO.monoMsNow) + 250 ≥ until_ms then break
    Async.sleep 250
  IO.println s!"{method} {path}: no node answered in {patience_ms} ms"
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
