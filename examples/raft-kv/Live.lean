/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RaftKV

/-!
Three nodes on the runtime, joined by TCP on this machine, with real timers and a journal each.
A leader is elected, a write and a read are answered, the leader is stopped, the other two go
on, and the stopped node comes back from its snapshot and its journal and catches up. Run by
`lake exe raftLive`.
-/

open Lanes RaftKV Std Std.Async

structure Running where
  input : Request (Fin 3) Command → Async Unit
  state : Async (RaftKV.Node (Fin 3) Command (Std.ExtTreeMap Text Text))
  stop : Async Unit

def raftConfig (k : Fin 3) : Config :=
  { electionTimeout_ms := 150 + 80 * k.val, heartbeat_ms := 30 }

def start (dir : System.FilePath) (ports : IO.Ref (Array UInt16))
    (answers : IO.Ref (Array (Response Answer))) (k : Fin 3) (create : Bool := false) :
    Async Running := do
  let listen : Peers.Address := { port := (← ports.get)[k.val]?.getD 0 }
  let (rt, peers) ← startNode (n := 3)
    { self := k, raft := raftConfig k, listen
      home := fun i => return (← ports.get)[i.val]?.map fun port => { port }
      journal := some (dir / s!"node{k}.journal"), create
      key := "the key of the live test's nodes".toUTF8 }
    { snapshotEvery := 16 } fun answer => answers.modify (·.push answer)
  if (← ports.get).size ≤ k.val then ports.modify (·.push peers.port)
  return {
    input := fun x => rt.input (.inl x)
    state := rt.state k
    stop := do peers.stop; rt.stop }

/-- Ask until `found` answers, for at most `patience_ms`. -/
def await? {α : Type} (patience_ms : Nat) (found : Async (Option α)) : Async (Option α) := do
  for _ in [0:patience_ms / 20] do
    if let some a ← found then return some a
    Async.sleep 20
  return none

def leaderAmong (nodes : List (Fin 3 × Running)) : Async (Option (Fin 3)) := do
  let mut best : Option (Fin 3 × Nat) := none
  for (k, node) in nodes do
    let s ← node.state
    if isLeader s && (best.all fun (_, term) => term < s.term) then best := some (k, s.term)
  return best.map (·.1)

def answerTo (answers : IO.Ref (Array (Response Answer))) (req : ReqId) :
    Async (Option Answer) := do
  return ((← answers.get).find? (·.req == req)).map (·.res)

def run : Async (List (String × Bool)) := do
  let dir : System.FilePath :=
    s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/raft-live-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  let ports ← IO.mkRef #[]
  let answers ← IO.mkRef #[]
  let mut nodes : List (Fin 3 × Running) := []
  for k in List.finRange 3 do nodes := nodes ++ [(k, ← start dir ports answers k (create := true))]
  -- A node that is not the leader drops a request, and an entry a deposed leader appended may
  -- never commit, so a client sends again to the leader of the moment. A put of the same value
  -- and a get may take effect twice.
  let ask := fun (nodes : List (Fin 3 × Running)) (req : ReqId) (cmd : Command) => do
    for _ in [0:8] do
      let some leader ← await? 5000 (leaderAmong nodes) | return none
      if let some (_, node) := nodes.find? (·.1 == leader) then node.input ⟨req, leader, cmd⟩
      if let some a ← await? 1000 (answerTo answers req) then return some a
    return none
  let first ← await? 5000 (leaderAmong nodes)
  let wrote ← ask nodes 1 (.put "a" "1")
  let read ← ask nodes 2 (.get "a")
  let some old := first | return [("raft: a leader is elected", false)]
  if let some (_, node) := nodes.find? (·.1 == old) then node.stop
  let rest := nodes.filter (·.1 != old)
  let second ← await? 5000 (leaderAmong rest)
  let wroteAgain ← ask rest 3 (.put "a" "2")
  let readAgain ← ask rest 4 (.get "a")
  let saved ← (dir / s!"node{old}.journal.snapshot").pathExists
  let back ← start dir ports answers old
  let caughtUp ← await? 5000 do
    let s ← back.state
    return if s.applied ≥ 4 && s.machine["a"]? == some "2" then some s else none
  let states ← (rest.map (·.2) ++ [back]).mapM (·.state)
  for (_, node) in rest do node.stop
  back.stop
  IO.FS.removeDirAll dir
  return [
    ("raft: a leader is elected", first.isSome),
    ("raft: a write and a read through the leader are answered",
      wrote == some .ok && read == some (.value (some "1"))),
    ("raft: with the leader stopped, the other two elect one of themselves",
      second.isSome && second != first),
    ("raft: and go on answering", wroteAgain == some .ok && readAgain == some (.value (some "2"))),
    ("raft: the stopped node comes back from its snapshot and its journal and catches up",
      saved && caughtUp.isSome),
    ("raft: at the end the three logs agree on what is committed",
      states.all fun a => states.all fun b =>
        a.log.take (min a.commit b.commit) == b.log.take (min a.commit b.commit)) ]

def main : IO UInt32 := do
  let results ← run.block
  for (name, ok) in results do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
  let failed := results.countP (!·.2)
  IO.println s!"{results.length - failed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
