/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Harness

/-!
Three `raftNode` processes under faults, for a minute by default:

    lake exe raftChaos [seconds] [seed]

Four clients write and read through whichever node they last had an answer from, while nodes
are killed with SIGKILL and started again, one or two at a time, and paused with SIGSTOP. The
nodes save their state every few entries, so they are killed in the middle of saves too, and
every start is from a snapshot and a cut journal.

Every operation is recorded with the times it was sent and answered. At the end every key is
read, and each read, those and the ones during the run, is held against the writes to its key:
the value was written, not after the read was answered, and no other write to the key was
acknowledged between that write's acknowledgement and the read being sent. A write that was
not answered may take effect at any time after it was sent, or never, so it excuses a read and
accuses none.

It takes a minute and its faults are random, so it is not part of `lake test`.
-/

open Lanes Std Std.Async Harness

structure Op where
  key : String
  write : Bool
  /-- What a write wrote, or what a read was answered: `none` for "no such key". -/
  value : Option String
  sent_ns : Nat
  /-- `none` for a write that was not answered. A read that was not answered is not recorded. -/
  answered_ns : Option Nat

def Op.answeredBefore (op : Op) (time_ns : Nat) : Bool :=
  op.answered_ns.any (· < time_ns)

/-- What is wrong with what `read` was answered, given the writes to its key. -/
def fault (writes : Array Op) (read : Op) : Option String :=
  let acknowledged := writes.filter (·.answered_ns.isSome)
  match read.value with
  | none =>
    if acknowledged.any (·.answeredBefore read.sent_ns) then
      some "no such key, after a write to it was acknowledged"
    else none
  | some value =>
    match writes.find? (·.value == some value) with
    | none => some "a value nobody wrote"
    | some write =>
      if read.answeredBefore write.sent_ns then some "a value before it was written"
      else if acknowledged.any fun later =>
          write.answeredBefore later.sent_ns && later.answeredBefore read.sent_ns then
        some "an older value, after a newer one was acknowledged"
      else none

section

def wrote (value : String) (sent_ns : Nat) (answered_ns : Option Nat) : Op :=
  { key := "k", write := true, value := some value, sent_ns, answered_ns }

def read (value : Option String) (sent_ns answered_ns : Nat) : Op :=
  { key := "k", write := false, value, sent_ns, answered_ns := some answered_ns }

#guard fault #[wrote "a" 1 (some 2), wrote "b" 3 (some 4)] (read (some "a") 5 6)
  == some "an older value, after a newer one was acknowledged"
#guard fault #[wrote "a" 1 (some 2), wrote "b" 3 (some 4)] (read none 5 6)
  == some "no such key, after a write to it was acknowledged"
#guard fault #[wrote "a" 1 (some 2), wrote "b" 3 (some 4)] (read (some "c") 5 6)
  == some "a value nobody wrote"
#guard fault #[wrote "a" 7 (some 8)] (read (some "a") 5 6) == some "a value before it was written"
#guard (fault #[wrote "a" 1 (some 2), wrote "b" 3 (some 4)] (read (some "b") 5 6)).isNone
#guard (fault #[wrote "a" 1 none, wrote "b" 3 (some 4)] (read (some "a") 5 6)).isNone
#guard (fault #[wrote "a" 1 (some 4), wrote "b" 3 (some 5)] (read (some "a") 6 7)).isNone
#guard (fault #[wrote "a" 1 (some 2), wrote "b" 3 (some 6)] (read (some "a") 5 7)).isNone
#guard (fault #[wrote "a" 1 none] (read none 5 6)).isNone

end

/-- Each client and the injuries have dice of their own, so a seed gives the same faults and the
same operations, though not at the same moments. -/
def dice (seed : Nat) : IO (Nat → Nat → BaseIO Nat) := do
  let gen ← IO.mkRef (mkStdGen seed)
  return fun lo hi => gen.modifyGet fun g => randNat g lo hi

/-- One exchange with a node, given up after three seconds. A response that began and did not
end is counted in `cut`: it is what a node killed while answering leaves, and no answer. -/
def exchange (c : Cluster) (cut : IO.Ref Nat) (node : Nat) (method key body : String) :
    Async (Option (Nat × String)) :=
  Async.race (do
      let some received ← converse (c.httpPort node) method s!"/kv/{key}" body | return none
      let answer := answer? received
      if answer.isNone && received.size > 0 then cut.modify (· + 1)
      return answer)
    (do Async.sleep 3000; return none)

/-- Half its operations are on four keys every client uses, half on keys of its own that are
written once. -/
def client (c : Cluster) (id until_ms : Nat) (roll : Nat → Nat → BaseIO Nat)
    (history : IO.Ref (Array Op)) (cut : IO.Ref Nat) : Async Unit := do
  let mut node := id % 3
  let mut count := 0
  while (← IO.monoMsNow) < until_ms do
    count := count + 1
    let shared := s!"shared{← roll 0 3}"
    let own := s!"client{id}-{← roll 1 count}"
    let choice ← roll 0 99
    let sent_ns ← IO.monoNanosNow
    if choice < 50 then
      let key := if choice < 25 then shared else s!"client{id}-{count}"
      let value := s!"{id}.{count}"
      let answer ← exchange c cut node "PUT" key value
      let now_ns ← IO.monoNanosNow
      let answered := answer.any (·.1 == 200)
      history.modify (·.push { key, write := true, value := some value, sent_ns
                               answered_ns := if answered then some now_ns else none })
      unless answered do node ← roll 0 2
    else
      let key := if choice < 75 then shared else own
      let read := fun (value : Option String) => do
        history.modify (·.push { key, write := false, value, sent_ns
                                 answered_ns := some (← IO.monoNanosNow) })
      match ← exchange c cut node "GET" key "" with
      | some (200, body) => read (some body)
      | some (404, "no such key\n") => read none
      | _ => node ← roll 0 2
    Async.sleep (.ofNat (← roll 0 20))

structure Faults where
  kills : Nat := 0
  pauses : Nat := 0
  /-- A node that did not start again: its journal was refused, or it did not listen. -/
  lost : Nat := 0

def revive (c : Cluster) (faults : Faults) (k : Nat) : IO (Cluster × Faults) := do
  let (c, started) ← c.spawn k
  return (c, if started then faults else { faults with lost := faults.lost + 1 })

/-- Until `until_ms`: a node is killed and started again a moment later, in three cases of ten
with a second node killed meanwhile, which leaves no majority; or a node is paused. -/
def injure (c : Cluster) (until_ms : Nat) (roll : Nat → Nat → BaseIO Nat) :
    IO (Cluster × Faults) := do
  let pause := fun (lo_ms hi_ms : Nat) => do IO.sleep (← roll lo_ms hi_ms).toUInt32
  let mut c := c
  let mut faults : Faults := {}
  while (← IO.monoMsNow) < until_ms do
    pause 50 1000
    let k ← roll 0 2
    if (← roll 0 99) < 60 then
      c ← c.kill k
      faults := { faults with kills := faults.kills + 1 }
      if (← roll 0 99) < 30 then
        let other := (k + 1 + (← roll 0 1)) % 3
        pause 0 300
        c ← c.kill other
        faults := { faults with kills := faults.kills + 1 }
        pause 0 800
        (c, faults) ← revive c faults other
      pause 0 1000
      (c, faults) ← revive c faults k
    else
      c.signal k "STOP"
      faults := { faults with pauses := faults.pauses + 1 }
      pause 200 2000
      c.signal k "CONT"
  return (c, faults)

def run (seconds seed : Nat) : IO (List (String × Bool)) := do
  let some c ← Cluster.launch "raft-chaos" 128
    | return [("chaos: three new nodes start", false)]
  let mut c := c
  let history ← IO.mkRef #[]
  let cut ← IO.mkRef 0
  let until_ms := (← IO.monoMsNow) + seconds * 1000
  let clients ← (List.range 4).mapM fun id => do
    (client c id until_ms (← dice (100 * seed + id + 1)) history cut).asTask
  let (injured, faults) ← injure c until_ms (← dice (100 * seed))
  c := injured
  for task in clients do task.block
  for k in [0:3] do
    unless c.up k do c := (← c.spawn k).1
  let running := (List.range 3).all c.up

  let during ← history.get
  let keys := (during.foldl (fun (keys : Std.TreeSet String) op => keys.insert op.key) {}).toList
  let mut final : Array Op := #[]
  let mut unread := 0
  for key in keys do
    let sent_ns ← IO.monoNanosNow
    match ← (c.get key).block with
    | some value =>
      final := final.push { key, write := false, value, sent_ns
                            answered_ns := some (← IO.monoNanosNow) }
    | none => unread := unread + 1
  let shapes ← (List.range 3).mapM c.shape
  c ← c.killAll

  let writes : Std.HashMap String (Array Op) := during.foldl (init := {}) fun writes op =>
    if op.write then writes.alter op.key fun ops => some ((ops.getD #[]).push op) else writes
  let faulty := fun (reads : Array Op) => reads.filterMap fun read =>
    (fault (writes.getD read.key #[]) read).map fun what =>
      s!"{read.key} read as {read.value}: {what}"
  let stale := faulty (during.filter (!·.write))
  let lostWrites := faulty final
  for line in (stale ++ lostWrites).toList.take 20 do IO.println s!"chaos: {line}"

  let acknowledged := (during.filter fun op => op.write && op.answered_ns.isSome).size
  let unanswered := (during.filter fun op => op.write && op.answered_ns.isNone).size
  IO.println (s!"chaos: {seconds} s with seed {seed}: {faults.kills} kills, {faults.pauses} "
    ++ s!"pauses; {acknowledged} writes acknowledged, {unanswered} not answered, "
    ++ s!"{during.size - acknowledged - unanswered} reads answered, {keys.length} keys; "
    ++ s!"{← cut.get} answers cut short by a node's death")
  IO.println (s!"chaos: at the end the journals are cut at entries {shapes.map (·.cutAt)} and "
    ++ s!"hold {shapes.map (·.entries)} entries, {shapes.map (·.bytes)} bytes")
  if stale.isEmpty && lostWrites.isEmpty && faults.lost == 0 && running && unread == 0 then
    IO.FS.removeDirAll c.dir
  else IO.println s!"chaos: the nodes' files are kept in {c.dir}"
  return [
    ("chaos: nodes were killed and paused, and writes were acknowledged meanwhile",
      faults.kills > 0 && faults.pauses > 0 && acknowledged ≥ 100),
    ("chaos: a node that was killed started again, every time, from a snapshot and a cut journal",
      faults.lost == 0 && running && shapes.all (·.cutAt > 0)),
    ("chaos: at the end every key is answered", unread == 0),
    ("chaos: every acknowledged write is there at the end, and no key has a value older than "
      ++ "one acknowledged after it", lostWrites.isEmpty),
    ("chaos: no read during the run was answered with a value nobody wrote, or with one older "
      ++ "than a write acknowledged before the read was sent", stale.isEmpty) ]

def main (args : List String) : IO UInt32 := do
  let seconds := (args[0]?.bind String.toNat?).getD 60
  let seed := (args[1]?.bind String.toNat?).getD ((← IO.monoNanosNow) % 1000000)
  report (← run seconds seed)
