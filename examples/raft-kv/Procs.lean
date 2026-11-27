/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Harness

/-!
Three nodes as three processes (`raftNode`), talked to over HTTP like any client would, saving
their state every few entries so that their journals are cut many times. Run by
`lake exe raftProcs`, which needs `raftNode` built beside it.

- Writes go on while the journals are cut, and a journal stays a few entries long.
- All three are killed with SIGKILL and come back from a snapshot and a cut journal, two at a
  time. Each pair must answer with everything that was acknowledged, which is so only if two
  of the three nodes each have all of it.
- The leader is killed, twice, and brought back in between, so the second leader's death
  leaves a majority only if the first came back with what it had.
- A node is not started without its journal, nor as new on one.

A request no node answers in `patience_ms` ends the test with the check it was for failed, so a
lost message is a failure in bounded time, not a test that waits for ever.
-/

open Lanes Std Std.Async Harness

def snapshotEvery : Nat := 64
def writes : Nat := 300

def key (i : Nat) : String := s!"k{i}"
def value (i : Nat) : String := s!"v{i}"

/-- Whether every `step`th of the writes, and the last, reads back. -/
def reads (c : Cluster) (step : Nat) : Async Bool := do
  for i in (List.range writes).filter fun i => i % step == 0 || i + 1 == writes do
    if (← c.get (key i)) != some (some (value i)) then return false
  return true

/-- A step the rest of the test needs did not happen: the nodes are killed, their files removed,
and `check` fails. A client gives up on a request after `patience_ms`, so a lost message ends
the test, as a failure, in a bounded time. -/
def abandon (c : Cluster) (check : String) : IO (List (String × Bool)) := do
  discard c.killAll
  IO.FS.removeDirAll c.dir
  return [(check, false)]

def start (c : Cluster) (nodes : List Nat) : IO (Cluster × Bool) := do
  let mut c := c
  let mut all := true
  for k in nodes do
    let (next, started) ← c.spawn k
    c := next
    all := all && started
  return (c, all)

def run : IO (List (String × Bool)) := do
  let some c ← Cluster.launch "raft-procs" snapshotEvery
    | return [("procs: three new nodes start", false)]
  let mut c := c
  let firstCheck :=
    "procs: three new nodes start, and a leader answers a write and a read over HTTP"
  let some _ ← (c.put "a" "1").block
    | abandon c s!"{firstCheck}: no node answered the first write"
  let readA ← (c.get "a").block

  let writtenCheck := s!"procs: {writes} writes are answered while every node saves its state "
    ++ s!"and cuts its journal, at least eight times, and no journal is left longer than "
    ++ s!"{8 * snapshotEvery} entries"
  for i in [0:writes] do
    if (← (c.put (key i) (value i)).block).isNone then
      return ← abandon c s!"{writtenCheck}: no node answered write {i}"
  let shapes ← (List.range 3).mapM c.shape
  let saved ← (List.range 3).allM fun k => (c.snapshot k).pathExists
  IO.println (s!"procs: after {writes} writes the journals are cut at entries "
    ++ s!"{shapes.map (·.cutAt)} and hold {shapes.map (·.entries)} entries, "
    ++ s!"{shapes.map (·.bytes)} bytes")

  c ← c.killAll
  let cut ← (List.range 3).mapM c.shape
  let mut pairs := []
  for pair in [[0, 1], [1, 2], [0, 2]] do
    let (next, back) ← start c pair
    pairs := pairs ++ [back && (← (reads next 7).block)]
    c ← next.killAll
  let (next, back) ← start c [0, 1, 2]
  c := next
  let all ← (reads c 1).block

  let leader ← (c.put "b" "2").block
  let some old := leader | abandon c "procs: a leader answers a write"
  c ← c.kill old
  let second ← (c.put "c" "3").block
  let some next := second
    | abandon c "procs: with the leader killed, another node answers a write"
  let afterFirstDeath ← (do return (← c.get "a", ← c.get "c") : Async _).block
  let (started, returned) ← c.spawn old
  c := started
  IO.sleep 1500
  c ← c.kill next
  let third ← (c.put "d" "4").block
  let some _ := third
    | abandon c "procs: with the second leader killed too, a write is answered"
  let last ← (do return [← c.get "a", ← c.get "b", ← c.get "c", ← c.get "d"] : Async _).block
  c ← c.killAll

  let nowhere := c.dir / "mistyped.journal"
  let absent ← Cluster.exitCode (c.args 0 nowhere)
  let made ← nowhere.pathExists
  let before ← IO.FS.readBinFile (c.journal 0)
  let again ← Cluster.exitCode (#["new"] ++ c.args 0)
  let kept := before == (← IO.FS.readBinFile (c.journal 0))
  IO.FS.removeDirAll c.dir
  return [
    (firstCheck, readA == some (some "1")),
    (writtenCheck, saved && shapes.all fun s =>
        s.cutAt ≥ 8 * snapshotEvery && s.entries ≤ 8 * snapshotEvery),
    ("procs: killed, each node leaves a snapshot and a journal that begins at its mark",
      cut.all (·.cutAt > 0)),
    ("procs: started again from those, every two of the three answer with what was "
      ++ "acknowledged, so two nodes each have all of it", pairs == [true, true, true]),
    ("procs: and all three with every write", back && all),
    ("procs: with the leader killed, another node answers, with what was written before",
      second != leader && afterFirstDeath == (some (some "1"), some (some "3"))),
    ("procs: with the second leader killed too, the first one back from its snapshot makes a "
      ++ "majority that has everything",
      returned && third != second
        && last == ["1", "2", "3", "4"].map fun v => some (some v)),
    ("procs: a node is not started on a path with no journal, and none is made there",
      absent == some 1 && !made),
    ("procs: nor as new on the journal of a node that has run, which is left as it was",
      again == some 1 && kept) ]

def main : IO UInt32 := do
  report (← run)
