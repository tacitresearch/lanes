/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! The scheduler's decisions as data (`Lanes.Runtime.Sched`): when an actor goes on a run queue,
what a step takes and leaves, a timer that went stale, a stop, and the ledger's bound and idle
waiters. Wakers are numbers here. -/

namespace Tests.Sched

open Lanes Lanes.Sched

abbrev sig : Signature where
  Id := Unit
  Msg _ := Nat
  In := Nat
  Out := Nat

/-- Adds what it is sent and puts out the sum; `0` stops it; `7` arms the timer `1`. -/
abbrev adder : System sig where
  State _ := Nat
  actor _ := {
    init := 0
    step := fun s n =>
      if n = 0 then (s, [.stop])
      else if n = 7 then (s, [.after 10 1])
      else (s + n, [.emit (s + n), .send () 1])
    recover := fun s => (s, []) }
  accept n := ⟨(), n⟩

def push (s : Slot adder ()) (x : Item sig ()) : Bool × Slot adder () := s.push x

def slotTests : List (String × Bool) :=
  let s := Slot.fresh adder ()
  let (queued, s) := push s (.msg none 5)
  let (again, s) := push s (.msg none 3)
  let (began, s) := s.begin
  let (started, s) := s.take
  let (s, _) := s.put 0 (match started with | .job j => j.run | _ => ((0 : Nat), []))
  let (delivered, s) := s.take
  let r := match delivered with | .job j => j.run | _ => ((0 : Nat), [])
  let (s, c) := s.put 0 r
  [ ("sched: an idle actor that gets mail is queued once", queued && !again),
    ("sched: a message to an actor down starts it and stays queued; then it is delivered",
      began && (started matches .job ⟨.start, _⟩) && (delivered matches .job ⟨.deliver none 5, _⟩)
        && s.cell.state == 5 && c.outputs == [5] && c.sends.length == 1),
    ("sched: an actor let go of with mail waiting is queued again",
      s.release.1 && s.release.2.status == .queued) ]

def timerTests : List (String × Bool) :=
  let s : Slot adder () := { Slot.fresh adder () with cell := { state := 0, up := true } }
  let (s, armed) := s.put 0 ((0 : Nat), [(.after 10 1 : Effect sig ())])
  let due := armed.armed.head?.map (·.2)
  let (s, _) := s.put 0 ((0 : Nat), [(.after 20 1 : Effect sig ())])
  let (_, s) := push s (.timer 1 (due.getD ⟨0, 0⟩))
  let (dropped, s) := s.take
  let (_, s) := push s (.timer 1 ⟨20, 1⟩)
  let (fired, _) := s.take
  [ ("sched: a timer armed again before it went off is dropped when taken",
      due == some ⟨10, 0⟩ && (dropped matches .stale)),
    ("sched: the timer pending is taken as a step", fired matches .job ⟨.timeout 1, _⟩) ]

def stopTests : List (String × Bool) :=
  let s : Slot adder () := { Slot.fresh adder () with cell := { state := 4, up := true } }
  let (_, s) := push s (.msg none 1)
  let (_, s) := push s (.msg none 2)
  let (s, c) := s.put 0 ((4 : Nat), [(.send () 9 : Effect sig ()), .after 5 1, .stop])
  [ ("sched: a stop takes the actor down with its timers and mail, and what it sent itself",
      !s.cell.up && s.cell.timers.isEmpty && s.mail.isEmpty && c.dropped == 2
        && c.droppedInputs == 2 && c.sends.isEmpty) ]

abbrev L := Ledger Nat Nat

def ledgerTests : List (String × Bool) :=
  let l : L := {}
  let (a, l) := l.offer 2
  let (b, l) := l.offer 2
  let (c, l) := l.offerOrWait 2 70
  let (quiet, l) := l.idle false 50
  let (room, l) := l.free 1
  let (idle, l) := l.done true 0 0 0
  let (room', l) := l.free 1
  let (idle', l) := l.done true 0 0 0
  let (now, l) := l.idle false 51
  let ((told, idlers), l) := ({ l with idlers := [(true, 60)] } : L).close
  [ ("ledger: the inbox takes up to its capacity, then a sender waits",
      (a matches .taken) && (b matches .taken) && (c matches .full) && !quiet),
    ("ledger: a step that takes an input makes room and wakes the sender that waited",
      room == [70] && idle.isEmpty),
    ("ledger: the last item done answers who waited for idle", room'.isEmpty && idle' == [50] && now),
    ("ledger: closing tells every waiter, and then nothing is taken",
      told.isEmpty && idlers == [60] && (l.offer 2).1 matches .closed) ]

def tests : List (String × Bool) :=
  slotTests ++ timerTests ++ stopTests ++ ledgerTests

end Tests.Sched
