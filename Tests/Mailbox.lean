/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-! The inbox as data: who is refused, who waits, who is woken, and in what order things come
out. Wakers are numbers here. -/

namespace Tests.Mailbox

open Lanes

abbrev Box := Mailbox Nat Nat

def offers (capacity : Nat) (xs : List Nat) (m : Box) : List Bool × Box :=
  xs.foldl (init := ([], m)) fun (answers, m) x =>
    match m.offer capacity x with
    | (.taken _, m) => (answers ++ [true], m)
    | (_, m) => (answers ++ [false], m)

def tests : List (String × Bool) :=
  let (answers, full) := offers 2 [1, 2, 3] {}
  let (waited, withWaiter) := full.offerOrWait 2 4 70
  let (urged, withUrgent) := withWaiter.urge 9
  let (taken, emptied) := withUrgent.take
  let (asleep, resting) := emptied.rest 50
  let (woken, afterOffer) := resting.offer 2 5
  let (stillAwake, _) := afterOffer.rest 51
  let (toWake, closed) := ({ resting with waiting := [60, 61] } : Box).close
  let twoUrgent := ((({} : Box).urge 7).2.urge 8).2
  let (restsOnUrgent, _) := twoUrgent.rest 53
  let (urgedAsleep, _) := resting.urge 6
  [ ("mailbox: what comes from other shards comes out in the order it went in",
      twoUrgent.take.1.batch == [7, 8]),
    ("mailbox: a shard does not sleep on what another shard sent, and is woken by it",
      !restsOnUrgent && urgedAsleep == some (some 50)),
    ("mailbox: a full inbox refuses, and what it took comes out in the order it went in",
      answers == [true, true, false] && taken.batch == [9, 1, 2]),
    ("mailbox: a sender that waits for room is woken when the shard takes",
      (waited matches .full) && taken.wake == [70] && emptied.count == 0),
    ("mailbox: what comes from another shard is never refused for want of room",
      urged == some none),
    ("mailbox: a shard asleep is woken by the first thing that arrives, and by nothing after",
      asleep && (woken matches .taken (some 50)) && afterOffer.sleeper.isNone),
    ("mailbox: a shard does not go to sleep on an inbox that has something in it", !stillAwake),
    ("mailbox: closing wakes the sleeper and every sender that waits, and then nothing is taken in",
      toWake == [50, 60, 61] && (closed.offer 2 1).1 matches .closed
        && (closed.urge 1).1.isNone && !(closed.rest 52).1) ]

end Tests.Mailbox
