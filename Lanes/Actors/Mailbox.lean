/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
A shard's inbox, as data. Senders on any thread put commands in; the shard takes everything
that has arrived at once. Taking a batch is what makes an input cheap: one exchange with the
other threads for many inputs, and one write to the journal.

The functions here decide who is refused, who waits and who is woken; the shell
(`Lanes.Runtime`) keeps a `Mailbox` in a reference and resolves the promises it is handed. The
lists are kept newest first, because a list is extended without copying it, and an object that
several threads can see is never updated in place.

`W` is whatever wakes a sleeper: a promise in the shell, a number in the tests. What these
functions decide is proved in `Lanes/Actors/MailboxSound.lean`.
-/

@[expose] public section

namespace Lanes

structure Mailbox (α W : Type) where
  /-- Bounded: senders are refused or wait when it is full. Newest first. -/
  items : List α := []
  count : Nat := 0
  /-- From other shards: never refused for want of room, so that two shards cannot block each
  other. Newest first. -/
  urgent : List α := []
  closed : Bool := false
  /-- The shard, asleep until something arrives. -/
  sleeper : Option W := none
  /-- Senders waiting for room. -/
  waiting : List W := []

namespace Mailbox

variable {α W : Type}

inductive Offered (W : Type) where
  /-- Taken. Wake the shard if it was asleep. -/
  | taken (wake : Option W)
  | full
  | closed

/-- Put `x` in if there is room. -/
def offer (capacity : Nat) (x : α) (m : Mailbox α W) : Offered W × Mailbox α W :=
  if m.closed then (.closed, m)
  else if m.count < capacity then
    (.taken m.sleeper, { m with items := x :: m.items, count := m.count + 1, sleeper := none })
  else (.full, m)

/-- Put `x` in if there is room, and otherwise remember `room` to be woken when there is. -/
def offerOrWait (capacity : Nat) (x : α) (room : W) (m : Mailbox α W) : Offered W × Mailbox α W :=
  match offer capacity x m with
  | (.full, m) => (.full, { m with waiting := room :: m.waiting })
  | answered => answered

/-- Put `x` in whatever the room. `none` if the mailbox is closed. -/
def urge (x : α) (m : Mailbox α W) : Option (Option W) × Mailbox α W :=
  if m.closed then (none, m)
  else (some m.sleeper, { m with urgent := x :: m.urgent, sleeper := none })

structure Taken (α W : Type) where
  /-- What had arrived, oldest first, those from other shards before the rest. -/
  batch : List α
  /-- Senders that waited for room, to be woken: there is room now. -/
  wake : List W
  closed : Bool

def take (m : Mailbox α W) : Taken α W × Mailbox α W :=
  ({ batch := m.urgent.reverse ++ m.items.reverse, wake := m.waiting, closed := m.closed },
    { m with items := [], count := 0, urgent := [], waiting := [] })

/-- Go to sleep until something arrives, unless something has: then stay awake. -/
def rest (wake : W) (m : Mailbox α W) : Bool × Mailbox α W :=
  if m.closed || !m.items.isEmpty || !m.urgent.isEmpty then (false, m)
  else (true, { m with sleeper := some wake })

/-- Take no more. Everyone asleep or waiting is to be woken. What is in it stays to be taken. -/
def close (m : Mailbox α W) : List W × Mailbox α W :=
  (m.sleeper.toList ++ m.waiting, { m with closed := true, sleeper := none, waiting := [] })

end Mailbox

end Lanes
