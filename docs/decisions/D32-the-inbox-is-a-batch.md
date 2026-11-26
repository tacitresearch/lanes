# D32. The inbox is a batch, and waiting for room is the rare path

`Lanes/Actors/Mailbox.lean`, `Lanes/Actors/Runtime.lean`. Measured on one shard, for the first
time: the kernel does over two million turns a second, and a shard took fifteen thousand
inputs. Two things cost, and the second was found only by measuring each piece alone.

- *The shard takes everything that has arrived at once.* The inbox was a
  `Std.CloseableChannel`, at tens of microseconds an item. It is a `Mailbox` in a reference:
  senders add to a list, the shard exchanges the list for an empty one. One exchange between
  threads for however many inputs arrived together. The lists are extended at the front and
  reversed when taken, because an object that several threads can see is never updated in
  place, so an array would be copied on every push.
- *One write to the journal for a batch.* Each input is still its own turn, the pure
  `Journal.turn`, so what is proved of a turn is unchanged; the entries of all the turns of a
  batch are appended together, and only then are their outputs handed over. This is the group
  commit that D24 named as the lever.
- *`input` offers first and prepares to wait only when the inbox is full.* The first version
  made a promise to wait on with every input, in a loop, and that alone held a sender to
  fifteen thousand inputs a second whatever the shard did. `tryInput` on the same shard went
  through at 1.7 million.
- *Who is refused, who waits and who is woken are pure functions* (`Mailbox.offer`, `take`,
  `rest`, `close`), tested as data; the shell resolves the promises they return.

Tried and removed: a shard that keeps looking at its inbox for a while before it sleeps. It
changed nothing while the real cost was elsewhere, and once that was fixed it made things
slower, because it competes with the senders for the reference.

Result: 1.8 million inputs a second from one sender and about a million from four, from
fifteen thousand; the scale benchmark's 20,000 messages in 15 ms, from about 1,000. The bound
on what a restart replays is unchanged: a save is taken inside a batch as soon as it is due.
