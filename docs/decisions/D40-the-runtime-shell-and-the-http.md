# D40. The runtime shell and the HTTP server only perform

Status: Accepted

The rule of the fourth review (`ROADMAP.md`: a pure function that decides, a model of what it
talks to, IO that only performs) was applied to the two trusted files that still decided in IO.

- *A batch is a pure function.* `Batch.run` takes the kernel, the number of entries written
  since the last save, the idle waiters and the commands taken from the inbox at once, and
  returns the kernel after them and a list of acts: append these entries, record these events,
  hand over these outputs, save this image, answer this peek with this state; and which idle
  waiters are answered. The shell performs the list in order. When the loop flushed (before an
  idle or a peek, before a save, at the end) is now where the list puts each act, and each act
  is proved sound where it falls (`Batch.run_sound`): an output is handed over only once the
  entries that produce it are appended, a save falls where everything produced has been handed
  over, a peek sees the kernel the journal so far describes. The kernel after the batch is the
  one its entries and saves describe (`Batch.run_kernel`). Reply handles are type parameters,
  as `Mailbox` has `W`, so the function holds promises without touching them.
- *The whole batch is computed before any of it is performed.* The loop used to hand over the
  outputs of a group before it ran the turns after it. Nothing a handler can do reaches the
  kernel in between: `tryInput` goes to the inbox, which is read at the next batch. So the
  only difference is when the first outputs leave, by at most one batch of pure work, and a
  write that fails still ends the shard before anything after it is performed.
- *An idle is answered at the end of a batch, as before.* `Batch.run_resolved` says so: a
  waiter, old or new, is answered exactly when the kernel is quiet, as it asked, after the
  whole batch, and otherwise waits for a later one. Answering at the idle's own place would
  answer sooner and is a change of behaviour nobody asked for.
- *An empty group gives no act.* `flush` leaves out an append, a record or a hand-over with
  nothing in it, so the shell has no guard of its own, and an empty append, which would write
  and flush nothing, is not sent to the journal.
- *The server's table is `Http.Waiting`.* `wait` hands out the next id with its waiter,
  `release` gives the id back when the shard refuses the input, `answer` hands the waiter of an
  id over and forgets it, `drain` hands over everyone. A refused request gives its id back by
  `release` rather than by putting back the table from before `wait`: holding that one across
  `tryInput` would be a second reference to the hash map, and `insert` would copy it on every
  request. `release` acts only on the id handed out last and still waited on, so the theorems
  hold of every sequence of operations, not only of the one the server makes under its mutex.
  They are stated over `Waiting.exec`, which keeps beside the table what it handed out and
  answered; the server never builds that trace.

The old trusted entry said the shell appends the entries of a batch "in one write". It wrote
once per group: an idle, a peek and a save each split a batch. `Batch.run` makes that exact.
