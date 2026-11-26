# D35. An append carries a batch, and only news brings the next

`systems/raft-kv/RaftKV/Protocol.lean`. The first protocol sent a follower everything after
what it was known to hold, in one message. A review ran it as processes: a log over the
transport's 16 MiB could not be sent, so after a change of leader nothing committed again;
with a node down, every proposal and every heartbeat sent that node the whole log.

- *A bound in `Config` (rule 2.6).* `appendFrom` sends at most `maxAppend` entries, and one
  where that is zero. The bound counts entries because the protocol is generic in the command
  and cannot measure one: `maxAppend` times the largest entry has to fit in a parcel, which
  the defaults do (8, and HTTP bodies of at most 1 MiB, under 16 MiB). That no `append` in
  flight carries more is proved (`append_bounded`).
- *Only news brings the next batch.* The leader used to answer any acknowledgement short of
  its log with what follows. With batches every acknowledgement during a catch-up is short of
  the log, so each heartbeat, which sends the batch again in case it was lost, started one
  more chain of batches that ran to the end. Measured on the step function, a follower 1,000
  entries behind with a heartbeat every ten messages: 174 appends with the rule, and without
  it 29,587 appends for the first 288 entries. Now the next batch is sent only when the
  acknowledgement raises what the leader knows, so there is one chain, and what a heartbeat
  repeats is acknowledged and dropped.
- *A proposal goes to the followers that are abreast.* Sending a batch to a follower that is
  behind on every proposal is the old cost with a bound on it. A follower that is behind gets
  the entry when it acknowledges what came before, or at the next heartbeat; with a node down
  a write sends that node nothing. The price: an entry proposed while the one before it is
  unacknowledged waits for that acknowledgement, so a follower is sent at most `maxAppend`
  entries per round trip.
- *A new leader sends the end of its log.* It knows of no follower's log, and the batch after
  entry 0 would walk every follower through the whole log before anything of the new term
  could commit. The last `maxAppend` entries are taken at once by a follower that was up to
  date, and ignored by one that is not, which is then walked from the start from the first
  heartbeat on.
- *What the proofs needed.* Where an `append` starts is free in them: `Sent` asks only that
  it is cut from the leader's log. That the batch stops short is the one change: an `append`
  in flight carries a start of what follows `prev` in a leader's log, and the follower that
  takes it ends with its own log or with that leader's log as far as the batch went
  (`Within`), where it used to be all of it. `take_append_merge` is applied to the start, and
  the layers above read `Within` where they read `Led`.
- *Not done.* A follower further behind than one batch is walked from entry 1, because
  nothing tells the leader where the follower's log ends: that needs a refusal that says so,
  or a `nextIndex` that steps back, and one more number in a leader's role. A follower that
  stops reading is still sent a batch per heartbeat, up to the transport's queue.
