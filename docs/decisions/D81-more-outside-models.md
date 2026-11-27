# D81. Models of more outside systems: queues, caches, clocks, shared caches, rate limits and disk faults

D65 gave the combinators for models of external services and the first instances. This adds six
more, each with a theorem about what it allows and a fixture in `Tests/` with a seeded bug the
checker finds against the model and the fix that passes. It changes nothing D65 decided, except
that the monotonic clock's model moves out of its IO file.

## The models

- **A queue** (`Lanes/Outside/Queue.lean`), as SQS gives one. A message is received with a
  receipt and may be received again at any moment until it is deleted with its latest receipt:
  the model has no time, so a visibility timeout may pass at once. A standard queue gives the
  messages in any order and keeps a copy for each send of an id; a FIFO queue gives a message only
  after every earlier one of its group has been received, and drops a resend of an id it holds.
  After `maxReceives` receives of a copy a message goes to the dead-letter queue, which is SQS's
  `maxReceiveCount` and the bound that keeps the checker finite. Proved: `Queue.received_le`,
  `Queue.fifo_received_le`, `Queue.deleted_not_received`.
- **A cache** (`Lanes/Outside/Cache.lean`), as Redis or memcached gives one, in front of a store.
  A key may be evicted or expire at any moment, so a get may always miss; a write lands at some
  moment between its request and its answer, or after a lost answer at any moment or never; a get
  answers what the key held at some moment while it was open. Leases, as memcached's: a miss may
  grant a token, and a `fill` sets the key only while the token is the key's lease, which any write
  ends. With `stale` a get may answer any value ever written to the key: a lagging replica, or a
  failover that lost the last writes. Proved: `Cache.read_sent`, `Cache.fill_unleased`.
- **Clocks** (`Lanes/Outside/Clock.lean`). `Clock.outside`, the monotonic clock, was in
  `Lanes/Outside/IO/Clock.lean` beside the handler; it moves here unchanged, with
  `Clock.outside_ge`. `Clock.wall skew_ms` is the wall clock: each reading within `skew_ms` of a
  true time that never goes back, so it may be set back by up to twice the skew between two
  readings, and no further (`Clock.wall_back_le`).
- **A shared cache in front** (`Lanes/Web/Http/SharedCache.lean`): what RFC 9111 lets a CDN or a
  proxy store and reuse, keyed by the target and the headers `Vary` names, as an `Outside` that
  keeps what the system answers. It is under `Lanes/Web/Http/` because it is about HTTP's values.
  Proved: `SharedCache.serve_storable` (nothing `private` or `no-store` is served),
  `SharedCache.serve_reuses`, and `SharedCache.serve_of_leaks`, which is what makes `leaks` a check
  an application can run: given exchanges with the origin, the pairs where the cache may give the
  second request the first's response and the origin gave it another. With none, a cache that kept
  any of them gives each of their requests what the origin gave it.
- **A service that throttles** (`Lanes/Outside/Throttle.lean`): a combinator over `Rpc.Server`.
  A call may be answered `throttled retryAfter` (HTTP's `429` with `Retry-After`), which did not
  execute it; a call received before the wait it was told has passed is counted (`early`). Time is
  a tick the service reports as an event, which the caller also sees as an input, at most
  `maxTicks` of them. With `burst` the limit is that many calls a tick: within it a call is never
  throttled, beyond it always. Proved: `Throttle.throttled_inner`, `Throttle.within_not_throttled`,
  `Throttle.wait_le`.
- **Disk faults** (`Lanes/Durable/Reading.lean`). A read at a start gives the bytes, says there is
  no such file, or fails. `Disk.ofReadings` refuses on a failure, and `Disk.Torn.load_readings`
  says that whatever dying left, a start whose reads do not fail loads the kernel the shard had: a
  read error never loses committed entries. A slow `fsync` is not a new fault: at every moment of
  it the files are what dying then would leave (`Disk.crash`), and the shell hands nothing over
  before its append returns (`Batch.run_sound`); that other work waits is the shell's and is not
  proved.

## A real defect: a journal that could not be read was begun again

`Store.open` asked `pathExists` whether the journal was there. `pathExists` says `false` for every
error of `stat`, not only for a file that is not there: an `EIO`, an `ELOOP`. The start then took
the journal for one never begun, and, with `create` (the default), wrote a new header over it by
the rename `Disk.mend` asks for: every committed entry lost, silently. A read that failed after
`stat` succeeded threw, and the start refused. Now the journal and the snapshot are read with one
call each, and only "no such file" is a file not there (`Journal.Reading`); any other error
refuses the start with the error, and the files are left as they were. The change is in
`Lanes/Durable/IO/Journal.lean`, trusted, and the decision is the pure `Disk.ofReadings`.
`Tests/Durable.lean` makes the journal a link to itself: the start before this change began a
journal over it, and this one refuses.

## What the fixtures show

The checker finds each seeded bug against its model; the counts are the steps of the shortest
counterexample, as the tests print them.

| Model | Seeded bug | Found in | Fix |
| --- | --- | --- | --- |
| Queue (`Tests/Queue.lean`) | A consumer that credits every message it receives credits one twice, received again before its delete | 5 steps | A table of the ids applied: passes with redeliveries, a crash and a FIFO queue |
| Cache (`Tests/Cache.lean`) | Read-through: a reader reads the store before a write, the writer deletes the key, the reader sets it after; a read begun after the update gives the old value | 26 steps | A lease, so the late fill is refused: passes whatever is evicted; a stale cache breaks it again in 26 steps |
| Wall clock (`Tests/WallClock.lean`) | A token's expiry as the difference of two readings: found expired, then valid again after the clock is set back | 16 steps | The latest time seen as a floor; the bug passes against the monotonic clock |
| Shared cache (`Tests/SharedCache.lean`) | An account page with no `Cache-Control` is served to another client | 4 steps | `no-store`; `leaks` finds the first and not the second |
| Throttle (`Tests/Throttle.lean`) | Retrying a `429` at once calls while told to wait (10 steps), and gives up without getting through (15 steps) | 10 and 15 steps | Holding every call until the wait has passed: no early call, and both requests get through |
| Disk (`Tests/Durable.lean`) | A start that took a failed read for no file begins a journal over every entry | a test | `Disk.ofReadings` |

The cache's checks explore about a hundred thousand states and run in `lanesCheck`; the others
run in `lake test`. `examples/videos` is checked against the shared cache: every reply and every
answer the bridge gives without the system, for three viewers, has no leak (its pages are
`no-store`, its redirects are not stored without freshness).

## What is assumed of the real systems

Premises of every theorem about a system beside these models, trusted and not tested against a
real service (`TRUSTED.md`, "Models of external services"):

- SQS: a delete with the latest receipt deletes; one with an earlier receipt may not, which the
  model reads as not. A delete is a call that may fail; the model takes it as done when it is
  handed over, so an adapter must not hand over a delete it did not make. FIFO deduplication has a
  five-minute window the model does not have, and a FIFO receive of a batch from one group is
  modelled as receives one at a time.
- Redis and memcached: eviction and expiry at any moment, writes landing between request and
  answer. Leases as memcached's are not Redis's: in Redis a fill under a lease is a script or a
  `WATCH`, and an adapter must make it end the lease on every write. With replication or a
  failover, `stale` is the model; without it, the model assumes reads from the primary.
- Clocks: the wall clock within `skew_ms` of a true time that never goes back. Nothing in Lanes
  measures the skew of a host.
- Shared caches: RFC 9111's rules for a shared cache. CDNs differ (some do not store a response
  with `Set-Cookie`, most need `Last-Modified` before they use heuristic freshness); the model
  allows the most, which is the safe direction for a check of leaks.
- Rate limits: one caller, and with `burst` a limit by the tick. A service that throttles for the
  load of others is the model without `burst`, under which no caller is sure to get through.
- The file system: a read that fails says so and does not give other bytes than the file's.

## Not done

- The premises of `Lanes/Web/Auth` (sessions' `seen_s` floor, ID tokens' `skew_s`) and of
  `integrations/aws/Aws/Refresh.lean` (`skew_ms`) are not yet stated against `Clock.wall`. Each
  is a theorem of its own: that a session's floor makes its expiry monotone under the wall clock,
  and that `skew_s` covers twice the model's skew.
- No adapter for SQS, Redis or a CDN, and no recorded run of a real one.
- A write to the journal that fails (`fsync` returning `EIO`) stops the shard, which is right, but
  a page the kernel dropped may leave the journal damaged where a restart refuses it rather than
  cut: not modelled.

## Consequences

- An application that uses a queue, a cache, the wall clock, a CDN or a rate-limited service can
  be checked against what it may do, not only against what it does on a good day, and the classic
  bug of each is a fixture to copy.
- A journal that cannot be read is refused, where it was begun again. A start that used to come
  back empty after an `EIO` on `stat` now does not come back until the file can be read.
