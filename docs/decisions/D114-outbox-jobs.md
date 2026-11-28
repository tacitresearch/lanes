# D114. The outbox and jobs are rows, performed by a worker under the row's id as the key

Status: Accepted

`docs/decisions/D110-volatile-actors.md` makes actors volatile and puts what must survive a
restart in the database: effects in an outbox, jobs with the time they are due, idempotency
keys. `docs/decisions/D111-typed-store.md` gives the typed transactions. This decision is the
outbox, jobs and schedules on them, and the worker that performs them (issue #243). It replaces
the in-memory jobs actor and scheduler (D55, D79), which lost every job at a restart.

## One table shape for effects, jobs and schedules

A jobs table (`Lanes/Db/Jobs.lean`) holds jobs: an id (the primary key, one more than the
largest), a key the requester chose, the work (text, through a `Payload` with the law
`decode (encode w) = some w`), the time it is due, a status (pending, done, failed, cancelled),
the attempts of this run, a lease, a period and a note. The key has a unique index, the time due
an index on `(status, due_ms)`.

- **The outbox** is a jobs table whose jobs are effects, written in the transaction that causes
  them, due at once. An effect written in a transaction that rolled back, or never committed, is
  not in the table, so it is never performed.
- **A job** is a row due at a time.
- **A schedule** is a job with a period: a success makes it due again `every_ms` later, its
  attempts counted afresh, on the same row and key.

One shape, not three, because the three need the same things: a time, retries with a bound, a
key, and a worker that survives nothing and loses nothing. The applications choose the table's
name, so an outbox and a jobs table are two tables of one shape.

**Enqueue is idempotent.** A key already held makes `enqueue` a no-op that answers the job that
holds it. A request whose answer was lost and that runs again enqueues once. This is acting
once at the source.

## Every decision is pure; transactions only read and write

`Config.claimed` and `Config.finished` say what a claim and an answer do to a job. The
transactions are short and serializable:

- `claim now limit` scans the pending jobs due by `now`, earliest first, at most `limit` and
  `batch_max`, and leases each: one more attempt, the lease changed, due again `lease_ms` later.
  A job whose attempts are spent is failed instead.
- `finish id lease now verdict` records an answer if `lease` is still the job's: done (or due
  again, for a schedule), failed for a fatal verdict or when the attempts are spent, or due again
  after a backoff. It changes the lease, so a second answer to the same attempt, or an answer to
  an older one, changes nothing.
- `cancel key` stops a pending job.

## The worker is an actor, and its attempt is named by the row

The worker (`Lanes/Db/Worker.lean`) is a system with one actor: ticks in, calls to the store and
attempts out, their answers in. It keeps only what a restart may lose: the time, the claim out,
the attempts out. Its IO (`Lanes/Lib/Postgres/IO/Worker.lean`) performs: the store's calls
through the typed store's driver, each attempt through the job's adapter on a task of its own.

An attempt is named by the job's id and lease, never by a counter of the worker
(`Worker.attemptNumber`). A worker that restarts numbers its calls from zero again; an answer to
an attempt from before the restart must not be taken for one after it. The coordinator found
that bug in `examples/payments` under the restart event (#240); the jobs table cannot have it.

The idempotency key is the job's id (`Worker.runPort`), with a prefix the adapter chooses. The
alternative was a key the application chose; the id is unique in the table already, needs no
second index, and is the same for every attempt.

## What is proved, against the store's model and the service's

The theorems run the worker's real step beside `Db.outside` with the application's
transactions on the same database at any moment (`Worker.world`; the input `submit` stands for
them in the model), and any service, in every environment model, process restarts included
(the restart event of #240: the worker starts again from nothing, the store and the service
keep what they hold):

- **No effect for a transaction that did not commit** (`Worker.committed_only`). Every attempt
  the worker hands over is of a job, with its work, in every database the model may hold, once
  any call still outstanding or lost takes effect too. It needs the application's transactions
  to keep the table (`Queue.Keeps`): add jobs, and leave those there alone. `enqueue` does
  (`Queue.enqueue_keeps`). The proof is a property of the model's worlds (`Db.WorldInv`,
  `Db.world_invariant`, new in `Lanes/Db/Sound.lean`): each claim that took effect answers jobs
  its world's table holds.
- **At most once at a receiver that honours keys** (`Worker.once_each`): every attempt is under
  its job's id, so behind `Idempotent.server` no two effects are under one job.
- **Bounded, every job due taken, one per key** (`Lanes/Db/JobsSound.lean`): a claim answers at
  most `batch_max` jobs (`Queue.claim_length`), each for one more attempt of a job whose attempts
  were not spent (`Queue.claim_attempts`); a claim short of its limit takes every job due
  (`Queue.claim_takes`); no two jobs hold one key in any database the model allows
  (`Queue.one_per_key`, from `Op.unique_apply`: the store keeps a unique index unique under every
  operation); a finish of a lease that is not the job's changes nothing (`Queue.finish_stale`).
- **At least once.** The worker hands every job of a committed claim to its adapter in the step
  that reads the answer (`Worker.stored_runs`); a job not finished is due again when its lease
  runs out. That a job is attempted until it is done or given up in every fair run is not one
  theorem: the store's model may fail every call forever, and a liveness theorem needs a
  premise of the store's progress that the model does not state yet. That a job done had an
  attempt the service took is model-checked (`Tests/Worker.lean`), not proved.

These replace the theorems of the jobs actor and the scheduler where they still mean something:
bounded (`Jobs.within`, `Schedule.within` become `Queue.claim_length` and
`Queue.claim_attempts`), every due job attempted (`Schedule.dispatch_due`,
`Schedule.held_ends` become `Queue.claim_takes` and `Worker.stored_runs`), at most one running
per key (`Schedule.within`'s "no id twice" becomes `Queue.one_per_key` and
`Queue.finish_stale`). Their timing theorems (no attempt before its time, the backoff) have no
counterpart: time is a column, compared by the claim, and nothing proved depends on it
(`TRUSTED.md`).

## Acting once is a key in the transaction

`Keys.once key body` (`Lanes/Db/Once.lean`) runs `body` and inserts the key with its answer in
the same transaction; a key already stored answers what it was given and runs nothing. A run
under a key that committed makes every later run under it, of any body, a no-op that answers the
same (`Keys.once_again`). The key is the table's primary key: two runs at once conflict at
`SERIALIZABLE` or on the key, the driver retries the second, and it finds the key. `enqueue`
under a key is the same idea for a job.

`Lanes.Once.actor` stays, labelled volatile: its memo is in an actor and a restart forgets it
(`examples/rookery` uses it until it moves to PostgreSQL, #246).

## What is removed

`Lanes/Behaviours/Jobs/`, `Lanes/Behaviours/Schedule/`, `Lanes/Semantics/Jobs.lean`,
`Lanes/Semantics/Schedule.lean` and their tests. No kept example needs them as a volatile
cache: `examples/reminders` moves to a jobs table. `Lanes/Web/IO/Jobs.lean` stays, as an
attempt over HTTP with the job's id in a header.

## Limits

- A lease must outlast an attempt on the worker's clock; with clocks of several instances apart
  by more, a job may be attempted twice at once, and the key makes the second take no effect.
- An attempt counts when it is claimed: a worker that dies between the claim and the attempt
  spends one.
- Ids are one more than the largest: a table whose newest rows were deleted would give their
  ids, and so their keys, again. Jobs that are over are kept; nothing sweeps them yet.
