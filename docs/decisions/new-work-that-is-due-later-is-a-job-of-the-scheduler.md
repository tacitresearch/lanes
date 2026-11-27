# D?. Work that is due later is a job of the scheduler: held by its id, run by its own timer, retried until it ends

`Lanes/Behaviours/Schedule/{Basic,Sound}.lean`, `Lanes/Semantics/Schedule.lean`,
`Tests/Schedule.lean`, `examples/reminders`. Every application wants work done later: a reminder,
an email, a delete in a store retried until it lands, an upload that expires if it is never
confirmed, a session that ends after a while, a payment reconciled at night. `examples/videos`
lists the gap (its friction log, items 5 and 10): a delete the store did not answer is sent again
at once a few times and then logged; an upload never confirmed stays pending; sessions never end.
D55's jobs actor runs work now, under a bound of work at once; it has no notion of *later*, and a
job that waits behind its backoff holds a slot. What was missing is a table of jobs, each due at a
time, that survives a restart, that runs each at its time and not before, retries it with a
backoff until it succeeds or gives up, and says how it ended.

## The shape

The scheduler is an actor (`Schedule.system`), joined beside the system that uses it as the jobs
actor is (`Schedule.attach sys config use`, D55). It takes `schedule now_ms spec`, `cancel key`
and, from the adapter, `reply key attempt reply`; it emits `call attempt` and `abandon key
attempt`, which leave the join for the adapter, and `notice key payload` and `answer key outcome`,
which go to the system. A job (`Schedule.Job`) has an id, chosen by the requester, a payload, a
`Work`, a run time `at_ms`, the attempts started and a phase. A `Work` is one of three:

- `call retry`: at its time the job calls the outside with its payload, and on a failure
  (an answer `Config.ok` refuses, `unknown`, or no answer by the end of its wait) is due again
  after a backoff, until an answer is accepted (`succeeded`), its attempts or its time run out
  (`failed`, the dead letter, with the payload, the attempts and the last answer), or it is
  cancelled;
- `once`: at its time the system is told `notice`, and the job is over;
- `every period_ms`: the system is told `notice` at its time and every period after, until
  the job is cancelled. This is the sweep: "every minute, expire the sessions that are over".

The policy is data, per job (`Schedule.Retry`) under a cap for all (`Schedule.Config`, rule
2.5): `maxAttempts`, at most `Config.maxAttempts`; `deadline_ms`, how long the adapter waits for
one answer, which the attempt carries (rule 3.4) and which the scheduler waits `grace_ms` longer
than; a wait after the `n`th failure of `min cap_ms (base_ms * 2^(n-1))`; and `until_ms`, after
which no attempt starts. A step is pure, so the jitter cannot be drawn: it is
`Config.jitter key n` cut to `jitter_ms`, by default none and in the example a hash of the id
and the attempt (`Schedule.hashJitter`). Two jobs that failed together then wait different times,
and a replay waits the same.

*Ids, and scheduling twice.* A job is held under its id, and a scheduling of an id held is
answered `already` and changes nothing: scheduling is idempotent while the job is held, so a
system may schedule at every start what must exist (the example's sweep) and a request retried
by its client makes one job. An id whose job is over may be scheduled again, as a new job.
Every attempt carries the id, so the far side can tell a retry from a new request (rule 3.4),
and the example puts it in `Idempotency-Key`.

*Bounds* (rule 2.6). At most `maxJobs` jobs are held and a payload is at most `maxPayload` by
`Config.size`; beyond either, a scheduling is answered at once, `refused full` or `refused
tooLarge`, and nothing is held. A queue of schedulings waiting for room was left out for D55's
reason: refusing needs no ranking of what waits, and leaves the choice to wait to the requester.

## Time

The semantics has no clock: an armed timer may fire at any moment (D42). The scheduler keeps the
latest time it knows, `now_ms`, which only grows (`Schedule.now_le_step`): the time each scheduling
carries, which the system takes from the request that caused it (the example writes the arrival
time into the request before it is journalled, as `examples/videos` does), and the time each of
its own timers was armed for, when it fires. Every job waits on exactly one timer, armed for
`at_ms` minus the time known: `due` while it waits, `expire` while an attempt is out
(`Schedule.timer`, `Schedule.armed`). So the time known is never later than the real time, given
two things the semantics does not have and the runtime does: that the times a system is told are
not ahead of the clock, and that a timer fires no earlier than its delay after it is armed (the
kernel fires a timer only once its clock has reached the timer's deadline, `Kernel.timerNext`).
These are premises, written in `TRUSTED.md`.

Three ways were weighed. *A clock asked by an output and answered by an input* (the clock
adapter, `Lanes/Outside/IO/Clock.lean`) on every wake-up: a round trip per job, and liveness then
needs the clock to answer and to advance, which no fairness of the semantics gives. *Time in every
input*: the replies of the adapter carry none, and a timer that fires carries none either.
*The timers as the clock*, taken: a timer firing says the time it was armed for has come, which
is what the runtime guarantees and what fairness already speaks of, so liveness needs nothing new.
The cost is lateness, never earliness: after a long time with no input the time known lags, and
a job scheduled then waits from the lagging time; after a start, timers are armed again from the
time known before the crash, so a job may be late by the time the process was down. A periodic
job bounds how far the time known lags while the process is up.

## One attempt at a time

An attempt is out from its dispatch until its answer comes or its wait ends; then it is over,
and only after the backoff does the next start. At the end of its wait the scheduler emits
`abandon`, so the adapter may cut the call off; the example's HTTP client cuts every call off at
its deadline anyway. A start arms every job's timer again and dispatches nothing: an attempt out
at a crash is ended by its `expire`, as in D55. A cancel of a job whose attempt is out waits for
the attempt to end, and answers `cancelled` then: removing the job at once would let the id be
scheduled again and a second attempt start while the first is out. The seeded bug the checker
finds is the start that does dispatch again the attempt out at a crash: two attempts of one id
out at once, in 7 steps.

## What is proved

Of the scheduler alone, for every configuration and every environment, crashes, lost, reordered
and repeated messages included:

- (i) *Never too early.* An attempt is dispatched only by its job's `due` timer, for a job that
  waits, stamped with the time then known, which is no earlier than the job's run time
  (`Schedule.dispatch_due`); after a failure the job is due again the backoff after the time the
  failure was known (`Schedule.retry_waits`); the time known never goes back. With the premises
  above, no attempt starts before its time.
- (ii) *Never more often than allowed.* Every job is within its attempts (`Schedule.attempts`),
  and no id is called more than `max 1 maxAttempts` times for each scheduling of it handled, in
  every run (`Schedule.calls_le_scheduled`, counted over what a run shows, D31's deeds).
- (iii) *Progress.* In a fair run (`System.Run.Fair`, which obliges a timer that stays armed and
  is not armed again to fire) in which the scheduler does not crash, every job held that is not
  periodic stops being held, whatever the service does (`Schedule.held_leaves`), and the step that
  ends it emits its end, an answer to its id or its notice (`Schedule.ends_of_leaves`), which is
  handed over (`Schedule.held_ends`). A periodic job is noticed again and again while it is held
  (`Schedule.every_noticed`). Beside any system the same holds of its jobs
  (`Schedule.attach_held_leaves`). The measure is two for each attempt left and one more while an
  attempt is out (`Schedule.left`); the rule is `System.LeadsTo.induction`, as for jobs.
- (iv) *One attempt out per id.* No id is held twice and the jobs stay within `maxJobs`
  (`Schedule.within`, `Schedule.attach_within`); an attempt is dispatched only for a job with
  none out (`Schedule.dispatch_due`), and an attempt out ends only with its answer or, abandoned,
  at the end of its wait (`Schedule.attempt_ends`).

*The premise of (iii), stated honestly.* The scheduler must not crash: a crash loses its timers,
and the semantics obliges a stopped actor to start again only when it has mail, as for the gate
and the jobs actor. A shard starts its actors again from the journal, and the start arms every
timer again (`Schedule.armed`), so in a deployment a crash delays jobs; that the start comes is
not proved. (iii) does not depend on the service: an attempt the service never answers ends at
its `expire`.

*Not proved.* That the time known is not ahead of the real time: it is the premise above. That
an attempt abandoned is over at the service: a service that may still act on it must deduplicate
by the id, which every attempt carries, and the example's HTTP client cuts its call off at the
deadline. That an answer emitted beside a system reaches it at most once (D55's limit, the same
here).

*Checked first* (`Tests/Schedule.lean`), with a requester that schedules, schedules twice and
cancels, and a service that answers success, failure or `unknown`, late or never, every timer
firing at any moment, what is checked is what the requester sees: no attempt is handed over with
a stamp before the time asked for or before the backoff after the attempt before it; no id is
called more often than its attempts for each scheduling sent; no id has two attempts out at the
service, the abandons still on their way counted; the same with the scheduler crashing and inputs
reordered; a sweep noticed three times and cancelled; refusals when full and too large; a cancel
while an attempt is out. The checks keep the outputs a run hands over in any order, as the
semantics does, so the service's model, `Schedule.callee`, keeps an abandon that arrives before
its call.

## Consequences

- `examples/reminders` uses it end to end over HTTP: a reminder is a job that posts its text to a
  notification service until it takes it, the sweep is a periodic job scheduled at every start,
  and a restart on the journal keeps every job.
- `examples/videos` is not changed yet: its delete retries, the expiry of its pending uploads and
  of its sessions are to move onto the scheduler once the changes other branches are making to
  it have landed.
- D55's jobs actor stays: it is for work now, bounded by work at once; the scheduler is for work
  later, bounded by jobs held.
