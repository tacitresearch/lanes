# D55. Work outside a step is a job: an actor with an outbox, a deadline per attempt and a bound

`Lanes/Behaviours/{Jobs,JobsSound}.lean`, `Lanes/Semantics/JobsLive.lean`, `Lanes/Env/Jobs.lean`,
`Tests/Jobs.lean`. An application needs work that is not a function of one request and must not
run on a shard's thread: an outbound call (an API, a mail provider, a model), slow pure work, and
work on a schedule. D3 and D26 already give the shape, an output an adapter performs and whose
answer comes back as an input, and the HTTP client does it for one call. What was missing is the
machinery every such use repeats: an id that goes with each attempt, retries with backoff, a
deadline, a bound on what is in flight, and the guarantee that each job is answered once.

- *An actor, not an effect.* The jobs actor (`Jobs.system`) takes `submit key job` and answers
  `answer key outcome`; between the two it dispatches `dispatch key attempt job` as an output
  and takes `result key attempt r` as an input. A system uses it beside itself
  (`Jobs.attach sys config use`, a `System.join`): `use` says which outputs of `sys` submit a job
  and which input of `sys` an answer is. Nothing new enters the semantics, so the checker, the
  kernel, the journal and every proof tool apply to it as they are.
- *The key is the requester's.* The requester names the job; the key travels with every attempt
  (`Jobs.call` puts it in `Idempotency-Key`) so the far side can tell a retry from a new request
  (rule 3.4), and the answer names it, so the requester's `accept` routes it back. A submission
  of a key already active is a duplicate and is dropped; it is answered with the first.
- *The policy is data* (rule 2.6, `Jobs.Config`): `maxInFlight` jobs active at once, each
  holding its slot from its first attempt to its answer; `maxAttempts`; `attempt_ms`, the
  deadline of one attempt; a backoff that doubles from `backoff_ms` up to `maxBackoff_ms`; and
  `retryable`, which results are failures worth another attempt. At the limit a submission is
  answered `refused` at once. A queue of waiting jobs was left out: a job behind others is
  answered only when one of them is, and its liveness needs a ranking over the jobs ahead,
  where refusing needs none and leaves the choice to wait to the requester (rule 1.5).
- *Outcomes.* `done r` (a result the policy accepts), `failed r` (the last attempt's result,
  which the policy would retry), `timedOut` (the last attempt's deadline passed with no result),
  `refused`. A result for an attempt that is not the one being made, a late one, is dropped: the
  attempt it answers has already been counted.
- *One timer per job.* A job waits on its attempt's deadline (`expire key`) or on the end of its
  backoff (`retry key`), never both (`Jobs.timer`). A start arms again each job's timer and
  dispatches nothing: an attempt in flight at a crash is retried by its deadline, with its key.
- *The pool decides nothing* (rule 3.9). `Jobs.handler` performs each dispatched attempt on a
  task of its own and hands the result back with `tryInput`; one that throws, or finds the inbox
  full, gives no result and the deadline brings the next attempt. A worker is a pure function
  (`Jobs.compute`) or an HTTP call (`Jobs.call`). `Jobs.pool` is what workers may do, answer an
  attempt dispatched, once, with anything, or never, which the checker explores and a recorded
  run is tested against. An attempt that is not cut off when its deadline passes keeps running,
  so the work done at once can exceed `maxInFlight`; the HTTP client cuts its own calls off at
  its own timeout, which should be at most `attempt_ms`. A pure worker cannot be cut off.
- *The journal.* Submissions and results are inputs (or, beside a system, messages caused by
  inputs) and are journalled; dispatches are outputs. A restart replays to the same active jobs
  with the same timers, hands over again the dispatches not marked as handed over, and so
  neither loses a job nor repeats one that was answered. A job whose result had not been
  journalled when the process died is attempted again with its key, and that is all the far
  side has to deduplicate it by.
- *A password is not hashed by a job.* What a job is asked is journalled, and a password must
  never be (D44); so the ledger's Argon2id stays in `Bridge.prepare`, which runs on the request's
  task, off the shard's thread, before the request has an id. A job is for work whose input may
  be journalled.
- *Work on a schedule* is an actor's own timer (`after`) whose step submits jobs; it needs
  nothing of its own.
- *What is proved*, of the actor alone, for every configuration: no more jobs are active than
  slots and no key twice (`Jobs.within`); while it is up, the timer each active job waits on is
  armed (`Jobs.armed`); no key is answered more often than a submission of it is handled, in
  every environment, crashes and duplicating links included (`Jobs.answered_le_handled`); a
  dispatch is of a job active after the step, with its key, work and attempt
  (`Jobs.dispatch_active`), and a retry carries the work of the attempt before it
  (`Jobs.retry_same`). In a fair run in which the actor does not crash, every job it admits is
  answered (`Jobs.active_answered`) and so is every submission it handles
  (`Jobs.submitted_answered`), whatever the workers do; the measure is two for each attempt left
  and one more while an attempt is made (`Jobs.left`), and the rule is
  `System.LeadsTo.induction`, new in `Lanes/Semantics/Liveness.lean`. Beside a system the slots
  hold (`Jobs.attach_within`) and every active job stops being active
  (`Jobs.attach_active_leaves`), by `System.LeadsTo.join_left`.
- *Not proved.* That the answer, once emitted beside a system, is delivered to the requester
  (the join's own delivery, which the projection does not carry), and at most once there: the
  count is proved of the actor alone and is not yet carried through the join by
  `SysState.run_left`, as the gate's is. With crashes the actor loses what was delivered to it
  and not yet handled, a submission among them, so liveness is stated of runs without them, as
  the gate's is.
- *Checked first.* Two jobs, two slots, two attempts, workers that succeed, fail, answer late or
  never, timers firing at any moment: every job answered once, every attempt with its key's work,
  within the slots, timers armed and never armed again while a job waits on them; the same with
  one slot, where a job is refused; with crashes and reordering; and beside an application that
  reports each answer once. Live: a local service that answers `503` twice and then `200` sees
  the same key three times; a closed port fails after three attempts; a service that never
  answers times out at the third deadline; the recorded runs are what `Jobs.pool` allows.
