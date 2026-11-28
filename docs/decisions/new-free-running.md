# D?. Actors run free on worker threads, proved to refine the interleaving semantics

Status: Accepted

Issue #241, part of #239. `docs/decisions/D110-volatile-actors.md` made actors volatile and
removed the journal, so parallel execution no longer has to equal one recorded order: it only
has to refine the semantics, every run the runtime makes being a run of `SysState.step`. This
decision is the runtime that does that, what is proved of it, what is trusted, and what changes
for reads from state.

## The scheduler

`Lanes/Runtime/IO/Shell.lean` runs a system's actors on `Runtime.Config.workers` threads (the
hardware threads by default), in the style of Tokio and Go:

- Each actor has a slot (`Lanes/Runtime/Sched.lean`): its state, its mailbox, and whether it is
  idle, on a run queue or running, in a reference of its own.
- Each worker has a run queue of actors with mail. It takes the first; when its own is empty it
  steals the first of another's. It steps the actor on up to `budget` items (64), then lets it go,
  back at the end of its queue if mail is waiting. An actor whose mail arrives while it is idle is
  put on the run queue of whoever pushed it; inputs from outside take the workers' queues in
  turn. An idle worker parks after saying so, and whoever queues an actor wakes one.
- One actor runs on one worker at a time (`Slot.begin` holds it, `Slot.release` lets go), and its
  mailbox is handled in the order messages reached it.
- A step takes the next item and the state out of the slot (`Slot.take`), runs the step function
  outside any lock, and writes the result back (`Slot.put`). The messages it sent are pushed to
  their receivers before the actor is let go of, so the messages of a link arrive in order.
- Timers are on an agenda kept by a thread of their own, which pushes each to its actor as an
  item of its mailbox when the monotonic clock reaches the deadline. A timer cancelled or armed
  again is dropped when its actor takes it (as `Kernel.fire` drops one), so the agenda never needs
  to be exact.
- Back-pressure is kept (rule 3.8): at most `inboxCapacity` inputs wait for their actor
  (`Sched.Ledger`); `tryInput` refuses beyond and `input` waits for room. The ledger also counts
  the items in mailboxes and the pending timers, which is what `idle` waits on.
- `stop` takes no more inputs, and the workers go on until every input taken has reached its
  actor, then end.
- An actor let go of at rest (up, no timers, no mail, `Actor.fresh`) leaves the table, as the
  kernel releases it (D51).

The decisions are the pure functions of `Lanes/Runtime/Sched.lean`; the shell calls them under
the slot's reference and moves data.

## What is proved

`Lanes/Runtime/SchedSound.lean` states the abstraction. `Sched.Model` is the scheduler's whole
state as one value: each slot, each worker's run queue and the actor it holds, the messages each
actor's last step sent and has not pushed yet, and two ghosts, the messages in flight in the
order the semantics sent them and the outputs not yet handed over. `Sched.Step` is one
transition: an input arrives; a timer is pushed (at any time, or never); a worker takes an actor
off its run queue or steals one; it steps the actor on its next item, or drops a stale timer;
it pushes one message the step sent; it lets the actor go; an output is handed over; the process
restarts. `Model.abs` reads a model as a `SysState`.

- `Sched.Step.sound`: every transition is zero or one event of `SysState.step`, from the state
  the model stands for to the one it leads to, under any environment whose links are reliable
  (`Sched.Reliable`; `Kernel.env` is one) and which allows restarts if the transition is one.
  A step is `deliver`, `start` or `timeout`; an input is `input`; a hand-over is `output`; a
  restart is `restart` (#240); everything else is no event.
- `Sched.Step.inv`: the invariant `Model.Inv` holds after every transition. It is three parts:
  the mailboxes and the messages not pushed hold the messages in flight, link by link in the
  order they were sent (`Model.Coherent`), which is what makes the head of a mailbox deliverable,
  since an ordered link promises only that its own messages arrive in order; what an actor has
  not pushed, it sent (`Model.OutSrc`); and where the actors are (`Model.Placed`): running
  exactly when a worker holds it, held by at most one worker, idle only without mail, and on a
  run queue when queued.
- `Sched.Model.init_spec`: the model's start stands for `SysState.init`, and satisfies the
  invariant.
- `Sched.Run.reachable`: every run of the model from its start is a run of the semantics from
  `SysState.init`, so the state it stands for is reachable, and the outputs it handed over are
  that run's (`Event.outputs`).
- `Sched.Slot.take_push`, `Sched.Slot.put_push`: a push to a slot that a worker holds commutes
  with its `take` and its `put`, the mailbox up to its layout (`Slot.Same`). This is why the
  step function may run outside the lock: whatever other threads push meanwhile, the result is
  the model's push followed by its step.

The kernel's theorems are not reused for the scheduler: the kernel has one queue and one
thread, and its abstraction is a function, while the scheduler's mailboxes stand for the net
only link by link. The proof follows the kernel's shape instead (`Slot.put_settle` is
`Kernel.abs_settle` for one slot) and reuses its lemmas about timers (`Kernel.map_fst_arm`,
`map_fst_eraseP`). The kernel stays, with its theorems, as the one-threaded reference that
`Http.Loopback` and the tests run.

## What is trusted

That the shell's threads perform the model's transitions (`TRUSTED.md`, the first row). Each is
atomic for a reason the row gives: a push, `begin`, a step's `take` and `put`, and `release` are
each one `modifyGet` on the slot's reference; between a pop from a run queue and `begin` only
pushes can reach the slot. One transition needs a lock: the model lets a step stop its actor only
when no message to it waits to be pushed, since the semantics drops all of a stopped actor's
mail at once. A step that sends holds a shared lock from before its write-back to its last push,
and a step that stops its actor holds it alone (`Std.BaseSharedMutex`). Stops are rare, so
steps that send almost never wait on each other.

Two things the shell does are outside the model and argued, not proved:

- A worker keeps the state it steps in its own hands for the whole of a turn and writes it back
  when it lets go of the actor. No thread reads the state of an actor that is held (a peek waits
  for the write-back), so nothing can tell. It matters for speed: Lean never updates in place an
  object another thread may see, so a state written back after every step would be copied at
  every step.
- Releasing an actor at rest is not in the model. Its next message starts it from `init`, which
  gives back the same state with no effects (`Actor.fresh_recover`), as the kernel's release
  does (`Kernel.exec_visible`). With `record` on, nothing is released, so recorded runs replay
  exactly.

Recorded runs replay through `SysState.run` in `Tests/Runtime.lean`, on one worker, on four, and
on two with a budget of one, with actors that stop, lose their mail and restart.

## Reads from state (D108)

A peek reads each actor it names between two of its steps: at once if no worker holds it,
otherwise when its worker lets go of it. It sees every message that actor took before and none
after. A peek of several actors is **not a consistent cut**: each is read at its own moment. A
consistent cut would need every worker to stop at once, or every actor to keep the states it
had, which costs every step to serve a read that few applications need. What needs a consistent
read of several things keeps them in one actor, or in the store, whose transactions give one
(`docs/decisions/D111-typed-store.md`). The bank's total (`Tests/Reads.lean`) now can miss a
transfer in flight, and a read after a response sees the actor that gave it, not yet the actors
it sent messages to; the tests say so.

## Waves and batches removed

`Lanes/Runtime/Wave.lean`, `Pace.lean`, `Batch.lean`, `PeekSound.lean`, `Mailbox.lean` and
`MailboxSound.lean` are gone, with `Runtime.Config.parallel`, `pace`, `batch` and
`Runtime.batches`, `Tests/Pace.lean`, `bench/Waves.lean` and `bench/Auto.lean`. They existed so
that a batch run in parallel equalled one recorded order (D64, D73, D88) and so that a shard's
inbox could be taken at once for one journal write (D32). `Peek` moved to
`Lanes/Runtime/Peek.lean`, since the loopback and the views still read a kernel. Nothing needs
`Batch`.

## Measurement

`bench/Mixed.lean` (`bench/mixed.sh`), brought from the paused branch `claude/waves-default`: 64
clients each keep one request outstanding to one of 64 counters, closed loop, each step costing
what the workload draws. `serial` is the runtime on one worker, `free` on four; the two
prototypes of the earlier measurement are kept as bounds. One session of five runs of 32,000
requests on the shared four-core container, other agents' work giving a load of 8 to 11 (more
than the four cores); medians, with the spread (highest − lowest) / median:

| Steps | Way | p50 µs | p99 µs | Answers a second |
| --- | --- | ---: | ---: | ---: |
| All 2 µs | serial | 305 (2%) | 4,435 (181%) | 143,105 (83%) |
| | free | 21 (57%) | 10,982 (49%) | 124,204 (67%) |
| 1 in 50 at 500 µs, else 2 µs | serial | 851 (3%) | 4,018 (149%) | 56,933 (10%) |
| | free | 124 (69%) | 11,415 (44%) | 59,611 (37%) |
| 1 in 5 at 50 µs, else 1 µs | serial | 910 (5%) | 1,607 (75%) | 75,716 (22%) |
| | free | 172 (50%) | 8,096 (86%) | 88,875 (89%) |
| All 50 µs | serial | 4,140 (2%) | 6,119 (9%) | 18,234 (4%) |
| | free | 450 (28%) | 3,995 (54%) | 55,355 (31%) |

Free-running is five to fifteen times lower at p50 on every workload, and three times the
throughput where steps cost 50 µs. At p99 it is worse than one worker on cheap steps on this
machine: with more runnable threads than cores, a worker descheduled while it holds an actor, or
inside one of the short sections on the shared ledger, holds up whoever needs it for a time
slice. A spread of 50 to 180% at p99 says the machine, not the runtime, sets these tails. The
warm runner, idle and with more cores, should confirm before any number here is quoted as the
runtime's.

## What remains

- **The step context (D101).** `now` and `seed` in the step's context, supplied by the runtime
  and by the checker and the simulator, change the type of every step function and every
  generic proof about steps (D101 counts them). It is its own pull request, after this one, on
  top of the restart event.
- **Poison messages.** A step that panics or loops cannot be caught in Lean: a panic returns
  `default` or aborts the process, and a step has no fuel. Handling one needs either fuel in the
  step's type (part of the step context's change) or a watchdog that restarts the process. It
  waits for the step context.
- **Contention.** Every step updates the one ledger, and every push may look up a shared table
  of slots. A ledger per worker, summed on demand, is the next step if the warm runner shows it.
