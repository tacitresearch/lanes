# D18. The runtime is a proved kernel inside a thin shell

Status: Accepted

*Supersedes D13 and D16.*

`Lanes/Runtime/Kernel.lean` holds every runtime decision as pure functions over a hash map of
actors and a queue: accept an input, take the oldest message (starting its receiver if it is
down), fire a timer. `Kernel.abs` reads a kernel state as a `SysState`, and
`run1_sound`, `accept_sound`, `fire_sound` and `abs_boot` prove each operation is a run of
`SysState.step` under `Kernel.env`, with the reported events being that run.

`Lanes/Runtime/IO/Shell.lean` is one task per shard that feeds the kernel from a bounded inbox
and carries out its commands (hand over an output, arm a timer).

Why: the first runtime was 400 lines of concurrent IO making decisions under locks. A review
found five defects in it and fixing them introduced a sixth. None of that logic needed to be
concurrent. As pure functions it is proved once, and the per-actor tasks, gate mutexes, logical
clock and outbox are gone. Recorded traces now replay by theorem; the repeat-run stress loop
went from twenty minutes to seconds.

Consequences:

- Actors in one shard do not run in parallel. Parallelism will come from several shards, each
  a system joined to the others by links, which the semantics already models.
- A stopped actor starts again on its next message. The eager restart policy and its budget
  are gone from the runtime; supervision returns as library actors with specs (rule 3.1).
- The only assumption about `Std.Async` is the inbox channel and the timer.
