# Trusted code

Everything Lanes asks you to trust rather than proves, listed in one place (rule 5.5). A property
of an application is only as strong as this list. Keep it short, and add an entry in the same
change that adds trusted code.

## Trusted by every Lean program

The Lean kernel, compiler and runtime, `Std.Async`, `Std.Sync`, `Std.Http`, libuv, the C
toolchain, the operating system and the hardware.

## Trusted in Lanes

| What | Where | Why it is trusted | How it is checked |
| --- | --- | --- | --- |
| The runtime shell | `Lanes/Actors/Runtime.lean`, 271 lines | It takes commands from an inbox, reads the clock, calls the kernel and hands the kernel's outputs to the adapter. That it hands them on unchanged, all of them and in order, is not proved. Nor is its ending: that `stop`, or a journal that cannot be written, ends the shard and leaves no caller waiting. With a journal, it is trusted to append the entries each turn gives it before it hands that turn's outputs over, and to hand over at start the outputs `Journal.recover` says were not marked as handed over. What a turn asks of the kernel and which entries describe it are not the shell's: they are `Journal.turn`, proved (`Journal.turns_kernel`). | `Tests/Runtime.lean`: one input's several outputs and the boot outputs compared exactly; recorded events replayed through `SysState.run`; timers, back-pressure, stopping an idle and a busy shard. `Tests/Scale.lean`: a message costs the same at 1,000 and 100,000 actors. `Tests/Durable.lean`, on a journal held in memory: every input is in the journal before an output it caused is handed over; outputs not marked as handed over are handed over after a restart and marked ones are not; when a write fails the shard ends, reports the error and releases every caller, also those whose commands it had not yet taken. Each of these fails on the mutant that breaks it. |
| The router between shards | `Lanes/Actors/Cluster.lean`, 106 lines | It starts one runtime per shard and carries each parcel a shard puts out to the shard that hosts its receiver. That a parcel arrives once, at the right shard, in the order sent, is not proved. What is proved is the model it has to implement: two shards joined, with each parcel one emits an input of the other, behave as the one system (`System.SplitReachable.merged` in `Lanes/Actors/ShardSound.lean`). Still trusted: that the runtimes and this router together are that join, and the same for more than two shards (`PLAN.md` B.1). | `Tests/Cluster.lean`: the bank on four shards with transfers crossing between them, ordered floods across three shards, and the same results from one shard and from four. |
| The journal's file | `Lanes/Env/Journal.lean`, 88 lines | It takes a lock beside the journal before it reads anything, reads the file, cuts off in place a write that did not finish (keeping the bytes beside the journal as `.cut`), appends and flushes. Which files open and which are refused is not its decision: that is `Journal.open?`, proved. A flush reaches the operating system, not the disk: Lean's `IO` has no `fsync`. | `Tests/Durable.lean`: restart from the journal; a journal cut at eight places; a second opener refused while the first holds the journal; another system's journal, one written with another codec and one with a flipped bit each refused and left byte for byte as they were; a child process killed with SIGKILL while working, after which every request it had answered is in the journal and the state is the one the journal describes. |
| The HTTP adapter's IO | `Lanes/Env/Http.lean`, 176 lines | It reads requests from sockets, gives each an id no other has, hands them to the gated system and writes the gate's one response for each. It answers `HEAD` as `GET` without the body, `405` for other methods and, when the inbox is full, `503` itself. When the shard ends on an error it answers the requests in flight `503` and shuts down, and `wait` throws. | `Tests/Web.lean`, over a socket: fifty requests at once, `HEAD`, `405`, `413`, links with awkward text decoded by the real server, stopping with a request in flight, the bank restarted on its journal with no request id used twice, a port already taken (the journal is left free and the process can exit), and a journal that stops taking writes (every request is answered and the server ends with the error). The `503` for a full inbox is not tested. |
| The clock adapter's handler | `Lanes/Env/Clock.lean`, 77 lines | It reads the wall clock and hands the time back as an input, never a time earlier than one it gave, nor, started on a journal, earlier than the last one in it. | `Tests/Clock.lean` checks a recorded run against `Clock.outside`, the model the checker explores, with a clock started on a journal whose last time is in the future. |
| The HTTP client adapter's handler | `Lanes/Env/HttpClient.lean`, 90 lines | It opens a socket, sends a request, reads the answer within a deadline and a size limit, and hands it back as an input. The wire format it sends and reads is pure code in `Lanes/Http/Wire.lean`, tested, not proved. | `Tests/HttpClient.lean`: real calls to a real server, a closed port and a bad address, and the recorded run checked against `Client.outside`. |
| The template macro | `Lanes/Html/Syntax.lean`, 113 lines | It turns template syntax into `Html` values. What it produces is type-checked, but that it produces the element the template shows is not proved. | `Tests/Html.lean` compares rendered templates with the expected text. |

`lanes lint` fails when one of these files grows past the line count given here (rule
`trusted-size`), so trusted code cannot grow without this file changing.

What a journal file means is not in this table either. Proved in `Lanes/Actors/Journal.lean`
and `Lanes/Data/Frame.lean`: a file reads back as the entries written (`Journal.open?_file`); a
file cut at any byte opens, is never refused, and gives exactly the entries wholly written
before the cut (`Journal.open?_cut`); recovery rebuilds exactly the kernel those entries lead to
(`Journal.recover_kernel`); and what is handed over again is exactly what was produced after
the last mark (`Journal.recover_handed`). A file that is not a cut journal of this system is
refused, not repaired: a frame that is all there and does not check, an intact entry the codec
cannot read, a header that names another system. Two things are not excluded. A checksum makes
it unlikely, not impossible, that a damaged entry is taken for a good one. And damage to the
length field of the last frames can look like a write that did not finish; what is cut off
then is kept in the `.cut` file, not deleted.

The runtime's decisions are not in this table: routing, start, stop, which mail a stopped
actor loses, which timer is due, how long to sleep, how much to do before looking at the inbox
again, and when the shard is idle. They are in `Lanes/Actors/Kernel.lean` and proved in
`Lanes/Actors/KernelSound.lean` and `Lanes/Actors/KernelTimers.lean`. Nor are the HTTP adapter's (which requests are waiting, when
one times out, when too many are pending): they are the gate actor in `Lanes/Http/Gate.lean`,
proved in `Lanes/Http/GateSound.lean` to answer each arrival at most once and model-checked in
`Tests/Gate.lean`.

## Assumptions the runtime makes

- **The shell passes things on unchanged.** `Kernel.exec_reachable` proves that any sequence
  of kernel operations, in any order, with any inputs, any clock readings, batches of work of
  any size and timers fired early, late, twice or never armed, leaves the kernel in a state the
  semantics can reach, and that the events it reported are a run reaching it.
  `Kernel.exec_outputs` proves the outputs it hands the shell are exactly the outputs of that
  run. The operations are the calls the shell makes (`Kernel.Op`: `input`, `advance`, `batch`),
  so the theorems are about the shell's loop as it is written, and `Kernel.exec_append` says a
  list of operations run in two parts is the same run. So no property of reachable states
  depends on the inbox, the clock or the scheduler. What is assumed is that the shell gives
  outputs to the adapter as the kernel gave them, and that an input it reports is the one that
  arrived.
- **Progress.** That a queued input is eventually handled and a pending timer eventually fires
  is not proved as a statement about time. It rests on the inbox delivering, the clock advancing
  and the shell calling the kernel again when its sleep ends, which are assumed. The kernel's
  part is proved. `Kernel.exec_wellFormed`: after any sequence of kernel operations the agenda
  holds exactly the pending timers. From that (`Kernel.WellFormed`): while a pending timer is due
  the kernel does not tell the shell to sleep (`wait_of_due`); whenever it says there is work, a
  step does some (`step_events_ne_nil`); it says to sleep until exactly the earliest pending
  deadline (`wait_for_ms`), and without limit only when no message is queued and no timer is
  pending (`wait_forever`); and it reports idle exactly then (`quiet_iff`). A timer that is due
  and a message that is queued take turns, so neither starves the other. The oldest queued
  message is delivered, or its receiver started, by the next step or the one after
  (`step_of_queued`); the exception is that the timer which went first stopped the receiver,
  whose mail the semantics drops. While a pending timer is due, a timer due no later is fired
  by the next step or the one after (`step_of_due`, `runBatch_of_due`); the exception is that
  the message which went first cancelled that timer, armed it again or stopped its actor. So a
  due timer may wait for one message, and the oldest message for one timer. No bound is proved
  for a message that is not the oldest, or from the start of a receiver to its delivery.
  Liveness theorems are stated of fair runs of the semantics (`System.Run.Fair`); that the
  runtime's runs are fair is this assumption, not a theorem. Fairness asks of a timer what the
  kernel does: one that stays pending and is not armed again fires, and one that is armed
  again starts its delay again, so a liveness theorem does not assume that a timer fires
  while its actor keeps arming it.
- **What the gate guarantees, and under what.** *At most once* is proved. In every run of
  `gated sys`, for every system, bridge and configuration, no request id is output more often
  than it was input (`Http.answered_le_arrived`). The environment may crash and restart every
  actor, the gate included, and may lose, reorder and duplicate messages on every link but
  one: the link from the outside world to the gate must not duplicate. `Kernel.env` meets
  that, so the theorem holds of the events the kernel reports
  (`Http.kernel_answered_le_arrived`). "No id is answered twice" follows when the ids that
  arrive are distinct (`Http.answered_nodup`). That they are is trusted: `Lanes/Env/Http.lean`
  allocates them. *At least once* is proved of fair runs, for a request the gate has admitted:
  in any environment that does not crash the gate, an answer to a waiting request is handed
  over, when its deadline fires if not before (`Http.pending_answered`). What is assumed is
  that the runtime's runs are fair, which is the progress assumption above, and that the gate
  does not crash, which holds on one shard. That an arrival reaches the gate is not proved.
  `Tests/Gate.lean` checks exactly once on two requests and shows each precondition is
  needed: a reused id is answered twice, a duplicating link from outside answers one arrival
  twice, and a gate that crashes leaves a request unanswered.
- **Durability.** Without a journal, the kernel keeps actor state in memory and it is lost with
  the process. With one, the shard returns in the state the journal describes: it survives the
  death of the process, not loss of power, since nothing is synced to disk. Outputs handed over
  shortly before the death may be handed over again. An output counts as handed over when its
  handler was called: a handler that throws is not called again for it. A journal is a list of
  requests and means what the step functions that answered them make of it: replayed through
  changed step functions it gives another state, silently, unless the application changes the
  `system` name it opens the journal under, which makes the old file refused.
- **Environment model.** One shard stays within `Kernel.env`: reliable ordered links, no
  crashes other than an actor stopping itself. Properties proved under a stronger model than
  that do not apply to a running system.
- **Unbounded queue.** The kernel's message queue has no bound of its own. The inbox is
  bounded, which limits inputs waiting to enter, but one input may cause any number of
  messages between actors, and those are not limited.

## Not trusted

Actor `step` functions, `SysState.step`, the kernel (`Kernel.run1_sound`), the model checker's
exploration of a state (`SysState.mem_successors_iff`), its search (`Check.search_sound`), what a
complete PASS of `Check.system` means (`Check.system_sound_of_respects`: for actor states whose
`==` is equality, a driver state whose `==` is an equivalence, with a matching hash, that the
driver respects, and properties that do not tell merged worlds apart; `Check.system_sound` is
the case where `==` on the driver's state is equality), what a complete PASS of a refinement
check means (`Check.refines_sound`, `Check.refines_traces`: under a monitored driver the
inputs and outputs of every run of the instance are a trace of the spec, for a spec state
whose `==` is equality),
the refinement theory and every theorem in `Lanes/` and `Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe`, `@[implemented_by]` or
`@[extern]` appears in them.
