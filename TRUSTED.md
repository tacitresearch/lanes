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
| The runtime shell | `Lanes/Actors/Runtime.lean`, 202 lines | It takes commands from an inbox, reads the clock, calls the kernel and hands the kernel's outputs to the adapter. That it hands them on unchanged, all of them and in order, is not proved. Nor is its stopping: that `stop` ends the shard and leaves no caller waiting. | `Tests/Runtime.lean`: one input's several outputs and the boot outputs compared exactly; recorded events replayed through `SysState.run`; timers, back-pressure, stopping an idle and a busy shard. `Tests/Scale.lean`: a message costs the same at 1,000 and 100,000 actors. |
| The HTTP adapter's IO | `Lanes/Env/Http.lean`, 133 lines | It reads requests from sockets, gives each an id no other has, hands them to the gated system and writes the gate's one response for each. It answers `HEAD` as `GET` without the body, `405` for other methods and, when the inbox is full, `503` itself. | `Tests/Web.lean`, over a socket: fifty requests at once, `HEAD`, `405`, `413`, links with awkward text decoded by the real server, and stopping with a request in flight. The `503` for a full inbox is not tested. |
| The template macro | `Lanes/Html/Syntax.lean`, 113 lines | It turns template syntax into `Html` values. What it produces is type-checked, but that it produces the element the template shows is not proved. | `Tests/Html.lean` compares rendered templates with the expected text. |

`lanes lint` fails when one of these files grows past the line count given here (rule
`trusted-size`), so trusted code cannot grow without this file changing.

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
- **What the gate guarantees, and under what.** *At most once* is proved. In every run of
  `gated sys`, for every system, bridge and configuration, no request id is output more often
  than it was input (`Http.answered_le_arrived`). The environment may crash and restart every
  actor, the gate included, and may lose, reorder and duplicate messages on every link but
  one: the link from the outside world to the gate must not duplicate. `Kernel.env` meets
  that, so the theorem holds of the events the kernel reports
  (`Http.kernel_answered_le_arrived`). "No id is answered twice" follows when the ids that
  arrive are distinct (`Http.answered_nodup`). That they are is trusted: `Lanes/Env/Http.lean`
  allocates them. *At least once* is not proved. `Http.deadlines_armed` proves that while the
  gate is up every waiting request has its deadline armed, in every environment. What remains
  is that the deadline fires, which is the progress assumption above, and that the gate does
  not crash and lose its mailbox, which holds on one shard. `Tests/Gate.lean` checks exactly
  once on two requests and shows each precondition is needed: a reused id is answered twice,
  a duplicating link from outside answers one arrival twice, and a gate that crashes leaves a
  request unanswered.
- **In-memory durability.** `Actor.recover` receives the actor's last state. The kernel keeps
  that state in memory, so it survives an actor stopping itself but not the process dying.
- **Environment model.** One shard stays within `Kernel.env`: reliable ordered links, no
  crashes other than an actor stopping itself. Properties proved under a stronger model than
  that do not apply to a running system.
- **Unbounded queue.** The kernel's message queue has no bound of its own. The inbox is
  bounded, which limits inputs waiting to enter, but one input may cause any number of
  messages between actors, and those are not limited.

## Not trusted

Actor `step` functions, `SysState.step`, the kernel (`Kernel.run1_sound`), the model checker's
exploration of a state (`SysState.mem_successors_iff`), its search (`Check.search_sound`), what a
complete PASS of `Check.system` means (`Check.system_sound`, for actor states and a driver state
whose `==` is equality, and properties that do not depend on message order),
the refinement theory and every theorem in `Lanes/` and `Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe`, `@[implemented_by]` or
`@[extern]` appears in them.
