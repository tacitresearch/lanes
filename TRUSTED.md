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
| The runtime shell | `Lanes/Actors/Runtime.lean`, 185 lines | It takes commands from an inbox, reads the clock, calls the kernel and hands the kernel's outputs to the adapter. That it hands them on unchanged is not proved. | `Tests/Runtime.lean` replays recorded events through `SysState.run` and compares final states, and tests timers, back-pressure and stopping; `Tests/Scale.lean` measures that a message costs the same at 1,000 and 100,000 actors. |
| The HTTP adapter's IO | `Lanes/Env/Http.lean`, 129 lines | It reads requests from sockets, gives each an id no other has, hands them to the gated system and writes the gate's one response for each. It answers `405` and, when the inbox is full, `503` itself. | `Tests/Web.lean` makes real requests over a socket, including fifty at once. |
| The template macro | `Lanes/Html/Syntax.lean`, 113 lines | It turns template syntax into `Html` values. What it produces is type-checked, but that it produces the element the template shows is not proved. | `Tests/Html.lean` compares rendered templates with the expected text. |

`lanes lint` fails when one of these files grows past the line count given here (rule
`trusted-size`), so trusted code cannot grow without this file changing.

The runtime's decisions are not in this table: routing, start, stop, which mail a stopped
actor loses, which timer is due, how long to sleep, how much to do before looking at the inbox
again, and when the shard is idle. They are in `Lanes/Actors/Kernel.lean` and proved in
`Lanes/Actors/KernelSound.lean`. Nor are the HTTP adapter's (which requests are waiting, when
one times out, when too many are pending): they are the gate actor in `Lanes/Http/Gate.lean`,
model-checked in `Tests/Gate.lean`.

## Assumptions the runtime makes

- **The shell passes things on unchanged.** `Kernel.exec_reachable` proves that any sequence
  of kernel operations, in any order, with any inputs, any clock readings and timers fired
  early, late, twice or never armed, leaves the kernel in a state the semantics can reach, and
  that the events it reported are a run reaching it. `Kernel.exec_outputs` proves the outputs
  it hands the shell are exactly the outputs of that run. So no property of reachable states
  depends on the inbox, the clock or the scheduler. What is assumed is that the shell gives
  outputs to the adapter as the kernel gave them, and that an input it reports is the one that
  arrived.
- **Progress.** That a queued input is eventually handled and a pending timer eventually fires
  is not proved. It rests on the inbox delivering, the clock advancing, and on the kernel's
  agenda holding every pending timer, which is tested (`Tests/Runtime.lean`) and not yet proved.
- **The gate's two preconditions.** Each request is answered exactly once provided request ids
  are never reused, which `Lanes/Env/Http.lean` ensures by allocating them, and provided the
  gate does not crash, which holds on one shard. `Tests/Gate.lean` shows both are needed.
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
