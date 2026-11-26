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
| The runtime shell | `Lanes/Actors/Runtime.lean`, 156 lines | It takes commands from an inbox, calls the kernel and carries out the kernel's commands. That it passes results on unchanged is not proved. | `Tests/Runtime.lean` replays recorded events through `SysState.run` and compares final states. |
| The HTTP adapter's IO | `Lanes/Env/Http.lean`, 125 lines | It reads requests from sockets, hands them to the gated system and writes the gate's one response for each. | `Tests/Web.lean` makes real requests over a socket, including fifty at once. |

| The template macro | `Lanes/Html/Syntax.lean`, 113 lines | It turns template syntax into `Html` values. What it produces is type-checked, but that it produces the element the template shows is not proved. | `Tests/Html.lean` compares rendered templates with the expected text. |

`lanes lint` fails when one of these files grows past the line count given here (rule
`trusted-size`), so trusted code cannot grow without this file changing.

The runtime's decisions (routing, start, stop, timers, which mail a stopped actor loses) are
not in this table. They are in `Lanes/Actors/Kernel.lean` and proved in
`Lanes/Actors/KernelSound.lean`. Nor are the HTTP adapter's (which requests are waiting, when
one times out, when the system is too busy): they are the gate actor in `Lanes/Http/Gate.lean`,
model-checked in `Tests/Gate.lean`.

## Assumptions the runtime makes

- **The inbox.** The shell assumes its channel hands over each command exactly once.
- **Timers.** A timer wakes no earlier than asked.
- **In-memory durability.** `Actor.recover` receives the actor's last state. The kernel keeps
  that state in memory, so it survives an actor stopping itself but not the process dying.
- **Environment model.** One shard stays within `Kernel.env`: reliable ordered links, no
  crashes other than an actor stopping itself. Properties proved under a stronger model than
  that do not apply to a running system.
- **Unbounded queue.** The kernel's message queue has no bound of its own. The shell admits one
  input per batch of kernel steps while the shard is busy, and the inbox is bounded, so the
  outside is pushed back; messages actors send each other are not limited.

## Not trusted

Actor `step` functions, `SysState.step`, the kernel (`Kernel.run1_sound`), the model checker's
exploration of a state (`SysState.mem_successors_iff`), its search (`Check.search_sound`, which
assumes `Model.Respects`; that the actor instance in `Check.system` meets it is not yet proved),
the refinement theory and every theorem in `Lanes/` and `Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe`, `@[implemented_by]` or
`@[extern]` appears in them.
