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
| The HTTP adapter | `Lanes/Env/Http.lean` | It reads and writes sockets and keeps the table of waiting requests in IO. | Manual `curl` runs only. It becomes an actor in `docs/PLAN.md` step 4. |

The runtime's decisions (routing, start, stop, timers, which mail a stopped actor loses) are
not in this table. They are in `Lanes/Actors/Kernel.lean` and proved in
`Lanes/Actors/KernelSound.lean`.

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
exploration of a state (`SysState.mem_successors_iff`), the refinement theory and every theorem in `Lanes/` and
`Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe`, `@[implemented_by]` or
`@[extern]` appears in them.
