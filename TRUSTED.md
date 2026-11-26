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
| The concurrent runtime | `Lanes/Actors/Runtime.lean` | It performs effects on real tasks, timers and channels; its conformance to `SysState.step` is not proved. | With `Config.record` on it records its events; `Tests/Runtime.lean` replays them through `SysState.run` and compares final states, under concurrent clients, self-stopping actors and timers. |
| `partial def post`, `perform`, `live` | `Lanes/Actors/Runtime.lean` | Actor tasks run forever and start each other, so they cannot be shown to terminate. | Same tests. |

## Assumptions the runtime makes

- **In-memory durability.** `Actor.recover` receives the actor's last state. The runtime keeps
  that state in memory, so it survives an actor stopping itself but not the process dying. Until
  the persistence adapter exists, an actor that claims durable state is only durable within one
  process lifetime.
- **Environment model.** The runtime stays within `Runtime.Config.env`: reliable ordered links
  between actors, unordered inputs from outside, no crashes other than an actor stopping itself.
  Properties proved under a stronger model than that do not apply to a running system.

## Not trusted

Actor `step` functions, `SysState.step`, the model checker's exploration
(`SysState.step_of_mem_successors`), the refinement theory and every theorem in `Lanes/` and
`Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe`, `@[implemented_by]` or
`@[extern]` appears in them.
