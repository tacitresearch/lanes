# D121. The step context as built, and poison messages

Status: Accepted

Issue #241. D101 fixed the step's final shape: a step is told the moment (`now`, `seed`) and who
sent its message, and the moment is recorded so traces replay. D110 then removed the journal, so
`now` and `seed` come from the runtime, and D116 made the actors run free on worker threads. This
decision records where the code departs from D101's text, and how a step that never ends (a
poison message) is handled.

## The shape

As D101 has it, with three differences:

```lean
structure Moment where
  now_ms : Nat := 0
  seed : UInt64 := 0

inductive Sender (Id : Type) where
  | outside | actor (i : Id) | timer

structure Ctx (Id : Type) extends Moment where
  src : Sender Id := .outside

structure Actor (S Msg Eff : Type) (Id : Type := Unit) where
  init : S
  step : S → Msg → S × List Eff := fun s m => stepAt {} s m
  stepAt : Ctx Id → S → Msg → S × List Eff := fun _ => step
  recover : S → S × List Eff := fun _ => (init, [])
  recoverAt : Moment → S → S × List Eff := fun _ => recover
  fresh : S → Bool := fun _ => false
  fresh_recover : ∀ t s, fresh s = true → recoverAt t init = (s, []) := by ...
```

- **No `Actor.Plain`.** D101 planned a second structure for actors that ignore the context, with
  a lift into the new one. Instead `step` and `stepAt` are two fields that default to each other
  (and `recover` and `recoverAt`): an actor gives one of them. An actor that ignores the context
  is written exactly as before, with no lift and no word changed; one that reads it gives
  `stepAt` (and `recoverAt`). Generic statements about steps change instead: they quantify over
  the context, or name the one the semantics gives (`Monotone.step`, `Inductive.step`, the
  refinement rules of `Lanes/Semantics/Simulation.lean`). The semantics, the checker and the runtime call only `stepAt` and `recoverAt`.
  `Sender` is generic in the identifier type, not in the signature, so a library actor stays
  generic; a join maps each side's senders (`Sender.left`, `Sender.right`: an actor of the other
  side is `.outside`, as in `Lanes/Proof/JoinSound.lean`'s projections), and an actor written for
  one identifier type enters a bigger system through `Actor.mapSrc`.
- **A tick may move the clock anywhere.** `Event.tick m` sets `SysState.clock` to `m` and is
  always enabled, where D101 allowed only ticks forward. The runtime's workers read the clock
  concurrently: worker A reads 5, worker B reads 6, B's step is recorded first. Each worker's
  steps, and each actor's, see the time go forward, but the record of the whole system does not,
  and making it would serialise the workers. So the semantics does not promise that `now` never
  decreases; a proof may not assume it. The checker still ticks only forward, along the moments a
  scenario lists (`Scenario.moments`, empty by default, so nothing ticks and every step sees
  `{}`), which keeps the state space finite.
- **The kernel is timeless.** The reference kernel (`Lanes/Runtime/Kernel.lean`) tells every step
  `{}`; its refinement proof is unchanged in substance. The free-running scheduler's model
  (`Sched.Step.step`) is told a moment `t` with each step, and the step is two events of the
  semantics, `[.tick t, step]`, so `Sched.Run.reachable` covers the context.

Starting the system (`SysState.init`) recovers the boot actors at the moment `{}`, since no tick
comes before them. A restart of one actor later (`Event.start`) is told the clock.

## What the runtime tells a step

`now_ms` is the wall clock read when the runtime starts plus the monotonic time since, in
milliseconds since the Unix epoch, as D101 has it without the journal's maximum. Setting the wall
clock back while the runtime runs changes nothing; timers' deadlines are on the same clock. The
seed comes from a SplitMix64 generator per worker, seeded from the operating system
(`IO.getRandomBytes`), so drawing one takes no lock. When `Config.record` is on, the record has
`.tick t` before each step, so a replay through `SysState.run` gives each step what it was told.

## The request id

D101's context has no request id: it has the sender. A request's id travels in the message, as
the web front's `ReqId` does (`Lanes/Web/Http/Front.lean`), and a structured log takes it from
there. `Ctx.src` is what the context exposes about where a message came from.

## Poison messages

A step that panics returns `default` in compiled Lean and goes on; a step that overflows the
stack or runs out of memory aborts the process. Neither can be caught. What can be seen is a
step that does not end: a loop, or work far too large for its input. Lean cannot interrupt a pure
computation, so the worker running it is lost either way.

Options, by reach and cost:

1. **A watchdog that restarts the process** (chosen). Each worker notes when its step began; a
   thread wakes every quarter of `Config.stepLimitMs` (30 s by default, `0` turns it off) and,
   when a step has run longer, reports it (`Config.onStuck`: the worker, the actor's hash, the
   kind of step, how long) and ends the process with status 75, for its supervisor to start
   again. Actors are volatile (D110), so the restart is the semantics' `Event.restart`, which
   `Sched.Step.restart` already has: everything in memory, the poisoned message with it, is
   dropped. Cost: one store per step and one thread that sleeps. Reach: every step that does not
   end, and only those.
2. **A crash of the receiver** (D101's quarantine of a message between actors). Only the actor
   whose step is stuck loses its mailbox and timers, and is recovered. But the stuck thread
   cannot be stopped: it keeps a core until its step ends, which for a loop is never, and if it
   ends it must not write back. That needs a generation on the slot, a transition of the
   scheduler's model that abandons a running step, and a limit after which leaked threads restart
   the process anyway. It keeps the other actors' state, which a process restart loses. It is the
   next step if restarts prove too costly.
3. **Fuel in the step's type.** Every step would count; every proof would carry it. It catches
   loops but not large work, and costs on every step.

A poisoned input that a client sends again kills the process again, every `stepLimitMs`. Refusing
it after a restart needs a record that outlives the process, which belongs in the store (D110), and
is not built. An application whose proofs assume no restarts (`EnvModel.mayRestart = false`) gets
no guarantee across the watchdog's restart; it may turn the watchdog off, and a stuck step then
holds its actor and its worker until it ends.
