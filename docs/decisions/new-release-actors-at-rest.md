# D?. An actor at rest is released, and the kernel's theorems hold up to the starts that bring it back

`Lanes/Actors/{Actor,Release,Kernel,KernelSound,KernelTimers}.lean`, `Tests/Release.lean`,
`systems/ledger/Release.lean`. The kernel started an actor at its first message and kept its
cell for ever, so a system with an actor per identity grew with every identity ever addressed:
in `systems/ledger` a stranger guessing names added an actor a guess.

- *What may be released.* An actor declares the states that starting it gives, with nothing to
  do: `Actor.fresh`, with the proof `fresh_recover` that `recover init` is that state and no
  effect. The default declares none, so nothing changes for an actor that says nothing, and
  `mapEff` and `comapMsg` pass the declaration on, so a gated system releases what its inner
  system declares. The kernel releases actor `i` after it handles a message or a timer, when
  it is up, in a fresh state and has no timers (`Kernel.rest`): its cell leaves the map, which
  is how a cell that was never there reads, down at `init` with no timers. Its next message
  starts it as any first message does, and the start gives it back as it was. The snapshot
  shrinks with the map, since an image is the map's entries.
- *Mail is not checked.* An actor with mail still queued is released too. Knowing would cost a
  look through the queue at every message, and the message that comes up starts the actor
  again, which is one more unit of work for that message and nothing else. The decision is
  only the actor's state and timers. An actor is not released right after a start, or a
  message for an actor whose start gives a fresh state would start it for ever.
- *Why a declaration and not equality with `init`.* `init` has no decidable equality in
  general, and an actor whose `recover` arms timers or sends is not given back by a start
  with nothing to do, though it is at `init`. The ledger's `user n` declares its vacant state
  (`none`), which a log-in for an unknown name leaves as it is: nothing else had to change.
  A user who signed up is never at rest; releasing it needs its state saved elsewhere.
- *What is proved.* `SysState.Released a b`: `b` is `a` with some actors at rest released. It
  is a simulation both ways, up to the starts that bring released actors back
  (`Released.run`, `Released.run_back`), under an environment where nothing crashes: a crash
  keeps an actor's state where a release puts `init`. So the same inputs and outputs, in the
  same order, are possible from both (`Released.visible`). `SysState.Leads a events b`: a run
  from `a` that differs from `events` only in starts reaches a state `b` is with actors
  released. The kernel's theorems keep their names and say that: `Kernel.exec_sound`,
  `exec_reachable` (the kernel's state is a reachable state with actors released),
  `exec_visible` (and so has the same visible futures as that state). `exec_outputs`,
  `exec_wellFormed` and the fairness theorems hold as they were. `SysState.Equiv` does not
  identify a released actor with one up at rest, and is not the relation: it is a bisimulation
  step for step, which a release is not.
- *What a trace replays as.* The events a releasing kernel reports are a run of the semantics
  but for those starts, so a test that replays a recorded trace through `SysState.run` skips a
  start of an actor that is up (`Tests/Release.lean` does). A system whose actors declare
  nothing reports runs as before.
- *Checked first.* A kernel that releases and one that keeps every actor, driven side by side
  by a client that sends anything to anyone and lets the queue drain: the same outputs, the
  same events but for starts, the same states. A shell that does anything, the timers of each
  turn and a message waiting at once included, takes the two kernels' outputs into different
  orders, both of which the semantics allows, because a start takes a turn of its own. So that
  check holds the clock while a message waits, and a second one checks the releasing kernel
  against the semantics under any shell. A hundred thousand identities touched leave no actor
  in the kernel, alone or on a live shard, where the kernel that keeps them holds one each.
- *Replay.* Opting an actor in changes what the kernel does on replay, so a journal written
  before must not be replayed by the new step functions: the journal's name changes with the
  declaration (D36).
- *Next.* An actor that is idle but not at its initial state (a user who signed up and logged
  out) can be released only if its state lives somewhere else: written to storage when the
  actor rests, read back when its next message starts it, as a `recover` that reads. That is
  the persistence adapter, and a release then is a save the kernel asks for.
