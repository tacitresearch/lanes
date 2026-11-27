| Runtime | A kernel of pure functions (routing, start and stop, timers, batching, idleness) proved to follow the semantics whatever its caller does (`Kernel.exec_reachable`, `Kernel.exec_outputs`), releasing an actor that is back where a start puts it with no timers and proved to change nothing anyone can see by it (`Kernel.exec_visible`; a hundred thousand identities touched leave none in the kernel), never to lose a pending timer or spin on one (`Kernel.exec_wellFormed`), and to let neither timers nor messages starve the other (`Kernel.WellFormed.step_of_queued`, `step_of_due`), inside a shell that only performs what a pure function of each batch returns, proved to keep the journal describing the kernel, to hand an output over only after the entries that produce it are written and to save only where every output is handed over (`Batch.run_kernel`, `Batch.run_sound`): one thread per shard, bounded inbox; the actors of a wave step in parallel on Lean's task pool where the shard's own timing says it pays (`Runtime.Config.parallel := .auto`), proved to change nothing the kernel does whatever is chosen (`Kernel.runWaves_eq`, `Batch.run_spread`). A message costs the same at 1,000 and 100,000 actors, and a step updates its actor's state in place, on the shard's thread and on the pool, so on the shard's thread it costs the same whatever the state's size (`Kernel.takeState`, `Kernel.Plan.real`, `Tests/Scale.lean`). Durable with a journal: the shard replays what its kernel was asked and returns in the same state, proved for whole and torn journals and tested with SIGKILL; a journal that is damaged, another system's, or written with another codec is refused and left as it is (`Journal.open?`), and so is one whose read fails, which is not taken for a journal that is not there (`Journal.Disk.Torn.load_readings`), and one process at a time holds a journal. What the inbox decides is proved for every capacity and every sequence of operations: a take returns exactly what was taken in since the last, in order (`Mailbox.batch_since_take`), it never holds more than its capacity (`Mailbox.Reachable.bounded`), and no sleeper or waiting sender is forgotten (`Mailbox.woken_after_rest`, `Mailbox.wake_since_take`). With codecs for its actors the shard saves its kernel and cuts the journal, so a restart replays only what came after the last save: starting from a snapshot gives exactly what replaying the whole history gives (`Journal.resume_eq_recover`), and a process that dies at any point of a save, or at any byte of an append, leaves files that load as the kernel it had (`Journal.Disk.Holds.save_crash`, `append_crash`), tested by killing a process while it saves. A deploy that changes a state or message type reads the old version's files through an upgrade: they are replayed as the old version did, the kernel is migrated with a proof that every state an old actor reaches lands in an inductive invariant of the new one, and that invariant holds of every actor afterwards (`Migration.inv_exec`, `Journal.Upgrade.inv_load`); dying anywhere in the migration's writes gives the same migrated kernel (`Journal.Upgrade.begin_crash`), and the crash theorems go on from the migrated kernel (`Journal.Upgrade.holds`); `examples/migration` Several shards: `System.shard` is a system as one shard sees it, on the unchanged kernel, and `Peers` joins shards in different processes. Shards joined behave as the one system, at the level of the semantics: every state of a well-routed run, read as one state, is a state the system reaches alone up to `SysState.Equiv`, for two shards (`System.SplitReachable.merged`) and for any number (`System.shards sys hosts` with `hosts : σ.Id → Fin n`, `System.ShardsReachable.unsharded`), so its invariants hold there (`System.Invariant.split`, `split_state`, `shards`, `shards_state`); model-checked on three shards with the bank and a relay of boot actors with timers and stops | `Lanes/Runtime/`, `Lanes/Durable/`, `Lanes/Proof/Lossy.lean`, `Lanes/Durable/IO/Journal.lean` |

- A journal is cut only if the application gives codecs for its actors (`Journal.Store.actors`,
  `Http.Saving`); without them it grows without bound and a restart replays all of it. A
  codec's law is an equality, so a state that holds a map holds a `Std.ExtTreeMap`
  (`Codec.extTreeMap`): a `TreeMap` or a `HashMap` has no codec. The codecs are derived
  by `lanes_data` from the declarations of the state and the messages, or written with
  `Codec.struct%` and `Codec.sum%` for a type it does not accept (recursive, with indices). The
  order in which a save replaces the journal's past is proved to lose nothing wherever the
  process dies (`Journal.Disk.Holds.save_crash`), over a model of the two files. That the
  operating system's rename is atomic, that flushed bytes survive the process and that synced ones
  survive a loss of power is trusted. Every flushed write is synced (`fsync`), about 0.2 ms a
  batch on the disk it was measured on.
- A journal is begun at any path that has none, unless the store says otherwise
  (`Journal.Store.create`). An application whose shard makes promises to others, as a Raft
  node does with its vote, has to say so itself, as `raftNode` does.
- A migration needs the old version's system, its step functions and codecs, in the new binary
  for as long as files of that version may exist. `Http.serve` takes no upgrades yet: its
  system is the application's behind the gate, and a migration would have to be lifted through
  the gate. What carries over a migration is what each new actor keeps by its own steps; an
  invariant proved only from boot, or refinement, does not, and a shard migrated twice is
  covered by `Journal.Upgrade.inv_load` only for the first migration.
- A journal's name has to cover everything its replay reads: the version of the step
  functions and every setting they use, timeouts among them, since a timer is due at the
  clock's reading plus the configured delay. Nothing checks that a name does. `raft-kv` puts
  its whole `Config` in the name, so a timeout of a node that has run cannot be changed.
- A save writes the whole kernel, and the shard does nothing else meanwhile. `raft-kv` never
  compacts its log, so a node's snapshot grows with every command it has ever taken.
- Cutting off a write that did not finish, and cutting a journal at a save, replace the
  journal file by a new one, which gets default permissions; `.tmp` files left by a process
  killed in between are not cleaned up.
- A timer does not advance while the process is down, and after a restart it also loses the
  time that had passed since the last journal entry before the process died.
- A step that emits very many outputs is quadratic in their number (`Kernel.performAll`
  appends one at a time): 20,000 outputs from one step take most of a second.
- The runtime releases only an actor whose state is one a start gives it (`Actor.fresh`, which
  an actor declares; the default declares none). An actor that is idle in any other state keeps
  its cell for good, so a session-per-user system still grows with its users. Releasing it means
  its state must live somewhere else, so this waits for the persistence adapter.
- The events a releasing kernel reports are a run of the semantics but for the starts that
  bring released actors back, so a replay through `SysState.run` must skip a start of an actor
  that is up. Declaring `fresh` changes what an old journal replays to: its name must change.
- One shard takes about 1.8 million inputs a second from one sender and about a million from
  four that contend for its inbox, on a four-core machine; its kernel alone does between two
  and three million turns a second. With a journal every batch is one write, so the disk is
  the limit there. A shard with nothing to do sleeps, and waking it costs tens of microseconds.
- That a pending timer fires in time is proved as far as the kernel goes: its agenda holds
  exactly the pending timers, it never tells the shell to sleep past one, and it fires one that
  is due on its next step or, when a message is waiting too, the step after
  (`Kernel.exec_wellFormed`, `Kernel.WellFormed.wait_of_due`, `step_of_due`, `wait_for_ms`).
  That the clock advances and the shell's sleep ends is assumed (see `TRUSTED.md`).
- The kernel's message queue has no bound of its own (see `TRUSTED.md`).
- Work outside a step goes through the jobs actor (`Lanes.Jobs`). On a journal, a job whose
  result was not journalled when the process died is attempted again with its key, so a far
  side that must not act twice has to deduplicate by it.
- Actors step in parallel only with `Runtime.Config.workers` above one, and then only within a
  wave, their steps committed in queue order by one thread; the gate of an HTTP server is one
  actor. A step handed to another thread costs a microsecond or two more, in Lean's reference
  counts of objects threads share, so cheap steps run slower that way
  (`docs/decisions/D64-actors-run-in-parallel.md`).
- Lean never updates in place an object another thread has seen, so each actor the pool steps
  has its state copied once a wave, in its task, and once more by its next step on the shard's
  thread. With `parallel := .on`, a write to one of two busy actors whose states hold a million
  numbers costs about a tenth of a millisecond, where it costs a microsecond on the shard's thread.
  `.auto` keeps such steps on the shard's thread (`docs/decisions/D88-waves-in-place.md`).
