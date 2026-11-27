# D?. One model with proofs, and runtimes proved against it (a proposal)

*A proposal. It moves no code. The owner agreed to the headline; the parts below are for the
owner to decide.*

Lanes makes two kinds of choice, and they are judged apart. One is the programming model. It is
where the guarantees come from, and it stays fixed. The other is how that model is run. Today
that is one implementation among several possible ones, and it is the narrow part. This decision
draws the line between the two. It says what a runtime has to prove to sit under an
application, and what the default runtime should be.

Rust is the nearest example. The language fixes what `async` code means, and executors such as
Tokio are libraries that run it. Lanes would fix what a system means, and runtimes would run it.
One difference matters, and it is below: here a library cannot tie itself to a runtime.

## The two layers

**Layer 1, the model.** It holds these, and they do not change with the runtime:

- actors with pure step functions (`Lanes/Core/Actor.lean`, `Lanes/Core/System.lean`);
- effects as data: `send`, `emit`, `after`, `cancel`, `stop` (D3, rule 2.4);
- the outside as models of services, with adapters that answer as inputs (D26, D61, D65,
  `Lanes/Outside/`);
- the semantics, `SysState.step` and its runs (`Lanes/Core/World.lean`, `Lanes/Core/Run.lean`, D6);
- the checker, which runs the real step functions (`Lanes/Check/`, D8, D33);
- every proof about an application.

What an application proves is a statement about Layer 1. `Videos.Site.listed_transcoded` and
the Raft refinement mention no thread, no file and no socket. Neither does
`Http.served_answered_le_arrived`.

**Layer 2, a runtime.** It takes a system and runs it on a machine. Today there is one:

- the kernel (`Lanes/Runtime/Kernel.lean`, D18);
- the shell around it (`Lanes/Runtime/IO/Shell.lean`);
- the journal and its files (`Lanes/Durable/`, D24, D29);
- waves on a pool (`Lanes/Runtime/Wave.lean`, D64, D73, D88);
- the gate and the HTTP server (`Lanes/Web/Http/Gate.lean`, `Lanes/Web/IO/Server.lean`, D43,
  D57);
- the transport between processes (`Lanes/Net/`, D30).

## The contract a runtime proves

Stated as the shape of a theorem, not as code. A runtime is a model of what its shell does:

- inputs arriving;
- outputs handed over;
- entries made durable;
- deaths of the process at any point;
- starts from what the storage holds.

The runtime is sound for a system `sys` and an environment `env` when this holds of every
execution of that model, deaths and starts included:

1. **Its outputs are a run of the semantics.** There is a run of `sys` from `SysState.init`,
   under `env`, whose events are the events the runtime reported. The outputs it handed over
   are that run's outputs, in order. There is one exception, which D24 states: an output
   produced after the last mark may be handed over again after a restart.
2. **No acknowledged input is lost.** An input is acknowledged once an output it caused has
   been handed over. After any number of deaths and starts, every acknowledged input is in the
   run once, at its place in the order. A restart is then not a crash in the semantics. The run
   goes on, so what is proved for an environment without crashes still holds across restarts.
3. **What it holds is a state the run reaches.** That state may have actors at rest released.
   Reads answered from it see a state of the run.

The second half of the contract says what stays trusted. A runtime names its IO and what that
IO is assumed to do: the threads, the storage and the network. It counts those lines in
`TRUSTED.md`, as today.

### Pieces already proved

Most of the contract is proved today, in pieces. What is missing is the one statement that
composes them. For now that composition is the prose of the runtime shell's row in
`TRUSTED.md`.

| Piece | Theorems |
|---|---|
| A kernel's operations are a run of the semantics, whatever the shell does | `Kernel.exec_reachable`, `Kernel.exec_outputs` (`Lanes/Runtime/KernelSound.lean`) |
| A turn and the journal describe the kernel exactly | `Journal.turns_kernel`, `Journal.turnAll_eq_exec` (`Lanes/Durable/Journal.lean`) |
| A batch hands an output over only after its entries are appended, and a peek sees the kernel the journal describes | `Batch.run_kernel`, `Batch.run_sound`, `Batch.run_peek` (`Lanes/Runtime/Batch.lean`) |
| Steps worked out in parallel give the sequential batch, value for value | `Kernel.runWaves_eq` (`Lanes/Runtime/Wave.lean`), `Batch.run_spread` |
| Replay rebuilds the kernel | `Journal.recover_kernel` |
| A snapshot is a memo of the replay | `Journal.resume_eq_recover`, `Kernel.abs_image_kernel` |
| A death at any byte leaves files that load as the kernel the shard had | `Journal.open?_cut`, `Disk.Holds.append_crash`, `Disk.Holds.save_crash`, `Disk.Torn.load_readings` (`Lanes/Durable/Disk.lean`) |
| The gate answers at most once and answers every request it admits | `Http.served_answered_le_arrived`, `Http.served_pending_answered`, `Gate.step_bounded` |
| A split system is the one system | `System.ShardsReachable.unsharded` (`Lanes/Runtime/ShardsSound.lean`), `System.SplitReachable.merged` |
| An old version's kernel carried across | `Migration` (`Lanes/Durable/Migration.lean`, D66) |

The first piece of work is the composed statement. It would be one theorem over a pure model
of the shell's loop, with a death allowed between any two acts. It needs no new mathematics.

### What stays trusted

These rows of `TRUSTED.md` stay trusted:

- the shell performs the acts `Batch.run` returns, all of them, in order (`Lanes/Runtime/IO/Shell.lean`);
- the parker (`Lanes/Runtime/IO/Park.lean`);
- Lean's `Task.spawn` and `Task.get`;
- the file system is the disk model (`Lanes/Durable/IO/Journal.lean`, `fsync` in `native/lanes.c`);
- the server and `Std.Net` do what their events say (`Lanes/Web/IO/Server.lean`);
- the transport and the claim that processes joined by it are `System.shards` (`Lanes/Net/IO/Peers.lean`, `Lanes/Net/IO/Node.lean`).

A new runtime adds rows of its own and proves the rest.

## Applications and libraries depend only on Layer 1

A step function cannot do IO (rule 2.4). So a library of actors, a behaviour such as
`Lanes.Schedule` or a model of a service cannot call a runtime, and cannot be tied to one. This
is why the split between language and runtimes splintered Rust's ecosystem and would not
splinter this one. In Rust a library that spawns a task or opens a socket picks Tokio or another
executor, and two such libraries may not mix. Here what a library does is data, and any runtime
that meets the contract runs it.

The one place where code touches a runtime is an adapter. It splits in two:

- **its model**, Layer 1: the service's model and the messages to it and from it. For example
  `Lanes/Outside/ObjectStore.lean` and `Lanes/Outside/Queue.lean`. The checker and the proofs
  use only this half.
- **its driver**, Layer 2: the IO that performs a request and returns the answer as an input.
  For example `Lanes/Web/IO/S3.lean`, `Lanes/Web/IO/Client.lean` and `Lanes/Outside/IO/Clock.lean`.
  Its behaviour against the model is trusted, and the oracles check it (D80).

Most adapters already have this shape. The rule would make it required: a model module imports
no driver.

## The default runtime: the best one for most applications

The default should be the best runtime for most programs: web applications, services, tools and
agents on one machine. It should not be a minimum. A system at the scale of a cloud database
writes a runtime of its own, and the contract is what lets it.

Proposed default:

1. **One ordered journal is the record.** As now (D24). The order of the journal is the order
   of the run, so every proof about one ordered run applies unchanged.
2. **The gate is off the hot path.** Today every request goes through one actor in the system
   (D43). Its decisions are pure (`Gate.step`). They can be made where a request arrives, with a
   theorem that the journal and the answers are those of the gate in the system. The gate's
   theorems keep their statements.
3. **Reads come from the state at batch boundaries** (D75, tacitresearch/lanes#58). A read is
   answered from a state the journal describes, without being journalled. The theorem to prove
   is that every read is a function of a reachable state. A read across several actors is taken
   at a batch boundary, so it sees one state.
4. **Steps are applied in parallel across cores, in waves.** The record stays one ordered
   journal, and the parallel run is proved equal to the sequential one. This is waves (D64,
   D73, D88), which exist and are proved (`Kernel.runWaves_eq`, `Batch.run_spread`), with the
   least new trusted code. Outputs are held until their entries are durable, as `Batch.run_sound`
   holds them now. D37 used the cores of a machine by running a process per core. Under this
   default an application gets them without sharding. Running without lockstep comes later, if a
   benchmark shows it is needed (below).
5. **Snapshots**, as now (D29). The default saves when the journal has outgrown the last
   snapshot, the rule D36 names as the better default, instead of a count the application picks.
6. **The journal's storage is pluggable.** `Journal.Log` in `Lanes/Runtime/IO/Shell.lean` is
   already the interface: past entries, the last save, `append` (durable on return), `note`,
   `save` and `close`. A local file is the default for development and one machine (`Lanes.Journal.Store.open`). Replicated storage is the
   choice for production. Each storage is trusted to meet the disk model, or proves it does.
7. **Later, a standby.** A second process tails the journal and replays it, and takes over when
   the primary dies, like a database with a replica. Its replay is the replay that is proved, so
   what is new is the hand-over: two primaries must never append at once. That is a fencing
   rule, and it can be model-checked like the courier.

**Why the default is not one journal per partition.** Most systems that persist keep a log per
entity or per partition. Examples are Akka's persistence, Temporal, Restate and Cloudflare's
Durable Objects. That scales across machines. It also makes three things worse for most
applications:

- Partition keys leak into the model. The application has to say which actors live together,
  and the checker and the proofs have to see it.
- Atomic steps across partitions become sagas: compensations, partial states and retries in
  application code, where today a step that touches two accounts is one step.
- The proofs get harder. Properties of one ordered run become properties of many runs with
  messages between them. `System.ShardsReachable.unsharded` shows this can be done, but only
  under `System.SteadyBoot` and lossy links.

One ordered journal with parallel apply keeps a single order. Single-thread designs of this kind
reach millions of operations a second on one machine (LMAX). That covers most applications.
Partitioned runtimes stay available as an opt-in for very large scale, built on
`System.shards`, D28 and D30.

## Parallel apply: what is proved and what it costs

*The owner has decided: waves first.*

**The theorem is equality to the journal's order.** It is not linearizability, and not
serializability. A parallel run gives the same kernel, the same events and the same outputs, in
the same order, as the journal's one order (`Kernel.runWaves_eq`). That is stronger than
serializable: a serializable run equals *some* order, and this equals *the* order the journal
records, as in Calvin. So every proof about one ordered run holds of the parallel run unchanged.

**Why it holds, and why applications owe no proof.** A step has the type
`State → Msg → State × Effects`. It reads and writes only its own actor's state, and it returns
its effects as data. So steps of different actors commute. The type enforces this; an
application proves nothing. The runtime keeps two orders:

- the steps of one actor run in journal order;
- a message is handled only after the step that sent it.

Fairness is a separate result about liveness (D27, `Lanes/Semantics/FairRuns.lean`). It is about
which events a run takes, not how a run is spread over threads, so it still holds.

**Waves first, free-running later.** In a wave every step must finish before the next wave
begins. In a free-running runtime there is no lockstep: an answer leaves once its input is
durable and its step is done. The difference shows with a slow step:

- with waves, a slow step stalls its wave;
- free-running, it stalls only its own actor.

Waves come first because they are proved and add the least trusted code. Whether free-running
is worth building is decided by a benchmark with mixed step costs: mostly steps of a few
microseconds, and now and then one of 50 ms, measuring the 99th percentile of latency.

In every mode, steps of one busy actor run one after another. The fix is to split the actor.
Large states have been fine since tacitresearch/lanes#70 (D84, D88). What a large state still
costs is memory, and the time to save a snapshot and to replay.

**Costs, written down:**

- The speedup needs work spread across actors. One actor gets no faster.
- Small batches run on the calling thread. An object that several threads can see is not
  updated in place (D32, and the conventions in `AGENTS.md`). So handing a state to another
  thread can turn an in-place update into a copy. D73's pace keeps cheap work on the shard's
  thread for this reason (`Lanes/Runtime/Pace.lean`).
- The real-time order of logs and of calls to the outside varies from run to run. Replay is
  still deterministic, because the journal holds the inputs and their order.
- So the proof must show that the outside world's model allows effects to leave in a real-time
  order other than the journal's. The models already let the outside answer late, again or out
  of order (D61, D65, `Lanes/Outside/`); the contract states it.
- The machinery that hands steps to threads is trusted code. Today it is Lean's `Task.spawn` and
  `Task.get`, and the shell's timing for the pace: small, but more than none (`TRUSTED.md`, the
  runtime shell's row).
- The checker already explores every order of different actors' steps (`Lanes/Check/System.lean`
  explores every interleaving of deliveries and timeouts). So the parallel runtime adds no
  behaviour the checker has not seen.

## Guidance for authors and agents

The default runtime is fastest for code written this way. The docs and the template should say
so:

- **One actor per entity:** a member, a video, an account. Not one actor for a whole table.
  Parallel apply needs work spread across actors.
- **Small steps.** A step is microseconds.
- **Heavy work leaves the step.** It goes through an effect to a worker, and the answer comes
  back as an input. `examples/videos` does this with its transcode worker (D91).
- **The test kit reports the slowest steps,** so a step that grows slow is seen in tests, not in
  production.

Even so, the default runtime should degrade gracefully. One slow step must never take the whole
site down. With waves, a slow step delays its wave and no more, and the gate still answers `504`
at its deadline (D43). The benchmark above measures how far that is from good enough.

## Leaks to remove

These are places where a runtime's choices show up in application code today:

- **The journal's name has the gate's timeout and bound in it.** `ServerConfig.journalName`
  (`Lanes/Web/IO/Server.lean`) adds them because the gate's step reads them (D43). So changing
  a server timeout makes the application refuse its own journal. Another branch is fixing this
  now. An application should state the version of its step functions, and nothing else should
  rename its journal.
- **Runtime settings are passed by the application.** `Http.serve` takes a `Runtime.Config`
  (`inboxCapacity`, `batch`, `snapshotEvery`, `workers`, `parallel`, `pace`) beside the
  `ServerConfig`. The ledger sets `snapshotEvery := 256` in `examples/ledger/Main.lean`.
  These should be the runtime's defaults, with overrides kept for tuning.
- **`ServerConfig` mixes three concerns:** HTTP limits, the journal (`journal`, `system`) and
  the server's threads (`ioThreads`). The first belongs to the HTTP adapter's driver. The
  second is the application's name and version plus the storage the runtime is given. The
  third is the runtime's.
- **Sharding is the application's.** Using more cores today means `System.shard sys hosts`,
  a process per shard, `Http.serveShard` and peers' addresses (D37, `Lanes/Net/IO/Node.lean`).
  Request ids are each process's own, so a response must come from an actor of the process that
  took the request; that row of `TRUSTED.md` says so. With parallel apply in the default, none
  of this is needed for cores. It remains for the partitioned runtime.
- **Codecs stay with the application.** `Http.Saving` (an identity, each actor's state and
  messages, the outputs) is not a leak. Any runtime that persists needs to read back what it
  wrote, so the codecs are part of how an application is described, whatever runtime runs it.

## The order of work

1. **The contract.** The composed theorem over a model of the shell, from the pieces above. It
   changes no behaviour.
2. **The gate off the hot path,** with its theorems restated and proved of the new place.
3. **Reads from the state** (D75), with the reachable-state theorem and a peek across several
   actors at a batch boundary.
4. **Parallel apply in waves as the default**, on what D64, D73 and D88 built. Then the
   benchmark with mixed step costs and p99 latency, which decides whether a free-running runtime
   is built. If it is, it is proved equal to the journal's order as waves are.
5. **The journal storage interface** made public and documented. That is `Journal.Log` with its
   obligations stated, plus a second storage that meets them.
6. **A standby** that tails the journal, with a fencing rule, model-checked.

Each step keeps every application's proofs as they are, because none of them changes Layer 1.

## Questions for the owner

1. **Should the contract be a Lean structure** that a runtime instantiates with its proof, or a
   theorem the default runtime proves with others following its shape? A structure makes
   "your own runtime" a typed interface. It also fixes the statement early.
2. **Is at-least-once delivery of outputs across a restart (D24) part of the contract,** or
   should the default runtime deduplicate outputs so that the contract promises exactly once?
3. **Which replicated storage comes first for the journal:** a replicated block volume, S3 with
   conditional writes, PostgreSQL, or a Raft group of our own (`examples/raft-kv`)?
4. **Should the runtime move out of `Lanes`** into a package of its own, so that an application
   imports Layer 1 and chooses a runtime? Or should it stay in the library, behind the interface,
   for now?
5. **Should runtime settings move out of `Http.serve`'s arguments** and into a runtime value that
   the application starts with one call, given the system, its codecs, its version and its
   storage?
6. **Does the partitioned runtime belong in this repository,** or does it stay an example
   (`examples/raft-kv`) until someone needs it?
