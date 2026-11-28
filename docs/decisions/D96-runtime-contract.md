# D96. One model with proofs, and runtimes proved against it

Status: Partly superseded by D110-volatile-actors.md (the default runtime, and the contract's clauses that rest on a journal: one order, output ids, no acknowledged input lost across a restart)

*Status: Accepted. The contract below is experimental until the multi-core runtime implements
it: until then its statement may still change.*

Lanes makes two kinds of choice, and they are judged apart. One is the programming model. It is
where the guarantees come from, and it stays fixed. The other is how that model is run. That is
one implementation among several possible ones, and it is the narrow part. This decision draws
the line between the two. It says what a runtime has to prove to sit under an application, which
assumptions about the environment each runtime provides, and what the default runtime is.

Rust is the nearest example. The language fixes what `async` code means, and executors such as
Tokio are libraries that run it. Lanes fixes what a system means, and runtimes run it. One
difference matters, and it is below: here a library cannot tie itself to a runtime.

## The two layers

**Layer 1, the model.** It holds these, and they do not change with the runtime:

- actors with pure step functions (`Lanes/Core/Actor.lean`, `Lanes/Core/System.lean`);
- effects as data: `send`, `emit`, `after`, `cancel`, `stop` (D3, rule 2.4);
- the outside as models of services, with adapters that answer as inputs (D26, D61, D65,
  `Lanes/Outside/`);
- the semantics, `SysState.step` and its runs (`Lanes/Core/World.lean`, `Lanes/Core/Run.lean`, D6);
- the environment a property is proved under (`EnvModel`), and the named sets of assumptions
  about it (below);
- the neutral image of a system's state (the data format, below);
- the checker, which runs the real step functions (`Lanes/Check/`, D8, D33);
- every proof about an application.

What an application proves is a statement about Layer 1. `Videos.Site.listed_transcoded` and
the Raft refinement mention no thread, no file and no socket. Neither does
`Http.served_answered_le_arrived`.

**Layer 2, a runtime.** It takes a system and runs it on a machine. The default runtime is:

- the kernel (`Lanes/Runtime/Kernel.lean`, D18);
- the shell around it (`Lanes/Runtime/IO/Shell.lean`);
- the journal and its files (`Lanes/Durable/`, D24, D29);
- waves on a pool (`Lanes/Runtime/Wave.lean`, D64, D73, D88);
- the gate and the HTTP server (`Lanes/Web/Http/Gate.lean`, `Lanes/Web/IO/Server.lean`, D43,
  D57);
- the transport between processes (`Lanes/Net/`, D30).

## The contract a runtime proves

**The contract is a Lean structure.** A runtime is a value of it, with its proof. That makes
"your own runtime" a typed interface. It is experimental until the multi-core runtime
implements it, because that runtime is the first to test it against something other than one
thread. The shape, not the code:

```lean
structure Runtime where
  /-- A pure model of what the runtime's IO does with one system: inputs arriving, steps,
  entries made durable, outputs handed over, deaths at any point, and starts. -/
  Exec : System σ → Type
  /-- What an execution reported: its events, each output handed over with its id, the inputs
  acknowledged, and the inputs quarantined. -/
  report : Exec sys → Report sys
  /-- The environment its runs are runs under, and the named sets of assumptions it meets. -/
  env : System σ → EnvModel σ
  provides : List Assumptions
  provides_hold : ∀ a ∈ provides, a.Holds (env sys)
  /-- Whether every execution has one order (a journal), and whether a read may see several
  actors at one point of the run. -/
  oneOrder : Bool
  cutReads : Bool
  /-- Clauses 1 to 5 below, for every system and every execution. -/
  sound : ∀ (sys : System σ) (e : Exec sys), Sound sys (env sys) oneOrder cutReads (report e)
```

The structure lives beside the semantics, in the layer of actors, so that a runtime written
elsewhere depends on no runtime of Lanes. A runtime is sound for a system `sys` when these hold
of every execution of its model, deaths and starts included:

1. **Its events are a run of the semantics.** There is a run of `sys` from `SysState.init`,
   under `env sys`, whose events are the events the runtime reported, up to the starts that
   bring actors at rest back (D51). The run keeps each actor's own order, and puts each message's
   send before its delivery. A runtime with `oneOrder` proves more: the run's order is the order
   of its journal. Every output handed over is an output of that run.
2. **Outputs are handed over at least once, each with a stable id.** An output may be handed
   over again after a restart (D24): exactly once is not promised. Each output carries an id that
   is unique in the life of the system and the same each time the output is handed over. An
   adapter's driver passes it on as the idempotency key where the service takes one, and the
   service's model treats a repeat under one key as one effect (`Idempotent.at_most_once`). The
   default runtime's id is the position in the history of the entry that produced the output,
   with the output's place among that entry's outputs. Replay is deterministic, so the id is the
   same after any restart. Waves keep it, because a parallel run gives the outputs in the
   sequential order (`Kernel.runWaves_eq`). A runtime with no single history defines its own id
   (the sketch of a runtime of objects below does).
3. **No acknowledged input is lost.** An input is acknowledged once an output it caused has
   been handed over, or once the runtime has told its sender it is taken. After any number of
   deaths and starts, every acknowledged input is in the run once, at its place in its actor's
   order. A restart is then not a crash in the semantics. The run goes on, so what is proved for
   an environment without crashes still holds across restarts.
4. **A quarantined input counts as one that never arrived** (below). It is in the report as
   quarantined and in the run nowhere.
5. **What it holds is a state the run reaches.** What it holds in memory and in storage together,
   read as one state, is a state of the run, with actors at rest released (`SysState.Released`)
   and actors hibernated (below). A read of one actor sees that actor's state in a state of the
   run. A read of several actors sees them in one state of the run only if the runtime has
   `cutReads`. An image the runtime exports is a state of the run.

The second half of the contract says what stays trusted. A runtime names its IO and what that
IO is assumed to do: the threads, the storage and the network. It counts those lines in
`TRUSTED.md`.

### Pieces already proved

Most of the contract is proved for the default runtime, in pieces. What is missing is the one
statement that composes them. Until it is written, that composition is the prose of the runtime
shell's row in `TRUSTED.md`.

| Piece | Theorems |
|---|---|
| A kernel's operations are a run of the semantics, whatever the shell does | `Kernel.exec_reachable`, `Kernel.exec_outputs` (`Lanes/Runtime/KernelSound.lean`) |
| A turn and the journal describe the kernel exactly | `Journal.turns_kernel`, `Journal.turnAll_eq_exec` (`Lanes/Durable/Journal.lean`) |
| A batch hands an output over only after its entries are appended, and a peek sees the kernel the journal describes | `Batch.run_kernel`, `Batch.run_sound`, `Batch.run_peek` (`Lanes/Runtime/Batch.lean`) |
| Steps worked out in parallel give the sequential batch, value for value | `Kernel.runWaves_eq` (`Lanes/Runtime/Wave.lean`), `Batch.run_spread` |
| Replay rebuilds the kernel | `Journal.recover_kernel` |
| A snapshot is a memo of the replay | `Journal.resume_eq_recover`, `Kernel.abs_image_kernel` |
| A death at any byte leaves files that load as the kernel the shard had | `Journal.open?_cut`, `Disk.Holds.append_crash`, `Disk.Holds.save_crash`, `Disk.Torn.load_readings` (`Lanes/Durable/Disk.lean`) |
| Actors at rest released, with the same visible futures | `SysState.Released.visible` (`Lanes/Runtime/Release.lean`), `Kernel.exec_visible` |
| The gate answers at most once and answers every request it admits | `Http.served_answered_le_arrived`, `Http.served_pending_answered`, `Gate.step_bounded` |
| A split system is the one system | `System.ShardsReachable.unsharded` (`Lanes/Runtime/ShardsSound.lean`), `System.SplitReachable.merged` |
| An old version's kernel carried across | `Migration` (`Lanes/Durable/Migration.lean`, D66) |

The first piece of work is the composed statement, as the default runtime's value of the
structure. It is one theorem over a pure model of the shell's loop, with a death allowed between
any two acts. It needs no new mathematics. The ledger already carries a theorem down to the
kernel's environment (`Ledger.implements_timed_kernel`); the composed statement does the same
for every system.

### What stays trusted

These rows of `TRUSTED.md` stay trusted for the default runtime:

- the shell performs the acts `Batch.run` returns, all of them, in order (`Lanes/Runtime/IO/Shell.lean`);
- the parker (`Lanes/Runtime/IO/Park.lean`);
- Lean's `Task.spawn` and `Task.get`;
- the file system is the disk model (`Lanes/Durable/IO/Journal.lean`, `fsync` in `native/lanes.c`);
- the server and `Std.Net` do what their events say (`Lanes/Web/IO/Server.lean`);
- progress: a queued input is eventually handled and a due timer eventually fires
  (`TRUSTED.md`, "Progress"), on which every theorem about fair runs rests;
- the transport and the claim that processes joined by it are `System.shards` (`Lanes/Net/IO/Peers.lean`, `Lanes/Net/IO/Node.lean`).

A new runtime adds rows of its own and proves the rest.

## Named sets of environment assumptions

Every theorem about a system picks its own premises about the environment: which links lose,
duplicate or reorder, which actors may crash, and whether the run is fair. Which runtime meets
them was left to prose. Once runtimes can be swapped, "which of my theorems hold on runtime R?"
needs a mechanical answer. A theorem whose premise a runtime breaks is still a theorem, so
nothing fails; it silently stops being about the deployed system.

So the premises get names, as predicates on `EnvModel` beside `EnvModel.Faultless` in
`Lanes/Core/System.lean`, each a structure whose fields are the premises theorems already state.
A theorem states its premises by these names. A runtime states which sets it provides
(`provides` above), and proves them of its environment. A theorem holds on a runtime when the
runtime provides every set the theorem names.

The premises the examples' and the library's theorems use:

| Premise, as theorems state it | Set | Theorems that use it |
|---|---|---|
| `env.Faultless`: no link loses or duplicates, no actor crashes | `Faultless` | `Counter.implements`, `Bank.money_conserved`, `Upload.implements`, `Server.implements` |
| The link from outside to an actor does not duplicate: `(env.link none i).duplicating = false` | `InputsOnce` | `Rookery.implements`, `RaftKV.cluster_implements`, `Http.served_answered_le_arrived`, `Ledger.implements_timed` |
| No link duplicates | `NoDuplicates` | `KV.implements`, `Ledger.implements_timed` (each user's link to the ledger) |
| A link is ordered | `Ordered` | `Ledger.implements_timed`, `Ledger.moves_serve` |
| A link loses nothing | `Lossless` | `Ledger.implements_timed`, `Reminders.delivery_answered`, `Videos.report_settles`, `System.Run.Fair.handled` |
| An actor does not crash: `env.mayCrash i = false` ("the ledger does not crash", "the scheduler does not crash") | `Up i` | `Ledger.implements_timed`, `Http.served_pending_answered`, `Reminders.delivery_ends`, `Reminders.delivery_answered`, `Videos.job_ends`, `Videos.report_settles`, the theorems of `Lanes/Semantics/Schedule.lean` and `Lanes/Semantics/Jobs.lean` |
| The run is fair: `r.Fair` | `Fair`, a property of runs, not of `EnvModel` | every liveness theorem, among them `Http.served_pending_answered`, `Reminders.delivery_answered`, `Videos.report_settles` |
| Booting loses no message: `System.SteadyBoot` | not a set: an obligation of the system, which a runtime may require | `System.ShardsReachable.unsharded`, `System.SplitReachable.merged` |

Two more premises are not about `EnvModel` and stay where they are. The outside does what its
model allows (`Outside.allows`, `Lanes/Outside/`): trusted, and checked by the oracles (D80). A
configuration without seeded bugs, such as `Videos.Config.Honest`, is about the application,
not the environment.

Bundles name what a kind of runtime gives:

- `OneProcess`: every link reliable and ordered, no actor crashes. It is `EnvModel.reliable`,
  which is the kernel's environment (`Kernel.env`), and it implies every set above but `Fair`.
- `Network`: inputs from outside arrive once; links between actors may lose, reorder and
  duplicate. It is what `EnvModel.distributed` allows, and what `Link.network` promises.

What each runtime provides:

| Runtime | Provides | Requires of the system |
|---|---|---|
| The default: one journal, one process, waves | `OneProcess`; `Fair` by trust (progress, above); `oneOrder`; `cutReads` | nothing |
| Shards in processes joined by the transport (`System.shards`, D30) | each process as the default; between processes, `Network` | `System.SteadyBoot` |
| One journal per partition (an example) | within a partition, as the default; between partitions, `Network` | `System.SteadyBoot` |
| A runtime of objects, after Durable Objects (sketch below) | `InputsOnce`, `Up i` for every actor; `Network` between actors, or `Lossless` and `NoDuplicates` with an outbox, and `Ordered` with sequence numbers too; `Fair` by trust | nothing |

The checker takes any `EnvModel`. A check names the runtime it models by the sets it uses, so a
check and a proof can be compared with what is deployed.

## Applications and libraries depend only on Layer 1

A step function cannot do IO (rule 2.4). So a library of actors, a behaviour such as
`Lanes.Schedule` or a model of a service cannot call a runtime, and cannot be tied to one. This
is why the split between language and runtimes splintered Rust's ecosystem and does not
splinter this one. In Rust a library that spawns a task or opens a socket picks Tokio or another
executor, and two such libraries may not mix. Here what a library does is data, and any runtime
that meets the contract runs it.

The one place where code touches a runtime is an adapter. It splits in two:

- **its model**, Layer 1: the service's model and the messages to it and from it. For example
  `Lanes/Outside/ObjectStore.lean` and `Lanes/Outside/Queue.lean`. The checker and the proofs
  use only this half.
- **its driver**, Layer 2: the IO that performs a request and returns the answer as an input.
  For example `Lanes/Web/IO/S3.lean`, `Lanes/Web/IO/Client.lean` and `Lanes/Outside/IO/Clock.lean`.
  Its behaviour against the model is trusted, and the oracles check it (D80). It is given each
  output's id (clause 2).

The rule: a model module imports no driver.

## One runtime value per application, in a package of its own

**An application starts with one call, `Lanes.run app runtime`.** `app` describes the
application: its system, its bridge and its views, its codecs (`Http.Saving`), the name and
version of its step functions, and its upgrades. `runtime` is a value: the default, given its
storage, or another. Runtime settings (the fields of `Runtime.Config`, the server's threads) are
the runtime's defaults, with overrides kept for tuning. They leave `Http.serve`'s arguments.

**The runtime is a package of its own,** in the split into layered packages (#101): the
semantics and the checker, actors, a runtime, durability, then web, PostgreSQL and AWS, each
usable without the layers above it, under one version and one `lanes` umbrella package. An
application imports the Layer 1 packages and picks a runtime.

## The default runtime: the best one for most applications

The default is the best runtime for most programs: web applications, services, tools and agents
on one machine. It is not a minimum. A system at the scale of a cloud database writes a runtime
of its own, and the contract is what lets it.

1. **One ordered journal is the record** (D24). The order of the journal is the order of the
   run, so every proof about one ordered run applies unchanged.
2. **The gate is off the hot path.** The gate is one actor in the system that every request goes
   through (D43). Its decisions are pure (`Gate.step`). They are made where a request arrives,
   and recorded in the journal as outcomes (the data format, below), with a theorem that the
   journal and the answers are those of the gate in the system. The gate's theorems keep their
   statements.
3. **Reads come from the state at batch boundaries** (below).
4. **Steps are applied in parallel across cores, in waves.** The record stays one ordered
   journal, and the parallel run is proved equal to the sequential one (`Kernel.runWaves_eq`,
   `Batch.run_spread`; D64, D73, D88). Outputs are held until their entries are durable, as
   `Batch.run_sound` holds them. D37 used the cores of a machine by running a process per core;
   under this default an application gets them without sharding. Waves become the default only
   after the videos test below.
5. **Snapshots** (D29). The default saves when the journal has outgrown the last snapshot, the
   rule D36 names as the better default, instead of a count the application picks.
6. **The journal's storage is pluggable.** `Journal.Log` in `Lanes/Runtime/IO/Shell.lean` is the
   interface: past entries, the last save, `append` (durable on return), `note`, `save` and
   `close`. The storages come in this order:
   1. a local file synced with `fsync`, whose sealed segments are shipped to S3. A segment is
      sealed and uploaded when the journal moves to the next one. A lost disk loses the tail
      since the last segment shipped, and the documentation says so;
   2. S3 with conditional writes: the journal kept in S3 itself, each append a put that fails if
      another writer appended first. The condition is also the fencing a standby needs;
   3. a Raft group (`examples/raft-kv`).

   Each storage is trusted to meet the disk model (`Lanes/Durable/Disk.lean`), or proves it does.
7. **Later, hibernation** of actors that hold state (below).
8. **Later, a standby.** A second process tails the journal and replays it, and takes over when
   the primary dies, like a database with a replica. Its replay is the replay that is proved, so
   what is new is the hand-over: two primaries must never append at once. That is a fencing
   rule, model-checked like the courier.

**Why the default is not one journal per partition.** Most systems that persist keep a log per
entity or per partition: Akka's persistence, Temporal, Restate and Cloudflare's Durable Objects.
That scales across machines. It also makes three things worse for most applications:

- Partition keys leak into the model. The application has to say which actors live together,
  and the checker and the proofs have to see it.
- Atomic steps across partitions become sagas: compensations, partial states and retries in
  application code.
- The proofs get harder. Properties of one ordered run become properties of many runs with
  messages between them. `System.ShardsReachable.unsharded` shows this can be done, but only
  under `System.SteadyBoot` and lossy links.

One ordered journal with parallel apply keeps a single order. Single-thread designs of this kind
reach millions of operations a second on one machine (LMAX). That covers most applications.

**A partitioned runtime is an example,** not part of the library, until someone needs it. It is
built on `System.shards`, D28 and D30, and provides the sets in the table above.

## One actor stays the atomic unit

A step changes one actor's state (rule 3.6). The model has no step over several actors, and this
decision keeps it so, as Pike, Helland, TigerStyle and Durable Objects do: what must touch two
actors goes through a protocol or a single owner. Steps over several actors are deferred, not
refused. Adding them later breaks nothing: no theorem about one-actor steps changes, and a
journal with one order is the order they need (Calvin's design).

The cost is plain. The flagship applications, `examples/rookery` and `examples/videos`, are each
one actor, with `Id := Unit` (`examples/rookery/Rookery/System.lean`,
`examples/videos/Videos/System.lean`; the video site is joined with the scheduler, which is its
only other actor). Each choice is deliberate: every claim is about one atomic owner. But one
actor gets no faster with waves, and its state grows in one value.

So, **before waves become the default, `examples/videos` is split into one actor per user,** to
check that the work spreads: that a page view or an upload touches one user's actor and the
actors it sends to, that the refinement can be proved again over the split system, and that a
load of many users fills the cores. The result decides the guidance for authors below.

## Hibernation

Actors are virtual already. Every identity names an actor that always exists and starts on
demand, so there is no spawn and no registry (`Lanes/Core/System.lean`, D2). D51 releases an
actor at rest from memory: one in a state its declaration says a start gives (`Actor.fresh`),
with no timers (`Kernel.rest`). Its next message starts it again, and the kernel's theorems hold
up to those starts (`SysState.Released.visible`, `Kernel.exec_visible`).

What is missing is **hibernation of actors that hold state**: a signed-up user, a video with its
comments. Such an actor is never at rest, so it stays in memory for ever, and memory grows with
every identity that ever held state. D51 says it: releasing one needs its state saved elsewhere.

How it fits the contract:

- **Hibernation is unobservable.** The runtime moves an actor's cell, its state, whether it is
  up and its timers, out of memory into storage, and loads it back exactly before the actor's
  next message or timer. It does not run `recover`: a load is not a start. So a hibernated
  actor is no crash, the run has no event for it, and every set the runtime provides still
  holds. Clause 5 reads memory and storage together, which is why it says "in storage".
- **To prove:** the kernel with some cells in storage reads as the kernel with those cells in
  its map. Then `Kernel.exec_reachable` and the theorems built on it carry over unchanged. It is
  simpler than D51's relation, which needs starts.
- **Storage:** the per-actor sections of the image, which the data format reserves (#91,
  "Reserved, not designed: actors one at a time"): a section kind in the image, an index from
  identity to section, and a journal entry kind that points at an actor's saved state. An
  actor hibernated between snapshots is written as a section, with an entry pointing at it, so
  that replay finds it.
- **Timers:** the runtime keeps an index of the timers of hibernated actors, deadline to actor,
  so that a timer wakes its actor.
- **Eviction:** when to hibernate an actor (the least recently used, under a memory bound) is the
  runtime's policy. It is unobservable, so the contract says nothing more of it.
- **Waves:** loading an actor is IO, done before the wave its step is in.

D51's release stays: it needs no storage. Hibernation is runtime work, and it changes nothing in
Layer 1.

## Reads

A page view is a request: it enters the journal and is synced before it is answered, and a site
read far more than it is written pays a sync per view. Reads are answered from the state
instead, without a journal entry (the closed #58, branch `claude/reads`, decision draft D75 on
it). Its theorems, as that branch names them, are in `Lanes/Runtime/PeekSound.lean` there:

- **The peek.** A read is a command through the shard's inbox, answered after every command
  taken before it, once the batch in progress has its entries appended and synced and its
  outputs handed over (`Batch.run_peek`). It is offered without waiting (`Runtime.tryPeek`), and
  the state is rendered off the shard's thread.
- **A read leaves no trace.** A batch with its peeks taken out appends the same journal, hands
  over the same outputs and leaves the same kernel (`Batch.run_erase_peeks`). Replay and
  recovery are those of the inputs alone.
- **A read never shows a state a crash could take back,** and every output before it has been
  handed over (`Batch.chain_sound`, `Batch.chain_peek`).
- **A read after a write's response sees it,** in a state the semantics reaches by a run that
  put out that response first (`Batch.chain_peek_after`). This is linearizability at the peek,
  per actor. Tying a read to the application's spec is the application's own invariant,
  `answer s = read (abs s)`, where it wants one.

Decided beyond the prototype:

- **Over several actors:** one peek is answered with the states of several actors taken at the
  same batch boundary, so a read sees one state of the run, not several peeks at different
  points. This is what `cutReads` names.
- **With deadlines:** a read has a deadline and a bound, as a request has, and a place in the
  drain, so a stopping server waits for it.
- **As a `view` beside the bridge:** an application declares its views, `Request → Option
  (Read sys)`, beside `Bridge`, not as an argument of `serve`.

**A shared reference to the state was rejected.** The shell could write each actor's state to a
reference after each batch, and readers would read it without a command. But Lean does not
update an object in place once another thread may see it. Every state published that way would
be copied at its actor's next step, read or not, and the kernel relies on updating states in
place (D84, D88). The peek costs only when a read comes.

## Quarantine

Failure is crash-only (rule 3.3), with quarantine (#99): an entry whose step crashed the process
at two starts in a row is skipped, recorded and reported (`lanes journal quarantined`), and it
can be driven again by hand.

**A quarantined input counts as one that never arrived.** That is always a legal run: in the
semantics, which inputs arrive is the environment's choice, so the run without the input is a run
under every environment, and every safety theorem holds of it. It was never acknowledged: its
step never finished, so no output it caused was handed over. What follows:

- Its entry keeps its place in the journal, marked, so the positions of later entries, and so
  the ids of their outputs, do not move.
- A request quarantined is answered at the front, outside the system, as a refusal is. The
  gate's theorems are about requests it admitted, and this one never was.
- An input driven again is a new arrival, at the end of the journal, with new output ids.

A step on a message between actors, or on a timer, is not an input. Skipping it would lose a
message, which is legal only under a lossy link or a crash. That case is open (questions).

## Parallel apply: what is proved and what it costs

**Waves first.** Free-running apply is built only if a benchmark with mixed step costs shows a
gain at the 99th percentile of latency.

**The theorem is equality to the journal's order.** It is not linearizability, and not
serializability. A parallel run gives the same kernel, the same events and the same outputs, in
the same order, as the journal's one order (`Kernel.runWaves_eq`). That is stronger than
serializable: a serializable run equals *some* order, and this equals *the* order the journal
records, as in Calvin. So every proof about one ordered run holds of the parallel run unchanged,
and so do the output ids.

**Why it holds, and why applications owe no proof.** A step has the type
`State → Msg → State × Effects`. It reads and writes only its own actor's state, and it returns
its effects as data. So steps of different actors commute. The type enforces this; an
application proves nothing. The runtime keeps two orders:

- the steps of one actor run in journal order;
- a message is handled only after the step that sent it.

Fairness is a separate result about liveness (D27, `Lanes/Semantics/FairRuns.lean`). It is about
which events a run takes, not how a run is spread over threads, so it still holds.

**Waves and free-running.** In a wave every step must finish before the next wave begins.
Free-running, there is no lockstep: an answer leaves once its input is durable and its step is
done. The difference shows with a slow step:

- with waves, a slow step stalls its wave;
- free-running, it stalls only its own actor.

Waves come first because they are proved and add the least trusted code. The benchmark that
decides free-running has mostly steps of a few microseconds and now and then one of tens of
milliseconds, and measures the 99th percentile. A free-running runtime, if built, is proved equal
to the journal's order as waves are.

In every mode, steps of one busy actor run one after another. The fix is to split the actor.
Large states are updated in place (D84, D88); what a large state still costs is memory, and the
time to save a snapshot and to replay.

**Costs:**

- The speedup needs work spread across actors. One actor gets no faster.
- Small batches run on the calling thread. An object that several threads can see is not
  updated in place (D32, and the conventions in `AGENTS.md`). So handing a state to another
  thread can turn an in-place update into a copy. D73's pace keeps cheap work on the shard's
  thread for this reason (`Lanes/Runtime/Pace.lean`).
- The real-time order of logs and of calls to the outside varies from run to run. Replay is
  still deterministic, because the journal holds the inputs and their order.
- So the outside world's model must allow effects to leave in a real-time order other than the
  journal's. The models let the outside answer late, again or out of order (D61, D65,
  `Lanes/Outside/`); the contract states it.
- The machinery that hands steps to threads is trusted code: Lean's `Task.spawn` and `Task.get`,
  and the shell's timing for the pace (`TRUSTED.md`, the runtime shell's row).
- The checker explores every order of different actors' steps (`Lanes/Check/System.lean`
  explores every interleaving of deliveries and timeouts). So the parallel runtime adds no
  behaviour the checker has not seen.

## The data format

The data format (#91) is decided with this contract in mind:

- **The neutral image is the one the model defines,** in Layer 1, the same for every runtime:
  each actor's state and whether it is up, its timers with their deadlines in order, the messages
  in flight in order, the outputs not yet handed over, the clock and the index in the history.
  It abstracts to a `SysState`. Clause 5 is stated over it: an image a runtime exports is a state
  of the run. It is what a migration maps and what a move to another runtime carries. The index
  in the history is in it so that output ids keep moving forward across a save, a migration and
  a move.
- **Journal entries stay the runtime's own** (`Journal.Entry`: `input`, `advance`, `batch`,
  `handed`, `snapshot`). The manifest names the runtime and the version of its policy, so a tail
  is replayed only by the runtime that wrote it. A move to another runtime goes through the
  neutral image with an empty tail. A runtime section beside the image holds what only its own
  runtime reads.
- **The journal stores decoded inputs,** `(ReqId, σ.In)`, and the gate's decisions as their
  outcomes. That is what takes the gate off the hot path, and it takes the gate's settings out
  of the journal's name.
- **Per-actor sections** are reserved in the image, with an entry kind that points at one. They
  are the storage of hibernation, and the native form of a runtime of objects.

## The test of generality: a runtime of objects

A contract that fits only the runtime it was written from is not a contract. The test is a
runtime after Cloudflare's Durable Objects, sketched here on paper: where the contract could not
express it, the contract changed.

**The mapping:**

- **Each actor is an object,** named by its identity's encoding (`Http.Saving`'s codecs). Virtual
  actors map directly: an object exists for every name and starts on demand.
- **State is per object.** A step is one transaction of its object: load the cell (state, up,
  timers, outbox), run `step`, write the new cell. An object holds its outgoing messages until
  its write is durable, as `Batch.run_sound` holds outputs.
- **Timers are alarms.** An object has one alarm. The cell keeps its timers in order of deadline,
  and the alarm is set to the earliest. Arming a pending timer again restarts it, and `cancel`
  removes it, as in the semantics.
- **Sends are calls between objects.** A call may fail with the caller not knowing whether it
  arrived, and calls from different objects arrive in any order. So, as they are, the links
  between actors are `Network`: they lose, reorder and, with retries, duplicate. With an outbox
  in the sender's cell, retried until acknowledged, and a table of seen messages in the
  receiver's, the links are `Lossless` and `NoDuplicates`. With a sequence number per link and
  a hold-back at the receiver, they are `Ordered` too.
- **Eviction is hibernation for free.** The cell is in storage after every step, and an evicted
  object loads it back exactly, without `recover`. So no actor crashes (`Up i` for every actor);
  `stop` still runs `recover` at the next start, as the semantics says.
- **Inputs** come through a front that routes `x` to the object of `(sys.accept x).1`. The gate
  must be off the hot path: as one actor it would be one object for the whole application.
- **Outputs** are handed over at least once, with the id `(actor, the actor's count of steps,
  place)`.
- **Trusted:** that an object's storage is durable when its write returns, that an object runs
  one step at a time, and that alarms and calls are eventually delivered (`Fair`).

**What the contract had to change to express it:**

- **One order.** A runtime of objects has no journal and no total order, only each object's
  history. Clause 1 asks for a run that keeps each actor's order and puts sends before their
  deliveries; such a run exists from the objects' histories. The journal's order is the stronger
  guarantee `oneOrder`, which the default runtime proves. No example theorem needs it: their
  statements are about runs of the semantics.
- **Output ids.** A position in one history does not exist here, so the id is defined by each
  runtime, unique and stable, not fixed as a journal position.
- **Acknowledged inputs** are in the run at their place in their actor's order, not in "the"
  order.
- **What it holds** is memory and storage together, and a read of several actors at one point
  needs `cutReads`. A runtime of objects reads one actor at a time; several objects read at
  once are at different points of the run. Its export of a neutral image needs a consistent cut:
  inputs stopped and messages drained, or a snapshot protocol (Chandy and Lamport).
- **The environment depends on the system,** since the runtime's configuration (an outbox or
  not) decides what each link is. `env : System σ → EnvModel σ`.

Nothing in it needs a change to Layer 1: no new effect, and no step over several actors, which
Durable Objects do not have either.

## Guidance for authors and agents

The docs and the template say how to write for the default runtime:

- **Small steps.** A step is microseconds.
- **Heavy work leaves the step.** It goes through an effect to a worker, and the answer comes
  back as an input. `examples/videos` does this with its transcode worker (D91).
- **The test kit reports the slowest steps,** so a step that grows slow is seen in tests, not in
  production.
- **An actor per entity,** a member, a video, an account, rather than one actor for a whole
  table, if the videos test shows the work spreads. If it does not, the guidance is one actor
  with fast collections, as LMAX does.
- **Outputs carry their ids.** An adapter's driver puts the id where the service takes an
  idempotency key, since an output may be handed over twice.

Even so, the default runtime degrades gracefully. One slow step must never take the whole site
down. With waves, a slow step delays its wave and no more, and the gate still answers `504` at
its deadline (D43). The benchmark above measures how far that is from good enough.

## Leaks to remove

These are places where a runtime's choices show up in application code:

- **The journal's name has the gate's timeout and bound in it.** `ServerConfig.journalName`
  (`Lanes/Web/IO/Server.lean`, `Lanes/Web/Http/JournalName.lean`) adds them because the gate's
  step reads them at replay (D43). `Http.regateUpgrade` carries a journal across changed gate
  settings when `serve` is given its `saving`. With the gate's decisions recorded in the journal
  (the data format), replay reads no gate setting and the settings leave the name. An
  application states the version of its step functions, and nothing else renames its journal.
- **Runtime settings are passed by the application.** `Http.serve` takes a `Runtime.Config`
  (`inboxCapacity`, `batch`, `snapshotEvery`, `workers`, `parallel`, `pace`) beside the
  `ServerConfig`, and the ledger sets `snapshotEvery` in `examples/ledger/Main.lean`. These
  become the runtime value's (`Lanes.run app runtime`).
- **`ServerConfig` mixes three concerns:** HTTP limits, the journal (`journal`, `system`) and
  the server's threads (`ioThreads`). The first belongs to the HTTP adapter's driver. The
  second is the application's name and version plus the storage the runtime is given. The
  third is the runtime's.
- **Sharding is the application's.** Using more cores by processes means `System.shard sys
  hosts`, a process per shard, `Http.serveShard` and peers' addresses (D37,
  `Lanes/Net/IO/Node.lean`). Request ids are each process's own, so a response must come from an
  actor of the process that took the request; that row of `TRUSTED.md` says so. With parallel
  apply in the default, none of this is needed for cores. It remains for the partitioned runtime.
- **Codecs stay with the application.** `Http.Saving` (an identity, each actor's state and
  messages, the outputs) is not a leak. Any runtime that persists needs to read back what it
  wrote, so the codecs are part of how an application is described, whatever runtime runs it.

## The order of work

1. **The contract** as the Lean structure, with the named sets of assumptions, and the default
   runtime's value of it: the composed theorem over a model of the shell. Stable output ids and
   quarantine with it. It changes no behaviour of a run.
2. **The gate off the hot path,** with decoded inputs in the journal (#91) and the gate's
   theorems restated and proved of the new place.
3. **Reads from the state:** the peek, over several actors, with deadlines, as a `view`.
4. **`examples/videos` split into one actor per user,** to check that the work spreads.
5. **Parallel apply in waves as the default,** on what D64, D73 and D88 built. Then the benchmark
   with mixed step costs at p99, which decides whether a free-running runtime is built.
6. **The journal storage interface** made public and documented: `Journal.Log` with its
   obligations stated. Sealed segments shipped to S3, then S3 with conditional writes, then Raft.
7. **`Lanes.run app runtime`,** and the runtime as its own package (#101).
8. **Hibernation,** on the image's per-actor sections.
9. **A standby** that tails the journal, with a fencing rule, model-checked.

Each step keeps every application's proofs as they are, because none of them changes Layer 1.

## Details settled

Each detail below is settled at the default it states (the owner's rule: small and reversible choices are taken at their default, and changed later if needed).

Each has a default, taken unless the owner says otherwise.

1. **Should an output id name its journal?** An id of history position and place repeats in
   two applications, or in one whose journal was started afresh, and a service keyed on it would
   take a new effect for a repeat of an old one. *Default:* yes. The id is the journal's own
   identifier, made at random when the journal is created and kept in the manifest, with the
   position and the place.
2. **What does quarantine do with a step on a message between actors, or on a timer?** Skipping
   it loses a message, which is a legal run only where the link to that actor is lossy or the
   actor may crash. *Default:* the runtime holds that actor, with the message first in its mail,
   reports it, and lets the rest run. The run so far is still a run, so every safety theorem
   holds; that actor's liveness is lost, and the report says so. Where the provided sets allow
   that actor to crash, the runtime crashes it instead.
3. **What if splitting videos does not spread the work?** *Default:* waves stay opt-in, the
   guidance becomes one actor with fast collections, and steps over several actors are
   considered again.
4. **Should the structure have a second instance from the start?** A structure with one instance
   fixes only what that instance does. *Default:* yes: a pure model of the runtime of objects
   above, with its proof and no IO, written with the default runtime's value, as the test that
   the structure is general.
