# D?. Reads answered from the state of an actor, without entering the system (a proposal)

The first application of the first release, `examples/videos`, found this its first problem:
every page view is a request, so it enters the journal with its headers, is synced before it is
answered, and is replayed at every start until a snapshot cuts it. A site that is read a thousand
times for each write pays a sync per view and keeps a journal that grows with its reads. This
surveys four ways out, recommends one, and prototypes it, opt-in: nothing changes for an
application that does not name its reads. It is for the owner to decide.

## What is promised today

Each option is measured against what the framework proves of a served system:

- **The gate.** No request is answered more often than it arrived
  (`Http.served_answered_le_arrived`), a waiting request keeps its deadline armed, and in a fair
  run every request the gate admits is answered (`Http.served_pending_answered`): at most once by
  proof, exactly once by proof and a check that an arrival reaches the gate.
- **Linearizability.** `System.Implements`: the system's traces of inputs and outputs are traces
  of its `Service.spec` (D42); `Server.implements` for the `Server` behaviour, `Rookery.implements`,
  `KV.implements`.
- **Crash recovery.** An output is handed over only after the entries that produce it are
  appended (`Batch.run_sound`), and a start rebuilds the kernel the journal leads to
  (`Journal.recover_kernel`, `Journal.Disk.Holds.append_crash`).
- **Replay determinism.** The journal describes the kernel (`Batch.run_kernel`): it is a journal
  of what the kernel was asked (D24), and replaying it gives the same state.
- **The checker** explores every input a driver sends; a view is an input like any other.

What a view costs now, measured below: a journal entry of the request (230–290 bytes for a bare
`GET /` with curl's headers, 340 for a page view of the video site), and a sync. The shell already
syncs once a batch, for everything that arrived together (D32, `Batch.run`), so under load the
syncs are shared; alone, a view waits for its own.

## (a) Queries on the state

The application names some requests as reads: a pure `Request → Option (Read sys)`, where a
`Read` is an actor and `answer : sys.State actor → Response`. The server answers a read from the
state of that actor as the shard has it, never entering the system.

*How.* The runtime already has a peek (`Batch.Command.peek`, `Runtime.state`): a command in the
inbox, answered by the shell after every command taken before it, once its entries are appended
and its outputs handed over (`Batch.run_peek`). A read is a peek offered without waiting
(`Runtime.tryPeek`), whose state is rendered on a task of Lean's pool, off the shard's thread.
The alternative to the peek is a published reference: the shell writes each actor's state, or the
kernel, to a shared reference after each batch and readers read it with no command. It answers
without waiting for the batch in progress; it shares every state with other threads at every batch
whether read or not (below, what sharing costs), and to keep "a read after a write's response sees
it" it must be written before the batch's outputs are handed over. The peek costs only when read.

*Cost.* No entry, no sync, no request id, no step: one command through the inbox, and the read
waits for the batch in progress, including that batch's sync. The state is then shared with the
rendering task, which costs on the shard's thread in proportion to the state, once for each read
that follows a write: on an actor whose state is an array of 10⁶ numbers, a write costs 0.9–1.5
ms without reads (the kernel copies such a state at each step anyway, below; 46 µs a write for 10
numbers), and 3.4–4.2 ms when a read comes between two writes, while reads with no write between
them cost 16–66 µs each. That the extra is Lean marking an object that crosses threads, which
walks it, is likely and not confirmed here. For states of the size of the examples there is
nothing to measure. A read of several actors is several peeks, at different points of the run:
not one consistent state.

*What it breaks.*

- The gate's theorems are untouched, since they are about the requests it receives; they say
  nothing of reads. A read has no deadline (it waits at most for the batch in progress), is not
  counted in `maxPending`, and is not in `Server.inFlight`, so a drain does not wait for it. It is
  answered once because a promise is resolved at most once, with the state or, if the shard
  stops first, `503`, as is a read the full inbox refuses: trusted, and tested.
- `System.Implements` is about the system's traces, and a read is not an event of the system: the
  theorem holds as it is and says nothing of reads.
- Crash recovery and replay are not broken, and that is proved: a peek leaves nothing.

*The theorems that replace them* (`Lanes/Runtime/PeekSound.lean`, gated):

- `Batch.run_erase_peeks`: a batch with its peeks taken out appends the same journal, hands over
  and records the same, and leaves the same kernel, count and waiters. So the journal, and what
  replay and recovery make of it, is that of the requests that entered, whatever was read and
  when. It needs the batch not to start with a save due, which holds after every batch (the
  flush that ends one leaves none due) and at a start, unless the journal replayed is longer than
  `snapshotEvery`, as after lowering it: then a read first in the first batch moves the first
  save before the first input.
- `Batch.chain_sound`, `Batch.chain_peek`: over the shard's whole history (`Batch.chain`, the
  batches one after another as the shell runs them; that the shell is that loop is trusted, as
  it was), every act is sound where it falls, and a peek is answered with the state of the
  kernel the journal so far describes once every output that journal produced is handed over. A read never shows a state a crash could take back, and
  every response it could reflect has been handed over.
- `Batch.chain_peek_after`: a peek asked after an output was handed over is answered with the
  actor's state in a world the semantics reaches, up to actors at rest released, by a run that
  put that output out first; from boot or from any journal a start replays. With the output a
  write's response, a read issued after the write's response sees the write, and every event of
  the run before it.

Together: a read is linearizable at its peek with respect to the system's own runs. The peek
falls between the read's arrival and its answer, and the state it reads is the state of the run
at that point. Two cautions, both per actor:

- *It sees the actor's state, not what is on its way to it.* A transfer's response is put out when
  the source debits itself; the credit is a message to the other account. A journalled balance
  query waits in the kernel's queue behind the credit and sees it; a read peeks at once and may
  not, if the batch's fuel ran out first. Whether that is allowed is the spec's: the bank's
  invariant, `conserved`, counts credits in flight, so a balance without the credit is a state
  it allows.
- *Lifting to the spec is the application's.* For the `Server` behaviour the actor's state is the
  spec's state, so `answer` of it is a read of a state the spec's history reaches. Elsewhere a
  read is right when `answer s = read (abs s)` holds of every reachable state, for a read of the
  spec's state (a `Service` has none today) and the abstraction its refinement proof uses. That is
  an invariant, and the checker checks it.

*The checker.* Reads are not events, so there is nothing new to explore, and fewer interleavings
than with views as inputs. That a read answers what the journalled request would is a property
of reachable states: `Tests/Reads.lean` proves it for the bank by `rfl` (the account's `query`
changes nothing and emits what the read renders), and in general it is an `always` property.

## (b) Reads as inputs that are not journalled

The read goes through the actor as now; the shell does not journal it.

*Cost.* A step on the shard's thread for each read, its rendering included; no sync; no entry.

*What it breaks.* Replay. `Batch.run_kernel` no longer holds: the read's arrival puts the request
in the gate's waiting list, arms its deadline and takes a timer token, its messages interleave in
the kernel's queue with journalled ones, and its response is an output no entry produced, so
`Batch.run_sound`'s "handed over exactly what the journal produced" fails. Replaying without the
reads gives another kernel unless every read leaves the kernel exactly as it found it, which is
false of the gate (tokens, the order of the agenda) and of any actor whose read changes its state
(a view count). The gate's theorems and `Implements` hold of the live run, but after a crash the
system goes on from the state of a run that never had the reads. The theorem that would replace
them is that a read message is a no-op on the kernel (`(k.handle i q).kernel = k`, outputs
aside), proved per actor and false of the gate, so the gate would have to let reads by: which is
(a) with a step added.

*The checker.* Unchanged: reads are inputs.

## (c) Batching the sync

The shell already appends and syncs once a batch: sixteen connections get about three times the
journalled requests a second of one (below), on one sync each batch. A wider window (waiting a few
milliseconds to gather more) would trade latency for fewer syncs. It breaks nothing, since
`Batch.run_sound` and `Batch.run_kernel` hold for any batching, and the checker does not see it.
It does nothing for the journal's growth or for replay: every view is still an entry, replayed at
every start until a snapshot.

## (d) Caching rendered pages

- *Before the system, in IO* (as `arrive` answers before it): a hit is not journalled, a miss is.
  Keeping it right needs the system to say what each write invalidates, before the write's
  response is handed over; otherwise a read after a write's response may see the page before it.
  `examples/kv-cache` proves that a read cache breaks refinement (`KV.caching_not_implements`).
  The cache would be trusted state, and the theorem left is at best "eventually fresh".
- *On (a)*, keyed by the state a page is rendered from: right by construction, since `answer` is a
  pure function of the state, and it saves only the rendering. The rendering is not where the time
  goes (below: a read and a request through the system without a journal serve about as many a
  second).

Neither touches the journal's growth unless the cache answers before the system, and that is (a)
with staleness.

## Recommendation

(a), through the peek. It is the only option that removes the entry and the sync of a view,
breaks no theorem the framework has, and comes with theorems of its own, proved: reads leave
nothing (`Batch.run_erase_peeks`) and see the state of the run at their peek, after every
response handed over before them (`Batch.chain_peek`, `Batch.chain_peek_after`). (c) is already
done, as far as it goes. (b) breaks replay. (d) is (a) plus a cache, or a stale cache.

## The prototype

- `Lanes/Web/Http/Read.lean`: `Http.Read sys`, the actor a request reads and the response made
  from its state.
- `Lanes/Runtime/IO/Shell.lean`: `Runtime.tryPeek`, a peek offered without waiting, its answer
  handed to a function on a task of its own, `none` if the shard stops first.
- `Lanes/Web/IO/Server.lean`: `serve`, `serveWith` and `serveFronted` take
  `reads : Request → Option (Read sys)`, by default none. After `arrive` and `prepare`, a request
  it names takes no id and does not enter: it is a peek at the actor it reads, answered with
  `answer` of the state, `503` when the inbox is full or the shard stops. Operators' requests,
  metrics and the access log see reads as any request.
- `Lanes/Runtime/PeekSound.lean`: the theorems above. `Batch.Act.Sound`'s clause for a peek now
  also says every output the journal so far produced is handed over (`Batch.run_sound`, unchanged
  otherwise).
- `Tests/Reads.lean`: the bank behind its web page with its balance pages as reads. The same
  requests with reads on and off get the same answers, and with reads on the journal holds the
  transfers and the requests that are no read, not the balance pages; twenty transfers each
  followed at once by a read of their source, every read showing the debit; forty concurrent
  reads, each answered once; a shard on a journal file with snapshots that answered reads between
  writes starts again in the state the writes left.
- `bench/ReadsHello.lean` (`benchReads`): a counter, `GET /` through the system, `GET /read`
  from its state, `GET /inc` a write.

## Measured

On this machine: 4 cores shared with other work (load average 4 to 13 during the runs, 2 to 3.6
cores of other CPU over each 5 s window), ext4 on a virtual disk. Server on CPUs 0–1, the load
generator of `bench/go/load` on 2–3, keep-alive, 1 s warm-up, 5 s measured, a fresh server and
journal each run; six runs in two sessions ten minutes apart, the median and the range. Numbers
from a shared machine are no results by `bench/README.md`'s standard: the ratios are the finding.
The journalled rows spread most; the disk was shared too.

| route | conns | requests/s, median (range) | p50 µs, median | journal after a run |
| --- | ---: | ---: | ---: | --- |
| `GET /`, journalled and synced | 1 | 2,119 (552–3,183) | 330 | 1.0–5.1 MB |
| `GET /read`, from the state | 1 | 9,849 (3,783–16,047) | 78 | 82 bytes, its header |
| `GET /`, no journal | 1 | 7,672 (6,085–8,573) | 103 | none |
| `GET /`, journalled and synced | 16 | 6,507 (2,253–8,248) | 1,325 | 4.2–11.2 MB |
| `GET /read`, from the state | 16 | 28,933 (22,082–32,235) | 440 | 82 bytes |
| `GET /`, no journal | 16 | 25,771 (19,748–32,016) | 543 | none |

Views while one connection writes (`GET /inc`, journalled), 15 connections viewing, one server
with reads on, three runs:

| views | views/s | writes/s |
| --- | ---: | ---: |
| `GET /read`, from the state | 18,064–22,188 | 1,112–1,340 |
| `GET /`, journalled | 8,173–11,881 | 559–791 |

A read serves about as many requests a second as a request through the system with no journal,
so entering the system costs little and the sync is what costs: at the median a read serves 4.6
times the journalled rate with one connection and 4.4 times with sixteen, and with writes going
on, twice the views and 1.7 times the writes, since the writes no longer share their batches with
the views. Each journalled request left 230–290 bytes (200 requests from curl one at a time: 293
bytes each); a read leaves none. A read waits for the batch in
progress: with writes going on its median latency is that of a write (610–740 µs here).

## Not done

- Reads of several actors at one point: a peek command over a set of actors, answered with their
  states from one kernel.
- A deadline for a read, a bound on reads in flight, and a drain that waits for them.
- The application-level theorem in general: a `Read` with a proof that it agrees with its spec's
  read under the abstraction, checked by the checker as an invariant, and a typed route for it.
- `examples/videos` with its feed and watch pages as reads.

## For the owner

- Whether a request may be answered outside the system from its state at all. It is the second
  departure from D44's "IO does not answer requests", after D72's `arrive`, though here nothing in
  IO decides: the answer is a pure function of a state the semantics reaches.
- Whether "linearizable at the peek, per actor" is the guarantee, or a route may be a read only
  with an application theorem that it agrees with the spec.
- The peek or a published reference: the peek waits for the batch in progress and costs only when
  read; a reference answers at once and shares every state at every batch.
- Whether reads get a deadline, a bound and a place in the drain, as the gate's requests have.
- The shape of the API: a parameter of `serve`, as here, or a field beside the bridge (`Bridge` is
  over a signature, and a read needs the system's states). And whether `Runtime.state`'s advice,
  "an application sends the actor a message", stands.
- Not about reads, and found measuring them: `Kernel.handle` steps an actor's state while the
  actor table still holds it, so a state that could be updated in place is copied at every step
  (about 1 ms a write for an array of 10⁶ numbers). It is part of the cost of the video site's
  "tables are lists".
