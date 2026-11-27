# Architecture

What Lanes is made of, how a request goes through it, and where each piece is proved. The rules
are in `AGENTS.md`; what works and its limits in `docs/STATUS.md`; what is trusted, and why, in
`TRUSTED.md`; why each piece is the way it is in `docs/decisions/`. The status of every public
definition (proved, with its theorems; trusted; checked; tested; a spec; or none) is generated
from the built library in `docs/INVENTORY.md` (D47), and what has none is on
`docs/inventory-none.md`: that is where a claim is checked, and this page only names the
headline theorems. Those are gated in `Tests/Axioms/`, which stops compiling if a `sorry` or a
new axiom reaches them.

The idea in one line: all logic is pure step functions, the semantics is one executable function
over them, and the code that runs, the checker that explores and the proofs that cover are all
about that function. IO happens only in a few small shells, each of which performs what a pure,
proved function tells it to.

| Piece | Where | Proved by |
| --- | --- | --- |
| Actors and systems | `Lanes/Actors/{Actor,System,World,Step}.lean` | the definition everything else is about |
| Proof tools for systems | `Lanes/Actors/{Lift,Ghost,Monotone,Equiv,Run}.lean` | `System.invariant_of_actor`, `Inductive.of_monotone`, `System.Invariant.of_ghost` |
| The kernel | `Lanes/Actors/{Kernel,KernelSound,KernelTimers}.lean` | `Kernel.exec_reachable`, `Kernel.exec_outputs`, `Kernel.exec_wellFormed` |
| The shell | `Lanes/Actors/{Runtime,Batch,Mailbox,MailboxSound}.lean` | `Batch.run_kernel`, `Batch.run_sound`, `Mailbox.batch_since_take`; the shell itself is trusted |
| Journal, snapshots, disk | `Lanes/Actors/{Journal,Snapshot,Disk}.lean`, `Lanes/Env/Journal.lean` | `Journal.open?_cut`, `Journal.recover_kernel`, `Journal.resume_eq_recover`, `Journal.Disk.Holds.save_crash` |
| Joins | `Lanes/Actors/{Join,JoinSound,MapIOSound}.lean`, `Lanes/Semantics/FairJoin.lean` | `System.Reachable.left`, `SysState.run_left`, `System.Run.Fair.left` |
| Shards and the transport | `Lanes/Actors/{Shard,ShardSound,ShardsSound,Courier,CourierSound}.lean`, `Lanes/Env/{Peers,Node}.lean` | `System.ShardsReachable.unsharded`, `Peers.Courier.written_sublist_sent` |
| The gate and the HTTP server | `Lanes/Http/{Gate,Front,FrontSound,Waiting}.lean`, `Lanes/Semantics/FrontLive.lean`, `Lanes/Env/Http.lean` | `Http.served_answered_le_arrived`, `Http.served_pending_answered`, `Http.Waiting.exec_answered` |
| Other adapters | `Lanes/Actors/Outside.lean`, `Lanes/Env/{Clock,HttpClient}.lean`, `Lanes/Http/{Wire,WireSound}.lean` | `Response.read_wire`, `Request.fields_framing`; conformance tests |
| Web | `Lanes/Http/{Basic,Route,Cookie}.lean`, `Lanes/Html/`, `Lanes/Auth/` | `Route.match?_link`, `Html.escape_safe`, `Auth.verify_sign` |
| The checker | `Lanes/Check/`, `Lanes/Semantics/{Monitor,MonitorSound}.lean` | `Check.search_sound`, `Check.system_sound_of_respects`, `Check.refines_traces` |
| The proof layer | `Lanes/Semantics/` | refinement, specs, fairness, leads-to |
| Data | `Lanes/Data/` | codec laws, `Quorum.majority_inter`, `Bytes.same_iff` |
| Bound C | `native/lanes.c`, `Lanes/Data/Sodium.lean` | trusted; tested against the Lean references |

## Actors and the semantics

An actor (`Lanes/Actors/Actor.lean`) is `init`, `step` and `recover`: a pure, total function from
a state and one message to a new state and a list of effects. A `Signature` names a system's
actors, each with its own message type, and its inputs and outputs; an identity is a typed
reference, and identities may be infinite families, since every identity names an actor that
always exists and starts on its first message (D2). The effects are `send`, `emit` (an output),
`after` and `cancel` (timers named by their message) and `stop` (D3). A `System` adds the actors,
which actors boot, and `accept`, which actor an input goes to (D4).

The semantics is one function, `SysState.step` in `Lanes/Actors/World.lean`: a state holds every
actor's state, the messages in flight, the armed timers and the outputs not yet handed over; an
`Event` is an input, a delivery, a duplicate, a drop, a timeout, an output, a crash or a start.
What may go wrong is an `EnvModel`: each link may lose, reorder and duplicate (`Link.network`
does all three), and actors may crash. Starting runs `recover`, every time (D5). The scheduler,
the checker, the kernel's proofs and `Lanes/Semantics/` all use this one function, so there is
no second model (D6).

Proof tools over it: a per-actor invariant lifts to every system under every fault model
(`System.invariant_of_actor`, with the tactic `actor_invariant`); invariants about states and
messages that hold under every fault take five cases and are built in layers
(`Inductive.of_monotone`, `Monotone.and_net`, D21); history variables are ghosts that cost
nothing at run time (`System.Invariant.of_ghost`, D20); the order of messages on different
links, which no actor can see, is factored out by `SysState.Equiv`.

## The kernel and the shell

The runtime of one shard is a pure kernel inside a thin shell (D18, D23, D40).

The kernel (`Lanes/Actors/Kernel.lean`) is every runtime decision as pure functions over a hash
map of actors, a queue of messages and an agenda of timers: accept an input, deliver the oldest
message (starting its receiver if it is down), fire a due timer, say how long nothing will
happen. Time is data: the shell says what the clock reads. Whatever sequence of operations the
shell asks for, in any order and with any clock readings, the kernel stays in a state the
semantics reaches and the events it reports are a run reaching it (`Kernel.exec_reachable`),
and its outputs are exactly that run's (`Kernel.exec_outputs`). Its agenda holds exactly the
pending timers (`Kernel.exec_wellFormed`), it never sleeps past one, and neither due timers nor
queued messages starve the other (`Kernel.WellFormed.step_of_queued`, `step_of_due`).

The shell (`Lanes/Actors/Runtime.lean`) is one thread per shard. Senders put commands in a
bounded inbox (`Lanes/Actors/Mailbox.lean`, pure: who is refused, who waits, who is woken). The
shell takes everything that has arrived at once and calls `Batch.run` (`Lanes/Actors/Batch.lean`),
a pure function that returns the kernel after the batch and a list of acts: append these journal
entries, hand over these outputs, save this image, answer this peek. The shell performs the acts
in order and decides nothing. Proved: the journal describes the kernel (`Batch.run_kernel`); an
output is handed over only after the entries that produce it are appended, and a save falls
only where every output is handed over (`Batch.run_sound`); a take returns exactly what went in
since the last, in order, and the inbox never holds more than its capacity
(`Mailbox.batch_since_take`, `Mailbox.Reachable.bounded`). Trusted: that the shell performs the
acts as given (`TRUSTED.md`, the first row).

## Journal, snapshots and the disk model

Durability is a journal of what the kernel was asked, not of actor states (D24): replaying it
through the same pure kernel gives the same state, so a restart is not a fault any proof has to
account for. Pure, in `Lanes/Actors/Journal.lean` and `Lanes/Data/Frame.lean`: a file reads back
as the entries written (`Journal.open?_file`); a file cut at any byte opens and gives exactly the
entries wholly written before the cut, and anything else wrong with it is refused, not repaired
(`Journal.open?_cut`); recovery rebuilds exactly the kernel those entries lead to
(`Journal.recover_kernel`), and hands over again exactly what was produced after the last mark
(`Journal.recover_handed`).

A snapshot is the kernel's image (`Lanes/Actors/Snapshot.lean`), saved with codecs the
application gives for its actors; a shard that saves goes on with the restored kernel, so a
snapshot is a restart without the crash (D29). Starting from a snapshot gives what replaying the
whole history gives (`Journal.resume_eq_recover`).

What is written, in what order, and what a start makes of the files are pure functions over a
model of the two files (`Lanes/Actors/Disk.lean`: `Journal.Disk.start`, `Disk.mend`,
`appendWrites`, `saveWrites`), in which an append may stop at any byte and a rename is atomic. If
the process dies anywhere in an append or a save, the files load as the kernel the shard had
(`Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.save_crash`), and a start mends what a
death left (`Journal.Disk.Torn.mend`), so this holds over any number of starts, saves and deaths.
`Lanes/Env/Journal.lean` performs the writes, each synced with `fsync` before the next, so a loss
of power leaves what a death would; that the file system is the model is trusted.

## Composition: joins, shards and the transport

`System.join a b wiring` (`Lanes/Actors/Join.lean`) is two systems as one: an output of one that
the wiring routes to the other becomes a message to the actor its `accept` names. Every tool
applies to a join, because it is an ordinary `System` (D25). What is proved of `a` for every
environment holds of `a` inside any join: of states (`System.Reachable.left`,
`System.Invariant.join_left`), of runs (`SysState.run_left`) and of fair runs
(`System.Run.Fair.left`, `System.LeadsTo.join_left`, D41); for `b`, up to `SysState.Equiv`.
`System.filterMapIO` renames inputs and outputs and hides some; a system behind it does what it
does in the open (`SysState.run_filterMapIO`).

A shard is a system too (D28): `System.shard sys hosts` (`Lanes/Actors/Shard.lean`) is `sys` as a
shard sees it, where a message to an actor hosted elsewhere leaves as a parcel and a parcel that
arrives is an input. It runs on the unchanged kernel and keeps the ordinary journal. Shards
joined behave as the one system, for two (`System.SplitReachable.merged`) and for any number
(`System.shards`, `System.ShardsReachable.unsharded`), under a condition on booting
(`System.SteadyBoot`), so the system's invariants hold of them (`System.Invariant.split`,
`System.Invariant.shards`).

Shards in different processes are joined by TCP, with a link that promises no more than
`Link.network` (D30). There is no router inside a process (D37); a machine's cores are used by
running a process per core. Every decision of the transport is the courier, `Peers.Courier.step`
(`Lanes/Actors/Courier.lean`), a pure function proved for every limit and every sequence of
events (`Lanes/Actors/CourierSound.lean`): one write at a time on a connection, writes only where
it dialed and only what it was sent, in order and at most once
(`Peers.Courier.written_sublist_sent`), a bounded queue, everything closed at `stop`
(`Peers.Courier.stop_closes`), and what it delivers is what its reader makes of the bytes
(`Peers.Courier.delivered_read`). `Lanes/Env/Peers.lean` only performs. That the running
processes implement `System.shards` is trusted.

## The gate and the HTTP server

The HTTP server's logic is a system of its own, the gate (D19, D31, D43). `Gate.step`
(`Lanes/Http/Gate.lean`) decodes each request into an input through the application's `Bridge`,
remembers which requests are waiting, arms a deadline for each, and answers with the system's
response or with `504` when the deadline fires. `Http.gateSystem` is the gate as one actor;
`Http.fronted sys` is the gate joined in front of `sys` (`Lanes/Http/Front.lean`), and
`Http.served sys` is `fronted sys` with requests its only inputs and responses its only outputs,
which is what `Http.serve` runs.

Proved of `served sys` for every system, bridge and configuration: no request is answered more
often than it arrived where the link from outside to the gate does not duplicate
(`Http.served_answered_le_arrived`), a waiting request keeps its deadline armed
(`Http.served_deadlines_armed`), and in a fair run in which the gate does not crash every request
the gate admits is answered (`Http.served_pending_answered`). These come from the gate alone
(`Http.Gate.answered_le_handled`, `Http.Gate.pending_answered`) by projection through the join.
That an arrival reaches the gate is checked, not proved.

The server (`Lanes/Env/Http.lean`) reads a request, prepares it with `Bridge.prepare` on the
request's own task, so a password or a cookie the bridge turns into what the system needs never
reaches the journal (D44), takes an id from `Http.Waiting` (pure: each id handed out once, each
answered at most once and to its own waiter: `Http.Waiting.exec_handed_nodup`,
`Http.Waiting.exec_answered`), and hands the input to the shard. It answers `503` itself when the
inbox is full and `405` for a method an application cannot handle. `Http.serveFronted` serves
`fronted sys`, whose other inputs and outputs pass the gate by, and `Http.serveShard`
(`Lanes/Env/Node.lean`) runs it with the transport: one process with an HTTP front and peers.

Around it, pure and in `Std` only: requests and responses as data, typed routes that print links
and match requests (`Route.match?_link`), HTML values with text escaped by type
(`Html.escape_safe`) and a template macro (`Lanes/Html/Syntax.lean`, trusted), htmx attributes
taken from routes, cookies, and `Lanes/Auth/` (signed tokens, `Auth.verify_sign`; form tokens;
Argon2id password digests; failed attempts; bounded sessions).

## Adapters

Whatever a system does not contain reaches it through outputs and inputs, never through an effect
that does IO (D26). An adapter is a model of the outside, an `Outside`
(`Lanes/Actors/Outside.lean`) that the checker explores the system against, and a handler that
performs; a conformance test records a real run and checks it with `Outside.allows`. Where an
adapter has something to decide, it is a pure function with its theorems (rule 3.9).

- **Clock** (`Lanes/Env/Clock.lean`): the time as an input, never earlier than one given before,
  also across a restart.
- **HTTP client** (`Lanes/Env/HttpClient.lean`): HTTP/1.1 without TLS, one request per
  connection. The bytes are pure (`Lanes/Http/Wire.lean`): the request writer frames the message
  itself (`Request.fields_framing`), and the reader is proved to read a response written as a
  server writes it as soon as its last byte is there, to stay within its limit and to end
  (`Lanes/Http/WireSound.lean`: `Response.read_wire`, `Response.read_more`; D39).
- **HTTP server, journal, transport**: above.

## The checker

`Check.system` (`Lanes/Check/System.lean`) explores every interleaving of a small instance under
an environment model: every order of deliveries and timeouts, every input a driver may send,
every loss, duplicate and crash allowed. It runs the actors' own `step` through `SysState.step`,
so what is checked is the code that runs. The engine (`Lanes/Check/Search.lean`) is breadth-first
over exact states, so traces are shortest (D8, D33). `Service.monitored` and `Check.refines`
(`Lanes/Check/Monitor.lean`) check a system against a `Service` spec with no refinement mapping
(D42). `Check.fuzz` runs seeded random runs for instances too large to explore, and the
deterministic scheduler (`Lanes/Actors/Scheduler.lean`, `Lanes/Actors/FairScheduler.lean`)
replays any run.

What a result means is proved: the checker lists exactly the enabled events
(`SysState.mem_successors_iff`); a complete PASS means each `always` property holds in every
reachable world of the instance (`Check.search_sound`, `Check.system_sound_of_respects`, under
lawful `==`); a reported violation is a real run (`Check.system_violated`); and a complete PASS of
a refinement check means every run's inputs and outputs are a trace of the spec
(`Check.refines_sound`, `Check.refines_traces`). Under D45 a PASS finds bugs; the claim rests on a
theorem.

## The proof layer

`Lanes/Semantics/` imports CSLib and Mathlib; nothing executable imports it (D11, rule 1.6).

- `System.sem` presents `SysState.step` as a CSLib `LTS`, and `System.Refines` is weak
  simulation to a spec (`Lanes/Semantics/System.lean`, `Lanes/Semantics/Refinement.lean`,
  `Lanes/Semantics/Simulation.lean`).
- `Service.spec` turns a sequential `Service` into what a concurrent implementation must refine,
  with deadlines as visible steps, and `System.Implements` is refinement to it: linearizability,
  stated as refinement (`Lanes/Semantics/Service.lean`, D42). A deadline passes in the system
  as a timer it names fires, or as a message it names is delivered
  (`docs/decisions/new-a-deadline-passes-where-it-is-served.md`). `Server.implements` proves the
  `Server` behaviour (`Lanes/Behaviours/Server.lean`) implements its spec.
- A request named by its client takes effect once (`Lanes/Semantics/Once.lean`, D48):
  `Service.once` is the spec, `Lanes/Behaviours/Once.lean` the memo that meets it, and
  `System.Refines.of_handles` the relation rule that a duplicated message cannot break. The
  key-value store implements it with no premise on its links
  (`Examples.KV.implements_once`).
- Liveness (`Lanes/Semantics/Liveness.lean`, D27): infinite runs (`System.Run`), weak fairness
  per obligation (`System.Run.Fair`), `System.LeadsTo` and its rule
  (`System.LeadsTo.ensures_of_invariant`). Every finite run extends to a fair one
  (`System.exists_fair_run_of_run`), and fair runs project through views and joins
  (`System.View.Projects`, `Lanes/Semantics/FairJoin.lean`).

## Bound C

What Lean cannot express or check is bound, as other languages bind it (D46): `fsync`, and from
libsodium SHA-256, HMAC-SHA-256, constant-time comparison, secure random bytes and Argon2id
(`native/lanes.c`, declared in `Lanes/Data/Sodium.lean` and `Lanes/Env/Journal.lean`). A bound
function with a Lean reference (`Sha256.reference`, `Hmac.reference`, `Bytes.sameReference`) has
that reference as its body, so its theorems (`Bytes.same_iff`) are about the reference, and what
is trusted is that the C computes the same, which `Tests/Crypto.lean` tests.

## A request, end to end

One process running `Http.serve` on a journal:

1. `Lanes/Env/Http.lean` reads the request from its socket and applies `Bridge.prepare` on the
   request's own task.
2. `Http.Waiting` hands it an id; the server offers the input to the shard's inbox and answers
   `503` if the inbox refuses it.
3. The shell takes the batch; `Batch.run` journals the input, and the shell appends the entry and
   syncs it.
4. The kernel delivers the input to the gate. `Gate.step` answers `503` if `maxPending`
   requests are waiting, decodes the request through `Bridge.decode` (which may answer it at
   once), arms its deadline, and passes the input on through the join to the actor the system's
   `accept` names.
5. Actors step, one message at a time; messages between them wait in the kernel's queue. One
   emits the response as an output; the wiring hands it back to the gate, which emits it and
   stops waiting. If the deadline fires first, the gate emits `504`.
6. The shell hands the output over only after the entries that produce it are appended
   (`Batch.run_sound`); the server looks up the waiter of its id and writes the response.

After `kill -9`, a start reads the snapshot and the journal (`Journal.Disk.start`), mends a torn
last write, and replays what came after the snapshot's mark through the same kernel; outputs that
were produced and not yet handed over are handed over again (`Journal.recover_handed`). With
peers (`Http.serveShard`), a message to an actor on another shard leaves as a parcel through the
courier and enters the other process's inbox as an input.

## Applications

`Examples/` holds small reference apps, each checked and proved: the bank (`Examples/Bank.lean`,
also served over HTTP by `Examples/BankWeb.lean`), a key-value store with front ends
(`Examples/KV.lean`, refinement in `Examples/KVProofs.lean`), leader election
(`Examples/Election.lean`) and a watchdog (`Examples/Watchdog.lean`). `systems/` holds serious
applications, each its own Lake package that requires Lanes as a user would (`systems/README.md`):
`systems/raft-kv`, a replicated key-value store proved to implement the map it replicates
(`RaftKV.implementsMachine`), and `systems/ledger`, a multi-user web ledger. `lanes new`
(`LanesCli/New.lean`, `templates/app/`) creates an application; `lanes lint`
(`LanesCli/Lint.lean`) checks the rules of `AGENTS.md` that the text can show, the generated files
and the inventory (`LanesCli/Inventory.lean`).
