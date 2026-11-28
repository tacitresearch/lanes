# Architecture

What Lanes is made of, how a request goes through it, and, area by area, what each part does,
what is claimed of it with the evidence, and its limits. The rules are in `AGENTS.md`; what is
trusted, and why, in `TRUSTED.md`; why each piece is the way it is in `docs/decisions/`. A claim
that is not here, or whose evidence does not say what its sentence says, is a defect
(`SECURITY.md` treats a theorem that states less than its docs claim as one). A limit here is
one the design accepts; a limit that can be fixed is an issue labelled `known-limit`.

This page names the headline theorems. `import Lanes` gives the API; the soundness theorems
named here are in `Lanes.Proofs` (`Lanes/Proofs.lean`), which `Lanes.Semantics` imports, and the
services' in `Lanes.Services` (`Lanes/Services.lean`). Those are gated in `Tests/Axioms/`, which
stops compiling if a `sorry` or a new axiom reaches them.

The status of a claim is one of:

- **proved**: a theorem, checked by Lean, with an axiom gate (`Tests/Axioms/`, or the example's
  `Proofs/Axioms.lean`) that stops compiling if a `sorry` or a new axiom reaches it;
- **checked**: a model check on a small instance, or a check of `lanes lint`;
- **tested**: a test run by `lake test`, a CI job or by hand, as the row says;
- **trusted**: listed in `TRUSTED.md`, with how it is checked;
- **not proved**: stated here so that nobody reads it into another row.

The idea in one line: all logic is pure step functions, the semantics is one executable function
over them, and the code that runs, the checker that explores and the proofs that cover are all
about that function. IO happens only in a few small shells, each of which performs what a pure,
proved function tells it to.

## The model, and how a request goes through it

An application is a process that keeps nothing it cannot lose
(`docs/decisions/D110-volatile-actors.md`). Its actors are volatile: a restart puts every one
back at its initial state, as in Go, Tokio or Erlang. What must outlive the process lives in
services outside, each with a model in Lanes: PostgreSQL first, through the typed store
(`docs/decisions/D111-typed-store.md`); S3 for objects; email and payments.

A request to a web application goes like this, in what `lanes new` writes (`examples/counter`)
and in `examples/rookery`:

1. The server reads it (`Http.Conn`), does what it needs in IO on the request's own task
   (`arrive`: the time it arrived, a password checked against its stored hash), and the bridge
   takes out what must not enter the system and parses the rest into an input (`Bridge.prepare`,
   `Bridge.decode`). The gate admits it, or answers `503` (`Http.served`).
2. The front, an actor that keeps nothing, sends it to the store as a call: the request as data,
   under the request's id.
3. The store runs the application's handler for it, a pure function from the request to one
   transaction (`Handler`, `Txn`), on PostgreSQL at `SERIALIZABLE`, trying it again on a conflict
   (`Postgres.Typed.Store.call`). The transaction is all the request does, so trying it again
   repeats nothing.
4. The answer comes back to the front as an input, out as an output, and the bridge renders it.

Effects and work for later are rows written by that transaction: an email, a charge, a reminder
is a job of an outbox, performed by a worker under the row's id as the idempotency key
(`docs/decisions/D114-outbox-jobs.md`); a key a client sends to act once is a row
(`Keys.once`). So an effect is performed only for a transaction that committed.

What is claimed of the application's data is proved per transaction: an invariant every
transaction keeps holds in every database the store's model allows (`Db.invariant`), and rows a
transaction does not write stay as they were (`Txn.All.others`). That PostgreSQL behaves like the
model is a premise, checked against runs recorded from PostgreSQL (`oracles/postgres/`).

**Several instances.** An actor's state is a cache of its process; whatever several instances
must agree on lives in the database. So an instance can be replaced, scaled or restarted at any
moment, and the normal deploy is several behind a load balancer, each running the migrations not
yet run at its start and refusing to start on tables other than the declared ones
(`Postgres.Typed.prepare`). `docs/DEPLOY.md` says how.

Actors with state of their own are still the tool for what lives in one process: a cache, a
protocol in progress, a coordination; `examples/bank` and `examples/kv-cache` show them, and the
semantics, the checker and the proofs below are about every system of actors.

| Piece | Where | Proved by |
| --- | --- | --- |
| Actors and systems | `Lanes/Core/{Actor,System,World,Step,Run}.lean` | the definition everything else is about |
| Proof tools for systems | `Lanes/Proof/{Lift,Ghost,Monotone,Equiv,Deed}.lean` | `System.invariant_of_actor`, `Inductive.of_monotone`, `System.Invariant.of_ghost` |
| The kernel | `Lanes/Runtime/{Kernel,KernelSound,KernelTimers}.lean` | `Kernel.exec_reachable`, `Kernel.exec_outputs`, `Kernel.exec_wellFormed` |
| The runtime | `Lanes/Runtime/IO/Shell.lean`, `Lanes/Runtime/{Sched,SchedSound,Peek}.lean` | `Sched.Run.reachable`, `Sched.Step.sound`, `Sched.Step.inv`, `Sched.Slot.take_push`, `Sched.Slot.put_push`; the threads are trusted |
| Joins | `Lanes/Core/Join.lean`, `Lanes/Proof/{JoinSound,MapIOSound}.lean`, `Lanes/Semantics/FairJoin.lean` | `System.Reachable.left`, `SysState.run_left`, `System.Run.Fair.left`, `System.Run.Fair.right` |
| The gate and the HTTP server | `Lanes/Web/Http/{Gate,Front,FrontSound,Admit,AdmitSound,View,Waiting,Conn,ConnSound,Stream,Sse,SseSound,Loopback}.lean`, `Lanes/Semantics/Front.lean`, `Lanes/Web/IO/Server.lean` | `Http.served_answered_le_arrived`, `Http.served_pending_answered`, `Http.Front.World.refines`, `Http.Front.pending_answered`, `Http.Waiting.exec_answered`, `Http.Conn.run_writes`, `Http.Conn.read_streamed`, `Http.Sse.parse_written` |
| Metrics, health and the access log | `Lanes/Lib/Metrics.lean`, `Lanes/Web/Http/{Ops,OpsSound}.lean`, `Lanes/Web/IO/Ops.lean` | `Metrics.Histogram.observeAll_eq`, `Metrics.readLabelValue_escapeLabel`, `Http.Ops.route?_default`, `Http.Ops.route?_metrics`, `Http.Ops.answer_ready`, `Http.Ops.Access.parse_line`; that none of it reaches a system is trusted and tested |
| Other adapters | `Lanes/Outside/Basic.lean`, `Lanes/Outside/{Clock,IO/Clock}.lean`, `Lanes/Web/IO/Client.lean`, `Lanes/Web/Http/{Grammar,Wire,WireSound}.lean` | `Response.read_wire`, `Request.fields_framing`; conformance tests |
| The platform: the file system | `Lanes/Outside/FileSystem/{Basic,Replace,Log}.lean`, `Lanes/Outside/FileSystem.lean`, `Lanes/Outside/IO/FileSystem.lean`, `Lanes/Lib/File.lean` | `Replace.crash`, `Replace.failed`, `Replace.done`, `Log.crash`, `Log.failed`, `Fs.crash_mem_crashes`; the crash rules and the binding are trusted |
| Models of external services | `Lanes/Outside/{Rpc,Idempotent,Events,ObjectStore,Queue,Cache,Clock,Throttle}.lean`, `Lanes/Services/S3/MultipartModel.lean`, `Lanes/Services/Stripe/Payments.lean`, `Lanes/Outside/Effects/`, `Lanes/Web/Http/SharedCache.lean`, `Lanes/Proof/Outputs.lean` | `Idempotent.at_most_once`, `Rpc.answered_le_called`, `Events.deliveries_le`, `ObjectStore.read_sent`, `ObjectStore.held_sent`, `Multipart.read_listed`, `Queue.received_le`, `Cache.read_sent`, `Clock.wall_back_le`, `Throttle.wait_le`, `SharedCache.serve_storable`, `SharedCache.serve_of_leaks`, `System.Emits.outputs`; that a real service conforms is trusted |
| Signature Version 4 and the S3 client | `Lanes/Web/Http/{SigV4,SigV4Sound}.lean`, `Lanes/Services/S3/{Basic,Xml,Post,PostSound,Multipart}.lean`, `Lanes/Services/S3/IO/Client.lean` | `SigV4.target_sign`, `SigV4.sortQuery_sorted`, `SigV4.canonicalHeaders_sorted`, `SigV4.encode_chunks`, `S3.Post.form_policy`, `S3.Post.admitted_bounded`, `S3.Multipart.Plan.count_le`, `S3.Multipart.Plan.range_full`; signatures tested against AWS's vectors and botocore, the client against a fake S3, the multipart flow model-checked; its IO trusted |
| AWS | `Lanes/Services/Aws/{Refresh,Imds,Ses,SesSound,Sqs,CloudFront,CloudFrontSound}.lean`, `Lanes/Services/Aws/IO/{Credentials,Ses}.lean` | `Aws.Refresh.current_fresh`, `Aws.Refresh.refresh_in_time`, `Aws.Ses.toAddresses_json`, `Aws.CloudFront.cannedPolicy_eq`; the IO is trusted |
| PostgreSQL and the store model | `Lanes/Services/Postgres/{Bytes,Message,MessageSound,Scram,Conn,ConnSound,ConnInfo,Pool,Settings,Table}.lean`, `Lanes/Services/Postgres/IO/{Client,Pool}.lean`, `Lanes/Lib/Crypto/Certificate.lean`, `Lanes/Outside/Store/{Basic,Sound}.lean` | `Backend.read_encode`, `Frontend.decode_encode`, `Conn.run_fifo`, `Conn.step_committed`, `Conn.step_query`, `Conn.tls_first`, `Conn.run_bound`, `Conn.onMessage_binds`, `Pool.run_size`, `Pool.never_again`, `SslMode.defaultFor_disable`, `Store.write_skew`, `Store.lost_commit_either`; the IO is trusted, and that the server behaves like the model is a premise |
| The typed store | `Lanes/Db/{Basic,Columns,Query,Txn,Retry,Model,Sound}.lean`, `Lanes/Services/Postgres/Sql.lean`, `Lanes/Services/Postgres/IO/Db.lean` | `Db.invariant`, `Retry.loop_committed`, `Txn.interp_apply`, `Postgres.Sql.decode_param`; the driver is trusted, and that PostgreSQL at `SERIALIZABLE` behaves like the model is a premise |
| Jobs, the outbox and acting once | `Lanes/Db/{Jobs,JobsSound,Worker,WorkerSound,Once,OnceSound}.lean`, `Lanes/Services/Postgres/IO/Worker.lean`, `Lanes/Web/IO/Jobs.lean` | `Worker.committed_only`, `Worker.once_each`, `Queue.claim_takes`, `Queue.claim_attempts`, `Queue.one_per_key`, `Queue.finish_stale`, `Keys.once_again`; the worker's IO is trusted |
| Web | `Lanes/Web/Http/{Basic,Route,RouteSound,Cookie,CookieSound}.lean`, `Lanes/Web/Html/`, `Lanes/Web/Auth/` | `Html.lex_render`, `Html.safeUrl_scheme`, `Http.dispatch_link`, `Http.parseForm_encodeForm`, `Http.readSetCookie_header`, `Auth.verify_eq_some`, `Auth.checkForm_other` |
| The checker | `Lanes/Check/`, `Lanes/Semantics/{Monitor,MonitorSound}.lean` | `Check.search_sound`, `Check.system_sound_of_respects`, `Check.refines_traces` |
| The proof layer | `Lanes/Semantics/` | refinement, specs, fairness, leads-to |
| Data and the standard library | `Lanes/Data/`, `Lanes/Lib/` | `Json.Fields.readObject_object`, `Json.Codec.ofAlts`, `Bytes.same_iff`, `Json.parse_iff`, `Url.parse_print` |
| Structured logs | `Lanes/Lib/{Log,LogSound}.lean`, `Lanes/Runtime/IO/Log.lean` | `Log.render_oneLine`, `Log.parse_render`; writing a line is trusted |
| Forms and uploads | `Lanes/Lib/Mime/{Multipart,MultipartSound}.lean`, `Lanes/Web/Http/Basic.lean` | `Multipart.parse_write`, `Multipart.parse_tooLarge`, `Multipart.length_le_of_parse`, `Multipart.headers_le_of_parse`, `Multipart.filename?_file`; compared with Go's `mime/multipart` |
| Compression | `Lanes/Lib/Compress/{Checksum,Inflate,Deflate,Gzip}.lean`, `Lanes/Web/Http/Compress.lean` | `Inflate.size_le`, `Gzip.size_le`, `Zlib.size_le`; compared with Go's `compress/flate`, `gzip` and `zlib` |
| Sign-in with OAuth 2.0 and OpenID Connect | `Lanes/Web/Auth/{Jose,IdToken,OAuth}.lean`, `Lanes/Web/IO/SignIn.lean`, the presets `Lanes/Services/Oidc/` | `OAuth.check_ok`, `OAuth.Used.accepted_once`, `OAuth.Used.length_claim`, `OAuth.IdToken.verify_accepted`, `Jose.verify_ok`, `OAuth.Keys.no_fetch_within`; the edge is trusted, tested end to end against a provider run in the test |
| Bound C | `native/lanes.c`, `Lanes/Lib/Crypto/Native.lean`, `Lanes/Outside/IO/FileSystem.lean`; `native/verify.c`, `Lanes/Lib/Crypto/Verify.lean`; `native/sign.c`, `Lanes/Lib/Crypto/Sign.lean` | trusted; tested against the Lean references and published vectors |
| TLS client | `native/tls.c`, `Lanes/Web/IO/Tls.lean` | trusted; tested against `openssl s_server` |

## Actors and the semantics

An actor (`Actor`, `Lanes/Core/Actor.lean`) is `init`, `step` and `recover`: a pure, total function from
a state and one message to a new state and a list of effects. A step is also told its context
(`Ctx`, D101 and `docs/decisions/D121-step-context.md`): the moment (`now_ms`, `seed`) and who sent
the message (`Sender`: the outside, an actor, or one of its own timers); a recovery is told the
moment. An actor that reads it gives `stepAt` and `recoverAt`; one that does not gives `step` and
`recover`, which they default to. A `Signature` names a system's
actors, each with its own message type, and its inputs and outputs; an identity is a typed
reference, and identities may be infinite families, since every identity names an actor that
always exists and starts on its first message (D2). The effects (`Effect`) are `send`, `emit` (an output),
`after` and `cancel` (timers named by their message) and `stop` (D3). A `System` adds the actors,
which actors boot, and `accept`, which actor an input goes to (D4).

The semantics is one function, `SysState.step` in `Lanes/Core/World.lean`: a state holds every
actor's state, the messages in flight, the armed timers and the outputs not yet handed over; an
`Event` is an input, a delivery, a duplicate, a drop, a timeout, an output, a crash, a start, a
restart or a tick, which sets the clock that steps are told (`SysState.clock`). Ticks may move
the clock either way, since concurrent workers read it in no global order; the checker ticks only
forward, along the moments a scenario lists (`Scenario.moments`, none by default). What may go wrong is an `EnvModel`: each link may lose, reorder and duplicate
(`Link.network` does all three), actors may crash, and the process may restart
(`EnvModel.mayRestart`). A restart puts the whole system back at `SysState.init`, as after a
process restart (D110): every actor at its initial state, and the messages in flight, the timers
and the outputs not yet handed over lost; the outside keeps what it sent and saw, so an answer
it waits for may never come. Restarts are a fault the environment model permits, off unless a
model says so: `EnvModel.Faultless` rules them out, and `EnvModel.Restarts` is one process that
may restart and does nothing else wrong. Starting runs `recover`, every time (D5). The scheduler,
the checker, the kernel's proofs and `Lanes/Semantics/` all use this one function, so there is
no second model (D6).

Proof tools over it: a per-actor invariant lifts to every system under every fault model,
restarts included (`System.invariant_of_actor`, `System.invariant_of_inductive`, with the tactic
`actor_invariant`); a system reaches the same states with restarts as without, so every
invariant proved without them holds with them (`System.Invariant.of_withoutRestarts`,
`System.Invariant.restarts`); invariants about states and
messages that hold under every fault take five cases and are built in layers
(`Inductive.of_monotone`, `Monotone.and_net`, D21); history variables are ghosts that cost
nothing at run time (`System.Invariant.of_ghost`, D20); the order of messages on different
links, which no actor can see, is factored out by `SysState.Equiv`.

Where: `Lanes/Core/{Actor,System,Join}.lean`, `Lanes/Core/{World,Step,Run}.lean`, `Lanes/Proof/`,
`Lanes/Core/{Scheduler,FairScheduler}.lean`, `Lanes/Check/Fuzz.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| The step function that runs is the one the checker explores and the proofs are about | One semantics, `SysState.step` (`Lanes/Core/World.lean`); `Check.system` runs actors through it (`Lanes/Check/System.lean`); the kernel is proved against it (`Kernel.exec_reachable`) | The shell is trusted to run the kernel as written | proved for the kernel; the rest by construction |
| A per-actor invariant holds in every reachable state of every system, under every fault model, restarts included | `System.invariant_of_actor`, `System.invariant_of_inductive`, `Lanes/Proof/Lift.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |
| A system reaches the same states with process restarts as without, so an invariant proved without restarts holds with them | `System.reachable_withoutRestarts`, `System.Invariant.of_withoutRestarts`, `System.Invariant.restarts`, `Lanes/Core/Step.lean`; gate `Tests/Axioms/Core.lean` | None | proved |
| History variables (ghosts) erase: an invariant proved with them holds without them | `System.Invariant.of_ghost`, `Lanes/Proof/Ghost.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |
| Invariants about states and messages take five cases, not eight, and hold under loss, duplication, reordering and crashes | `System.Inductive.of_monotone`, `System.Monotone.and_net`, `Lanes/Proof/Monotone.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |

Also:

- The layers of a proof rule for invariants are added with `Monotone.and_net`, `and_state` and
  `Monotone.of_iff`; per-event lemmas give each event's enabling condition and next state.
- A kind of message that only the outside sends is handled no more often than it is put in,
  where the links from outside do not duplicate (`System.handled_le_put`): proved.
- A system behind hidden inputs and outputs (`System.filterMapIO`, or `System.mapIO`, which
  hides none) does what it does in the open, event for event (`SysState.run_filterMapIO`,
  `System.Invariant.filterMapIO`): proved.
- What relates two moments does not survive a restart in general: a refinement of a spec whose
  value lives in actors, acting once on a memo, a count of what was answered against what is
  owed, liveness. Each theorem says which it is: one that holds under restarts is stated for every
  environment or under `EnvModel.Restarts` (`Bank.money_conserved_restarts`, the gate's
  `answered_le_handled`, `System.handled_le_put`, `Worker.committed_only`,
  `Shop.charged_at_most_once`), and one that does not takes `env.mayRestart = false` or
  `EnvModel.Faultless` (`Server.implements`, `Once.server_implements`, `KV.implements_once`,
  every leads-to).
- The deterministic scheduler gives seeded runs, replayable event lists and drivers for the
  outside world; `FairScheduler` takes the event the system has owed longest, counting a timer
  that is armed again as owed from then, and its run is a fair run of the proof layer.

## The kernel and the runtime

A system runs in one process, its actors free on worker threads as in Go, Tokio or Erlang
(`docs/decisions/D116-free-running.md`). Its state lives as long as the process: every start is a
boot, with every actor in its initial state. State that must outlive the process lives in a
service outside, reached through a modelled adapter (`Lanes/Outside/`, `Lanes/Db/`).

The runtime (`Lanes/Runtime/IO/Shell.lean`) keeps each actor in a slot of its own
(`Lanes/Runtime/Sched.lean`): its state, its mailbox, and whether it is idle, on a run queue or
running. Each worker has a run queue of actors with mail. It takes the first, or steals one from
another worker's queue when its own is empty, steps it on up to `Runtime.Config.budget` items of
its mailbox, and lets it go, back on its queue if mail is waiting. An actor runs on one worker at
a time, and handles its messages in the order they reached it. A step takes the next item and
the state out of the slot (`Slot.take`), runs the step function outside any lock, and writes the
result back (`Slot.put`); the messages it sent are pushed to their receivers' mailboxes
(`Slot.push`) before the actor is let go of (`Slot.release`), so a link's messages arrive in
order. Timers are on an agenda kept by a thread of its own, which pushes each to its actor when
it is due; one cancelled or armed again is dropped when its actor takes it. Inputs go straight
to their actor's mailbox; at most `inboxCapacity` wait for their actor (`Sched.Ledger`), and
`tryInput` refuses beyond (rule 3.8). The messages between actors are bounded together
(`docs/decisions/D123-runtime-limits.md`): while `Runtime.Config.mailHighWater` of them wait, no
input is taken, and a step that leaves more than `mailCapacity` waiting is handed to `onOverflow`,
which by default reports it and ends the process with status 75, the semantics' restart. A step's
sends, outputs and timers are gathered newest first and turned round once, so a step costs time
linear in its effects (`Sched.Slot.put_eq`, `Kernel.performAll_eq`).

Each step is told the moment: the wall clock read at the start plus the monotonic time since, and
a seed from its worker's generator, seeded from the operating system. With `record` on, the trace
has a tick with that moment before each step, so it replays through `SysState.run`. A watchdog
thread hands a step that has run longer than `Runtime.Config.stepLimitMs` (30 s) to `onStuck`,
which by default reports it and ends the process with status 75 for its supervisor to start
again: the semantics' restart, which drops the poisoned message with the rest of memory
(`docs/decisions/D121-step-context.md`).

What the runtime decides is those pure functions; the threads only move data. The scheduler's
model (`Lanes/Runtime/SchedSound.lean`) is its whole state as one value: every slot, each
worker's run queue and the actor it holds, the messages a step sent and has not pushed yet, and
two ghosts, the messages in flight in the order the semantics sent them and the outputs not yet
handed over. Each of its transitions, the threads' operations, is no event of `SysState.step`,
one, or for a step a tick with the moment it is told and the step (`Sched.Step.sound`), under any environment whose links are reliable, so every
run of the model from its start is a run of the semantics, with its outputs
(`Sched.Run.reachable`). It keeps an invariant (`Sched.Step.inv`): the mailboxes and the
messages not yet pushed hold the messages in flight link by link in order, so a message at the
head of a mailbox is the oldest on its link and may be delivered; an actor runs on at most one
worker, and is running exactly when one holds it; an idle actor has no mail and a queued one is
on a run queue, so no mail waits for a worker that will never come (`Sched.Model.Placed`). Pushes
by other threads to a slot a worker holds commute with its `take` and `put`
(`Sched.Slot.take_push`, `Sched.Slot.put_push`), which is why the step function can run outside
the lock. Trusted: that the threads perform the model's transitions (`TRUSTED.md`, the first
row, says how each is atomic).

A peek (`Runtime.tryPeek`, D108) reads each actor it names between two of its steps: an actor no
worker holds at once, a held one when its worker lets go of it. It sees every message that actor
took before and none after. The states of different actors are not read at one moment: a read of
several actors beside work in flight is not a consistent cut, and one read after a response sees
the actor that gave it as it was then, not the actors it has sent messages to since.

The kernel (`Lanes/Runtime/Kernel.lean`) is the runtime's decisions on one thread, as pure
functions over a hash map of actors, a queue of messages and an agenda of timers. `Http.Loopback`
and the tests run it. Whatever sequence of operations is asked of it, the kernel stays in a
state the semantics reaches and the events it reports are a run reaching it
(`Kernel.exec_reachable`), and its outputs are exactly that run's (`Kernel.exec_outputs`). Its
agenda holds exactly the pending timers (`Kernel.exec_wellFormed`), and neither due timers nor
queued messages starve the other (`Kernel.WellFormed.step_of_queued`, `step_of_due`). Before a
step it takes the actor's state out of its cell (`Kernel.takeState`), so the step updates the
state in place (`docs/decisions/D84-the-kernel-takes-the-state-out-before-the-step.md`).

Where: `Lanes/Runtime/`, `Lanes/Proof/Lossy.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Every run of the free-running scheduler is a run of the semantics, interleaving per-actor steps, and its outputs are that run's | `Sched.Run.reachable`, `Sched.Step.sound`, `Sched.Step.inv`, `Lanes/Runtime/SchedSound.lean`; gate `Tests/Axioms/Runtime.lean` | The runtime's threads perform the model's transitions (TRUSTED, the first row); links reliable | proved; the threads trusted |
| An actor runs on at most one worker; no mail waits for a worker that will never come | `Sched.Model.Placed`, kept by `Sched.Step.inv` | as above | proved of the model |
| Recorded runs replay through the semantics, on one worker and on several, with actors that stop and timers | `Tests/Runtime.lean` | | tested |
| The kernel stays in a state the semantics reaches, and its events are a run reaching it, for any sequence of operations, inputs and clock readings | `Kernel.exec_reachable`, `Kernel.exec_outputs`, `Lanes/Runtime/KernelSound.lean`; gate `Tests/Axioms/Runtime.lean` | | proved |
| A message costs the same at 1,000 and 100,000 actors | The scale benchmark in `lake exe lanesCheck` (`Tests/Scale.lean`) | A four-core machine | tested |
| A step's write-back is the fold the soundness proofs are about, and costs time linear in the step's effects | `Sched.Slot.put_eq`, `Kernel.performAll_eq`; the time at 10^3, 10^4 and 10^5 outputs and sends in `lake exe lanesCheck` (`Tests/Scale.lean`) | | proved; the time tested |
| An input is taken only while the inbox has room and the mail between actors is below its high-water mark, and one refused leaves no trace | `Sched.Ledger.offer_taken`, `offer_refused`, `offer_of_mail`, `done_wakes`, `Lanes/Runtime/SchedSound.lean`; `Tests/Runtime.lean` under a fan-out | The shell asks the ledger as written (TRUSTED, the first row) | proved of the ledger; tested |

Also:

- An actor let go of at rest (up, no timers, no mail, in a state a start gives it) leaves the
  table, as the kernel releases it (`Kernel.exec_visible`); a hundred thousand identities touched
  leave none behind (`Tests/Release.lean`).
- On mixed step costs, free-running gave several times lower p50 and more answers a second than
  one worker (`bench/Mixed.lean`, `docs/decisions/D116-free-running.md`, which has the numbers).

### Limits

- Actor state, timers included, is lost with the process: a restart is a boot.
- A state crosses threads between two turns of its actor, and Lean never updates in place an
  object another thread may see: the first step of a turn copies the state it updates, and the
  write-back walks it. The steps of one turn update it in place. A write to a state of a million
  numbers costs about two copies when each message is a turn of its own (`Tests/Scale.lean`).
- A peek of several actors is not a consistent cut (above).
- The mail between actors is bounded as a whole: an actor far behind holds up every input, not
  only those to it. Past `mailCapacity` the process restarts, losing every actor's state; an
  application whose proofs assume no restarts has no guarantee there
  (`docs/decisions/D123-runtime-limits.md`).
- Arming a timer looks through the actor's pending timers, so a step that arms `n` different
  timers takes time quadratic in `n`: messages have only `DecidableEq`.
- Every turn updates one shared ledger (inputs waiting, items in mailboxes) and every push may
  look up a shared table of slots; on many cores these are points of contention.
- That a queued actor is eventually stepped and a due timer pushed rests on the workers and the
  agenda's thread running (`TRUSTED.md`, "Progress"). No bound is proved.
- A step that never ends restarts the process (the watchdog, above), losing every actor's state;
  a client that sends the poisoned request again kills it again. A step that overflows the stack
  or runs out of memory aborts the process, unreported by the runtime. A panic returns `default`
  and the step goes on.
- The boot's recoveries are told the moment `{}`: no tick comes before `SysState.init`.

## Composition: joins

`System.join a b wiring` (`Lanes/Core/Join.lean`) is two systems as one: an output of one that
the wiring routes to the other becomes a message to the actor its `accept` names. Every tool
applies to a join, because it is an ordinary `System` (D25). What is proved of `a` for every
environment holds of `a` inside any join: of states (`System.Reachable.left`,
`System.Invariant.join_left`), of runs (`SysState.run_left`) and of fair runs
(`System.Run.Fair.left`, `System.LeadsTo.join_left`, D41). For `b`, which boots second, it
holds of states up to `SysState.Equiv` and of fair runs exactly (`System.Run.Fair.right`,
`System.LeadsTo.join_right`). What one side sends the other through the wiring is handled
there in every fair run, on a link that loses nothing, by an actor that is not crashed and
never stops (`System.Run.Fair.routed_right`, `System.Run.Fair.routed_left`).
`System.filterMapIO` renames inputs and outputs and hides some; a system behind it does what it
does in the open (`SysState.run_filterMapIO`).

Where: `Lanes/Core/Join.lean`, `Lanes/Proof/{JoinSound,MapIOSound}.lean`,
`Lanes/Semantics/FairJoin.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| What is proved of either side of a join holds of it in the join: of its states, its runs and its fair runs, so leads-to carries over | Left: `System.Reachable.left`, `SysState.run_left`, `System.Run.Fair.left`, `System.LeadsTo.join_left`; right: `System.Reachable.right`, `System.Run.Fair.right`, `System.LeadsTo.join_right`; `Lanes/Proof/JoinSound.lean`, `Lanes/Semantics/FairJoin.lean`; gates `Tests/Axioms/Proof.lean`, `Tests/Axioms/Semantics.lean` | The side alone gets its inputs on `Link.network` (`EnvModel.left`, `EnvModel.right`). States of the right side only up to `SysState.Equiv`, since it boots second. Fair runs are seen without the messages from outside in flight, and leads-to only of the side's actors' states | proved |
| What one side of a join sends the other through the wiring is handled by the other side | `System.Run.Fair.routed_right`, `System.Run.Fair.routed_left`, from `System.Run.Fair.handled_right`, `handled_left` and `System.Run.Fair.handled`; `Lanes/Semantics/FairJoin.lean`, `Lanes/Semantics/Liveness.lean`; gate `Tests/Axioms/Semantics.lean` | A fair run; the link from the sender to the receiving actor loses nothing; the environment does not crash the receiving actor, and it never stops, in a step or a start. Each is needed: a loss, a crash or a stop can take the message out of flight. Only outputs emitted as the sender handles a message, not as it starts | proved |

### Limits

- `System.join` leaves the inputs it wires open to the outside until `mapIO` or `filterMapIO` hides them, and keeps the outputs it wires in its signature though none is put out; `Http.fronted` hides both. A fair run of a join is a fair run of each side (`System.Run.Fair.left`, `System.Run.Fair.right`).
- A system runs in one process. Clustering across processes is not on main (it is kept on the branch `claude/archive-journal-runtime`).

## The gate and the HTTP server

The HTTP server's logic is a system of its own, the gate (D19, D31, D43). `Gate.step`
(`Lanes/Web/Http/Gate.lean`) decodes each request into an input through the application's `Bridge`,
remembers which requests are waiting, arms a deadline for each, and answers with the system's
response or with `504` when the deadline fires. `Http.gateSystem` is the gate as one actor;
`Http.fronted sys` is the gate joined in front of `sys` (`Lanes/Web/Http/Front.lean`), and
`Http.served sys` is `fronted sys` with requests its only inputs and responses its only outputs:
the specification of what `Http.serve` does.

`Http.serve` does not run the gate as an actor, which would make it a serial point for every
request (`docs/decisions/D96-runtime-contract.md`). It makes the gate's decisions before the
runtime, under the lock of its table of waiting requests, and hands the runtime only what the gate
admitted; the runtime runs `Http.admitted sys` (`Lanes/Web/Http/Admit.lean`), which is `sys` with
no actor every request goes through. `Http.Front.World` models the server so: the front's state
beside the runtime's. Every run of it is a run of `served sys`, with the same requests arriving and
the same answers handed over in the same order (`Http.Front.World.refines`,
`Lanes/Web/Http/AdmitSound.lean`), so every theorem below holds of the server
(`Http.Front.World.answered_le_arrived`). Of the front alone: it answers no request more often
than it arrived (`Http.Front.run_answered_le`), its waiting list stays within `maxPending`
(`Http.Front.run_bounded`), and every waiting request is answered if every deadline that stays
armed is passed to it (`Http.Front.pending_answered`).

A request that changes nothing can be answered from the state (`Lanes/Web/Http/View.lean`, the
decision "Reads from the state"). The application gives `serve` a `view` beside its bridge: for a
request it names, the actors it reads, a predicate for the actors of which it reads every one
started (`View.every`), and its response from their
states. Such a read never
enters the system. It waits behind a gate of its own, `Gate.step` over `readSig`
(`ServerConfig.reads`: its own deadline and bound), for a peek of those actors
(`Runtime.tryPeek`), and is answered from their states off the workers' threads, or `504` at its
deadline. It reads each actor it names between two of that actor's steps, and changes nothing
the actors do; the states of several actors are not read at one moment (the runtime, above).
That a view answers
what the request would if it entered is the application's claim. `Http.Front.World` does not model reads: that
the server does what the gate of reads decides is trusted, as for the gate.

Proved of `served sys` for every system, bridge and configuration: no request is answered more
often than it arrived where the link from outside to the gate does not duplicate
(`Http.served_answered_le_arrived`), a waiting request keeps its deadline armed
(`Http.served_deadlines_armed`), and in a fair run in which the gate does not crash every request
the gate admits is answered (`Http.served_pending_answered`). These come from the gate alone
(`Http.Gate.answered_le_handled`, `Http.Gate.pending_answered`) by projection through the join.
Every request that arrives is answered, in a fair run in which the gate does not crash and the
link from outside to the gate loses nothing (`Http.served_arrival_answered`): a message in
flight on such a link to an actor that stays up is handed to it (`System.Run.Fair.delivered`),
and the gate answers an arrival at once or admits it. With distinct ids and a link from outside
that does not duplicate, each request is answered exactly once.

The server (`Lanes/Web/IO/Server.lean`) reads a request, prepares it with `Bridge.prepare` on the
request's own task, so a password or a cookie the bridge turns into what the system needs never
reaches the system (D44), takes an id from `Http.Waiting` (pure: each id handed out once, each
answered at most once and to its own waiter: `Http.Waiting.exec_handed_nodup`,
`Http.Waiting.exec_answered`), puts it before the gate and hands what the gate admits to the
runtime. The gate decides under the same lock that hands out the id (`Gate.admit`), so a `503`
from a full inbox leaves the gate's state as it was; it reads the runtime's outputs
(`Gate.receive`), and the server's ticker hands it each deadline that passes, which it answers
`504` (`docs/decisions/D106-gate-before-shard.md`). It answers
`503` itself when the inbox is full and `501` for a method it does not know (#171). With `ServerConfig.ioThreads`
above zero (four by default), the connections run on that many threads of the server's own, each on one for its
whole life; Lean has one libuv loop a process, which every read and write still goes through. `Http.serveFronted` serves
`admittedFronted sys`, whose other inputs and outputs pass the gate by.

A request may stream (`ServerConfig.streams`, the decision "Bodies and responses stream through
the gate"): its head is handed on alone, its body follows in pieces of at most `piece_max` bytes,
and the answer may open a response whose parts the connection pulls; each piece and each pull is
a request of its own through the gate (`Lanes/Web/Http/Stream.lean`), one at a time, so the gate
and its theorems are unchanged and back-pressure reaches the client's TCP window. Proved of
`Conn.step` for every configuration, beside its theorems before: the bytes of a streamed response
are `Response.wireChunked`, read back as the head with the parts as its body
(`Http.Conn.read_streamed`); each part is written as its chunk after what came before
(`Http.Conn.pulled_part`, `Http.Conn.flushStream_ended`); a pull is made only when nothing written
is unsent (`Http.Conn.flushStream_going`); a piece is what `Inflow.gather` reads at the
connection's position (`Http.Conn.pump_piece`). That the pieces of a whole run make up the strict
reader's body and the bytes of a whole stream are the parts given is model-checked
(`Tests/HttpStream.lean`), not proved. Server-Sent Events are parts of a stream of events: the
client's reader, a model of the WHATWG one, reads back the events written, in order, each once,
comments between them ignored (`Http.Sse.parse_written`), and an event made from an answer is one
it reads back as it is (`Http.Sse.Event.ofResponse_valid`). `Http.Loopback` runs a front end with
no socket, for tests: the connection, the gate as the server runs it, and `admitted sys` on a
kernel of its own.

A request may switch protocols (`serve`'s `upgrade`, `Lanes/Web/Http/Upgrade.lean`, the decision
"WebSockets behind the gate"): its head is handed on alone and nothing after it is read; the
system's `101` is not written by the connection, which hands itself over once every earlier
response is written (`Http.Conn.flushSwitch_switch`, `Http.Conn.respond_upgrading`) to the
protocol's pure machine, run by the same loop. The protocol's requests go through the gate as
pieces do, and the system reaches the connection with outputs that answer the head's id, which
the gate would drop (`Http.Gate.receive_absent`). WebSockets are such a protocol
(`Lanes/Web/Http/WebSocketSession.lean`, a root of its own, so a program that does not import it
does not build or link it): each message received is a request through the gate, answered
`Response.taken` before the next is handed on; a socket holds at most one place among the gate's
pending requests, and only while that request is with the system (`WebSocket.Session.step_submits`,
`step_withSystem`); everything it writes after the `101` is frames a client reads back
(`WebSocket.Session.step_writes`); the system is told once when a socket ends. An open socket
counts as a connection against `connections_max`. `examples/chat` is a room built on it.

The server tells its operators how it is, each part off by default (`ServerConfig.ops`,
`docs/decisions/D69-observability.md`): a metrics page in the Prometheus text format, liveness,
readiness, request ids and a JSON access log. What is decided is pure. `Lanes/Lib/Metrics.lean`
renders counters, gauges and histograms, whose buckets count the observations at or below their
bounds (`Metrics.Histogram.observeAll_eq`) and whose label values a reader reads back as written
(`Metrics.readLabelValue_escapeLabel`). `Lanes/Web/Http/Ops.lean` says which request is the
operators', none with nothing configured (`Http.Ops.route?_default`), that the metrics page is
answered only to a peer on a loopback address unless the configuration lets others in, however
its path is written (`Http.Ops.route?_metrics`), while liveness and readiness answer every peer
(`Http.Ops.route?_peer`), that readiness answers
`200` exactly when the runtime has booted and the server is not stopping or draining
(`Http.Ops.answer_ready`), and what a log line holds, the JSON text of its record
(`Http.Ops.Access.parse_line`). `Lanes/Web/IO/Ops.lean` answers an operator's request before it
is prepared or has an id, so it never reaches the runtime, and passes every other request on as it
came. So the same inputs enter the system with all of it on as off, which is trusted and tested
(`Tests/Ops.lean`). `Server.stopOnSignal`
is a stop that drops nothing in flight: at SIGTERM or SIGINT readiness answers `503`, the
requests the runtime has taken are answered until none is left or a deadline passes, and then the
server stops, as `Http.Shutdown.step` decides (the platform's signals, below); performed by
trusted IO and tested with a child process.

Where: `Lanes/Web/` (`Http/`, `IO/Server.lean`), `Lanes/Semantics/Front.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| No request is answered more often than it arrived | `Http.served_answered_le_arrived`, `Http.kernel_served_answered_le_arrived`, `Lanes/Web/Http/FrontSound.lean`; gate `Tests/Axioms/Web.lean` | The link from outside to the gate does not duplicate (the kernel's does not); "no id answered twice" also needs distinct ids (`Http.served_answered_nodup`), which the server takes from `Http.Waiting` (trusted) | proved |
| A waiting request keeps its deadline armed | `Http.served_deadlines_armed`; gate `Tests/Axioms/Web.lean` | None | proved |
| Every request the gate admits is answered, by the system or with `504` | `Http.served_pending_answered`, `Lanes/Semantics/Front.lean`; gate `Tests/Axioms/Semantics.lean` | A fair run (that the runtime's runs are fair is assumed, TRUSTED "Progress"), and the gate does not crash | proved |
| Every request that arrives is answered; with distinct ids, exactly once | `Http.served_arrival_answered`, `Http.fronted_arrival_answered`, `Lanes/Semantics/Front.lean`, from `System.Run.Fair.delivered`; with `Http.served_answered_nodup` for "exactly"; gate `Tests/Axioms/Semantics.lean`; `Tests/Gate.lean` checks it on two requests and that each premise is needed | A fair run (assumed of the runtime, TRUSTED "Progress"); the gate does not crash; the link from outside to the gate loses nothing. "Exactly once" also needs distinct ids and a link from outside that does not duplicate | proved |
| Each server connection writes responses in the order requests were read, each once, within its bounds | `Http.Conn.run_writes` and the others of `Lanes/Web/Http/ConnSound.lean`; gate `Tests/Axioms/Web.lean` | The IO of `Lanes/Web/IO/Server.lean` performs what `Conn.step` says | proved; the IO trusted |
| A streamed response is read back by the client as its head with the parts the system gave, in order, as its body | `Http.Conn.read_streamed`, `Http.Conn.pulled_part`, `Http.Conn.flushStream_ended`, `Lanes/Web/Http/ConnSound.lean`; gate `Tests/Axioms/Web.lean` | Parts of at most sixteen hex digits of size and a body under 10^18 bytes; each of a step, the whole run model-checked (`Tests/HttpStream.lean`); the IO trusted to give each answer to the pull it was asked under | proved of each step; checked of a run |
| The pieces of a streamed request body make up the body the strict reader reads, in order, one with the system at a time | `Http.Conn.pump_piece` (each piece is what `Inflow.gather` reads at the connection's position), `Http.Conn.gather_length` (of a body framed by its length, the bytes from that position, the last piece exactly at its end); `Tests/HttpStream.lean` | Of a whole run, model-checked on a body framed by its length and one in chunks, not proved; the IO trusted to tag each piece with its head's id | proved of each step; checked of a run |
| The client's reader of Server-Sent Events reads back the events a stream writes, in order, each once | `Http.Sse.parse_written`, `Http.Sse.Event.ofResponse_valid`, `Lanes/Web/Http/SseSound.lean`; gate `Tests/Axioms/Web.lean` | Against a model of the WHATWG reader that splits lines at LF, gives each event its own block's `id` and `retry`, and takes a `retry` of at most eighteen digits | proved |
| Everything a WebSocket writes after the `101` is frames a client reads back: unmasked, none longer than `frame_max`, every control frame whole and at most 125 bytes, a close's reason cut to fit | `WebSocket.Session.step_writes`, `WebSocket.Conn.receive_sends`, `WebSocket.size_closePayload`, with `WebSocket.decode_encode`, `Lanes/Web/Http/WebSocketSessionSound.lean`; gate `Tests/Axioms/Web.lean`; live against Python's websockets client (`Tests/WebSocket.lean`) | The loop writes what the session asks, in order (trusted) | proved of each step |
| A WebSocket holds at most one place among the gate's pending requests: it hands the system at most one request in a step, and none while one is with it but on that one's answer | `WebSocket.Session.step_submits`, `WebSocket.Session.step_withSystem`; `Http.Gate.receive_absent` for the outputs that go to a socket instead of the gate | The loop submits what the session asks and tells it each answer under its index (trusted) | proved of each step |
| A streamed connection holds at most one piece and one part of a stream, and pulls only once what it wrote was sent | `Http.Conn.flushStream_going`, `Http.Conn.pulled_large`, `Lanes/Web/Http/ConnSound.lean`; `Tests/HttpStream.lean` | The loop tells `sent` when its last write ends (trusted) | proved of each step |
| HTTP: requests a second at 1, 16 and 64 connections against Go `net/http` | `bench/run.sh` through the Bench workflow on a c7a.16xlarge, commit 70d61f52d0aa, 2026-11-27 (`bench/README.md`) | One set of runs; the report is the workflow's artifact, not in the repository | tested (measured) |

Also:

- Proved of `fronted sys` by projection from the gate alone, for every `sys`: at most once per arrival where the link from outside to the gate does not duplicate (`Http.fronted_answered_le_arrived`, from `Http.Gate.answered_le_handled`) and deadlines stay armed (`Http.fronted_deadlines_armed`); and in every fair run in which the gate does not crash a request the gate has admitted is answered (`Http.fronted_pending_leaves`, `Http.fronted_pending_answered`, from `Http.Gate.pending_leaves` and `Http.Gate.pending_answered` of the gate alone, through the hidden inputs and outputs and the join); model-checked with the properties checked of `served`, and the premises of the leads-to rule on the gate alone with the link a join gives it from outside.
- Proved of `served sys` for every system, bridge and configuration: an arrival is answered at most once in any environment whose link from outside to the gate does not duplicate (`Http.served_answered_le_arrived`, `Http.kernel_served_answered_le_arrived`, with crashes, loss, reordering and duplication elsewhere allowed), a waiting request keeps its deadline armed (`Http.served_deadlines_armed`), and in every fair run in which the gate does not crash a request the gate has admitted is answered, by the system or with `504` (`Http.served_pending_leaves`, `Http.served_pending_answered`). These are the theorems of `fronted sys` carried through its hidden inputs and outputs.
- The server prepares each request as its bridge says (`Bridge.prepare`, pure) on the request's own task before it enters the runtime, so a password or a cookie a bridge takes out never enters the system and slow work is not done in a step (`docs/decisions/D44-request-prepared-before-journal.md`).
- For its operators, each off by default (`ServerConfig.ops`, `docs/decisions/D69-observability.md`): a metrics page in the Prometheus text format (requests by method and status class, latency, connections open and refused, requests in flight, the inbox), liveness, readiness that answers `200` exactly when the runtime has booted and the server is not stopping or draining (`Http.Ops.answer_ready`, `Server.drain`), request ids taken from a client only when bounded and plain (`Http.Ops.RequestId.accept?_eq_some`), and a JSON access log whose lines are the JSON text of their records (`Http.Ops.Access.parse_line`) and hold no query, header or body; none of it reaches a system, which is trusted and tested: the same inputs enter the system with all of it on as off.
- The server reads and writes HTTP/1.1 itself on `Std.Net`, with no `Std.Http`: each connection is `Http.Conn.step`, pure, model-checked against a client that sends in any pieces, pipelines and leaves, and proved to write responses in the order requests were read, each once (`Http.Conn.run_writes`), to hand on only requests the strict reader reads (`Http.Conn.step_submit_read`), to keep its buffer within `message_max` and its requests in flight within `inflight_max` (`Http.Conn.run_buffer`, `run_slots`), to take nothing once closed or no longer reading (`Http.Conn.step_closed`, `step_notReading`, `step_reading`), to stop reading at a deadline (`Http.Conn.step_tick`) and to write what the client's reader reads back (`Http.Conn.read_encode`), with `100 Continue`, keep-alive, pipelining, deadlines for a slow head or body and a bound on connections (`docs/decisions/D57-the-server-runs-its-own-connections.md`).
- The strict reader of requests (`Http.Request.read`, `docs/decisions/D49-the-server-reads-requests-by-a-strict-profile.md`) is proved final once it answers (`Http.Request.read_append`), to wait only within its limits and answer within them (`Http.Request.read_more`, `read_done`), to read back what `Request.wire` writes wherever it starts and whatever follows, at its last byte and not before (`read_wire`, `read_wire_extract`), and to refuse a length beside a coding, two lengths, a blank before a colon, obs-fold, a bare CR or LF and a malformed chunk size for every head of those shapes (`read_lengthAndCoding`, `read_twoLengths`, `read_blankInName`, `read_fold`, `read_bareCR`, `read_bareLF`, `read_badChunkSize`); its other refusals, and its verdicts against Go's, Node's and h11's parsers on a corpus, are tested (`oracles/go/requests/requests.py`: stricter or alike on every case).
- The HTTP server passes against the gate's assumption.
- WebSockets (RFC 6455, `Lanes/Web/Http/WebSocket.lean`, its own root): the opening handshake read from a request and answered, frames written and read back (`WebSocket.decode_encode`), and a server's side of a connection, pure: fragments put together within a message's limit, a ping answered, a close echoed, text checked as UTF-8 and the close codes of §7.4; compared with Python's websockets on generated byte streams (`oracles/websockets`). The server runs it behind the gate (`Lanes/Web/Http/WebSocketSession.lean`, above). Not done: a WebSocket client, extensions (permessage-deflate), and `Http.Loopback` running a protocol switched to, which ends its exchange at the switch.

## Pages, sessions and sign-in

Around the gate, pure: requests and responses as data; typed routes whose links the
server reads back and `dispatch` hands to their route's handler (`Http.dispatch_link`); forms
(`Http.parseForm_encodeForm`); HTML values that a browser reads as the tree they were rendered
from, so text stays text (`Html.lex_render`, against a model of the HTML tokenizer), with URL
attributes limited to `Html.allowedSchemes` (`Html.safeUrl_scheme`), and a template macro
(`Lanes/Web/Html/Syntax.lean`, trusted); htmx attributes taken from routes (`Hx.request_match?`);
cookies a browser stores with exactly the attributes they name (`Http.readSetCookie_header`,
against RFC 6265's algorithm); and `Lanes/Web/Auth/`: signed tokens and form tokens that name
the key they are checked with, so keys rotate (`Auth.verify_rotate`), and accept exactly what
was signed for their purpose and session, a token before its expiry (`Auth.verify_eq_some`,
`Auth.verify_expired`, `Auth.checkForm_iff`), and another's only through an HMAC collision
(`Auth.verify_sign_other`, `Auth.checkForm_other`); Argon2id password hashes stored as PHC
strings, which carry their cost and salt and read back as written (`Auth.Phc.parse?_encode`),
checked under what they carry and asked to be hashed again at a new cost
(`Auth.Password.verify_phc`); failed attempts that lock at their limit
(`Auth.Attempts.locked_unlock_repeat`) and sessions that keep the newest (`Auth.Sessions.ids_starts`)
and end after a lifetime, judged at the time a request arrived, so that one over is never let in
again (`Auth.Sessions.accepts_iff`, `Auth.Sessions.Ended.run`). Those two are an actor's state,
lost at a restart; what must survive one is in rows (`Lanes/Web/Auth/Rows.lean`): failed log-ins,
a row per user that each transaction updates with `Auth.Attempts.fail` and `succeed`, so a
restart unlocks no account; and open sessions, a row each with an index by user, which a log-out
deletes, so that a session closed before its signed token expires stays closed. A session is
judged at a time no earlier than its last use, so a clock that steps back, another instance's
that lags, or a request with no time neither ends one nor lets in one that is over.

Sign-in with another service (`docs/decisions/D72-sign-in-with-oauth.md`) is OAuth 2.0's authorization
code flow with PKCE and OpenID Connect on it, decided in `Lanes/Web/Auth/OAuth.lean` and done
where a request arrives, before the system (`serve`'s `arrive`, `Lanes/Web/IO/SignIn.lean`), so no
code or token enters the system. A sign-in begun is a ticket the browser keeps in a cookie under the
server's tag, so beginnings take no room on the server. A callback is accepted only with its
browser's ticket, for its state and provider, not expired (`OAuth.check_ok`), and no state twice
(`OAuth.Used.accepted_once`), which is also model-checked against an attacker's browser;
an ID token only if its header names RS256 or ES256, a key of the provider's set of that
algorithm and `kid` checks it, and every claim passes (`OAuth.IdToken.verify_accepted`,
`Lanes/Web/Auth/Jose.lean`). The system gets the identity in headers a client cannot send
(`OAuth.identity?_strip`), read back as written (`OAuth.identity?_withIdentity`). Its name, the
provider's `name` or GitHub's `login`, is a `DisplayName`: at most 64 characters, none of them a
control or reordering mark, by its type (`OAuth.DisplayName.length_le`), and text a page shows
escaped. Vendors' presets are services, in `Lanes/Services/Oidc/`: Google's and GitHub's.

The sign-in's IO (`Lanes/Web/IO/SignIn.lean`) holds the random values of a beginning and the key of the
tickets, the states used and each provider's keys held in references, and the calls to the token endpoint,
the JWK Set and a user API; every decision is `Lanes/Web/Auth/OAuth.lean`'s (above).

Where: `Lanes/Web/Http/`, `Lanes/Web/Html/`, `Lanes/Web/Auth/`, `Lanes/Web/IO/SignIn.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A link printed from a route is matched by that route's handler | `Http.dispatch_link`, `Lanes/Web/Http/RouteSound.lean`; gate `Tests/Axioms/Web.lean` | Links printed from routes; a link written by hand is not covered | proved |
| Rendered HTML is read by a browser as the tree it was rendered from, so text stays text | `Html.lex_render`, `Lanes/Web/Html/BasicSound.lean`; gate `Tests/Axioms/Web.lean` | Against a model of the tokenizer's data and double-quoted-attribute states (the limits of "Pages, sessions and sign-in") | proved |
| The template macro produces the element the template shows | `Tests/Html.lean` |  | trusted, tested |
| HTML from a user, sanitized, holds only the elements and attributes of the policy, and URL attributes only URLs `safeUrl` passes of the policy's schemes | `Html.sanitize_safe`, `Html.lex_sanitize`, `Lanes/Web/Html/SanitizeSound.lean`; gate `Tests/Axioms/Web.lean`; attacks written by hand (`Tests/Oracle/Html.lean`) | The browser model of `Html.lex_render`; what an element or attribute the policy allows does is the policy's choice | proved |
| A sign-in's callback is accepted only with its browser's ticket, for its state and its provider and not expired, and no state twice, among at most `maxUsed` states kept | `OAuth.check_ok`, `OAuth.Used.accepted_later`, `OAuth.Used.accepted_once`, `OAuth.Used.length_claim`, `Lanes/Web/Auth/OAuth.lean`; gate `Tests/Axioms/Web.lean`; model-checked against an attacker's browser across a restart and tested end to end (`Tests/OAuth.lean`) | The edge keeps the states used and performs what it decides (TRUSTED, "The sign-in's IO"); the key and the random source | proved; the edge trusted, tested |
| An ID token is accepted only when its header names RS256 or ES256, a key of the provider's set of that algorithm and `kid` checks its signature, and every claim passes | `OAuth.IdToken.verify_accepted`, `OAuth.IdToken.check_ok_iff`, `Jose.verify_ok`; gate `Tests/Axioms/Web.lean`; refusals of `none`, HS256 keyed by the public key, an unknown `kid`, a changed payload and each claim tested end to end (`Tests/OAuth.lean`); `Jose.verify` against jwcrypto 1.6.2 on generated tokens, valid and tampered (`oracles/jwcrypto`) | The signature check (`native/verify.c`); the provider holds only its keys in its set (TRUSTED, "Identity providers"); the wall clock | proved of the decision; the signature trusted, tested |
| Failed log-ins kept as rows stay within their limit, an account with that many locked, under every transaction of `Failures`; a closed session's id lets nobody in again | `Rows.Failures.bounded`, `Rows.Sessions.closed_refused`, `Lanes/Web/Auth/RowsSound.lean`; gate `Tests/Axioms/Web.lean`; `Tests/Auth.lean` | The limit is below `2 ^ 63`; with `Db.invariant`, PostgreSQL behaves like the store's model | proved |
| No code, token or client secret of a sign-in reaches the system, and a client cannot send the identity headers | `OAuth.identity?_strip`, `OAuth.identity?_withIdentity`; `Tests/OAuth.lean` end to end | That the edge lets a callback in only through `withIdentity` (TRUSTED, "The sign-in's IO") | proved of the headers; trusted, tested |

Also:

- Cookies a browser stores with exactly the attributes they name (`Http.readSetCookie_header`, `Http.setCookie_read`) and read back (`Http.parseCookies_cookieHeader`), the origin check of a form (`Http.Request.sameOrigin_iff`), a per-route body limit.
- Character references decoded as the WHATWG standard decodes them, every name of its table (`Html.unescape`), compared with Go's `html.UnescapeString`; and a sanitizer of HTML from users with an allowlist of elements, attributes and URL schemes (`Html.sanitize`, `Policy.basic`), its own root: `import Lanes.Web.Html.Sanitize`.
- Htmx attributes as typed values taken from routes (`Hx.request_match?`), triggers with no script filter (`Hx.render_plain`).
- Scoped template macro with components, fragments and attribute splices.
- Typed routes whose links reach their route's handler (`Route.match?_link`, `Route.link_target`, `Http.dispatch_link`).
- `Html` that a model of the browser's tokenizer reads as the tree it was rendered from, text as text and attribute values as given (`Html.lex_render`), with URL attributes whose scheme, however spaced or cased, is `http`, `https`, `mailto` or `tel` (`Html.safeUrl_scheme`).
- A provider of OAuth 2.0 alone is asked its user API; the identity reaches the system in headers a client's are dropped from (`OAuth.identity?_strip`), with the provider's name for the user bounded and stripped of control characters by its type (`OAuth.DisplayName`).
- The claims of an ID token checked are its issuer, audience, authorized party, expiry, `nbf`
  within a skew and nonce; JWK Sets are cached and fetched again at most once a minute
  (`OAuth.Keys.no_fetch_within`): proved.
- Password hashes by Argon2id, stored as PHC strings (`Auth.Phc`), are compared with OpenSSL's
  `CRYPTO_memcmp`; a session ends
  after an idle or absolute lifetime, checked on use and swept on write, with no timer, and the
  oldest is closed when a user has too many (`Auth.Sessions.ids_starts`).

### Limits

- A purpose of `Auth.sign` must have no zero byte, and `form` is the purpose of form tokens.
- Templates cannot contain inline `<script>` or `<style>` text, and `render` gives those elements no children; URL attributes accept only relative, `http`, `https`, `mailto` and `tel` URLs. An attribute that holds code or markup (`onclick`, `srcdoc`, `style`) takes its value as given, escaped: what it means is the application's.
- `Html.sanitize` nests elements as the input does, and does not repair a table or a paragraph as a browser's tree builder does: a browser may move what it keeps, but reads no element or attribute it did not keep. It keeps no `style` attribute and no CSS.
- Templates take text children as string literals (`<p>"text"</p>`), not bare text.
- The browser model of `Html.lex_render` is the tokenizer's data and double-quoted-attribute states: a browser also lowercases names, keeps the first of two attributes of one name, and reads the content of `title`, `textarea`, `noscript` and the other raw text elements as text.

## Adapters and models of external services

Whatever a system does not contain reaches it through outputs and inputs, never through an effect
that does IO (D26). An adapter is a model of the outside, an `Outside`
(`Lanes/Outside/Basic.lean`) that the checker explores the system against, and a handler that
performs; a conformance test records a real run and checks it with `Outside.allows`. Where an
adapter has something to decide, it is a pure function with its theorems (rule 3.9).

- **Clock** (`Lanes/Outside/IO/Clock.lean`): the time as an input, never earlier than one given
  before, nor than the floor it was started with. Its model is the monotonic clock (`Clock.outside`, `Lanes/Outside/Clock.lean`);
  the wall clock as the operating system reads it, which NTP may set back by up to twice its skew
  (`Clock.wall`, `Clock.wall_back_le`), is a model of its own for a system that reads it.
- **HTTP client** (`Lanes/Web/IO/Client.lean`): HTTP/1.1, or HTTPS through the TLS binding
  below, one request per connection; a `HEAD` is read without a body (`Response.readHead`). The bytes are pure (`Lanes/Web/Http/Wire.lean`): the request writer frames the message
  itself (`Request.fields_framing`), and the reader is proved to read a response written as a
  server writes it as soon as its last byte is there, to stay within its limit and to end
  (`Lanes/Web/Http/WireSound.lean`: `Response.read_wire`, `Response.read_more`; D39).
- **Models of external services** (`Lanes/Outside/`, D61 and the decision on models of external
  services): what a service a system calls may do, built from three combinators on a model of
  the service (`Rpc.Server`). `Rpc.outside` answers each call at most once, or `unknown`, or never
  (`Rpc.answered_le_called`); an `unknown` leaves open whether the request took effect, so a
  request counts as an effect the service may have had from the moment it is sent.
  `Idempotent.server` gives a request under a key the effect of the first under that key, a
  repeat the first's answer or a refusal, and proves that a request always sent under one key
  has at most one effect in every run the model allows (`Idempotent.at_most_once`).
  `Events.bounded` delivers events late, out of order and up to `maxDeliveries` times
  (`Events.deliveries_le`). `ObjectStore.server` is an object store whose reads see the last write answered,
  unless a write that timed out, was refused or overlapped it may have come after; a get is
  answered only with an object a put sent (`ObjectStore.read_sent`), and a head says a key holds
  one only when a put sent one under it (`ObjectStore.held_sent`); a write granted to someone else,
  a browser's through a presigned link or a form, is never answered and may land or not.
  `Multipart.server` is a store's multipart uploads, parts lost, sent again, out of order and
  completed twice: an object a read sees is exactly the parts some Complete of its key listed, in
  order, each sent as that part with the tag listed (`Multipart.read_listed`,
  `Multipart.completed_sent`). `Effects` is the class of services that hold things with a lifecycle,
  made under a key and reported by webhooks, with two instances: payments, with the statuses
  Stripe documents for a PaymentIntent (`Lanes/Services/Stripe/Payments.lean`), and email
  (`Lanes/Outside/Effects/Email.lean`). A system's part of a proof is a fact about what its steps
  emit, lifted to every run by `System.Emits.outputs`; `examples/payments` proves a shop charges
  each order at most once from an outbox (`Shop.charged_at_most_once`). That a real service does only
  what its model allows is trusted; the S3 client's runs against a fake are checked against the
  object store's, and no adapter talks to a real service yet.
- **More outside systems** (the decision on models of more outside systems), each with a fixture
  in `Tests/` whose seeded bug the checker finds: a queue as SQS gives one, received at least once,
  again at any moment until deleted with its latest receipt, in any order or by FIFO group, at most
  `maxReceives` times a copy (`Lanes/Outside/Queue.lean`, `Queue.received_le`), and a run of
  moto's SQS through the AWS service's calls (`Aws.Sqs`) that the model allows; a cache in front
  of a store, evicting at any moment, with leases and, optionally, stale reads
  (`Lanes/Outside/Cache.lean`, `Cache.read_sent`, `Cache.fill_unleased`); a service that throttles
  with `429` and `Retry-After`, a combinator over `Rpc.Server` (`Lanes/Outside/Throttle.lean`,
  `Throttle.throttled_inner`, `Throttle.wait_le`); and a shared cache in front of the server, what
  RFC 9111 lets a CDN keep (`Lanes/Web/Http/SharedCache.lean`), which serves nothing `private` or
  `no-store` (`SharedCache.serve_storable`), and whose `leaks` is a check an application runs on
  its exchanges: with no leak, the cache gives each request what the origin gave it
  (`SharedCache.serve_of_leaks`).

Where: `Lanes/Outside/`, `Lanes/Outside/{Rpc,Idempotent,Events,Queue,Cache,Clock,Throttle}.lean`,
`Lanes/Outside/Effects/`, `Lanes/Outside/IO/Clock.lean`, `Lanes/Web/IO/{Client,Tls}.lean`,
`Lanes/Web/Http/{Wire,WireSound}.lean`, `Lanes/Web/Http/SharedCache.lean`, `Lanes/Proof/Outputs.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| The HTTP client reads a response written as a server writes it, stays within its limit and ends | `Response.read_wire`, `Response.read_more`, `Lanes/Web/Http/WireSound.lean`; gate `Tests/Axioms/Web.lean` | Responses of the forms `Response.wire` writes; other forms are tested only | proved |
| A request always sent under one idempotency key has its effect at most once, in every run a model of a service behind keys allows; each call is answered at most once; each event delivered at most `maxDeliveries` times | `Idempotent.at_most_once`, `Idempotent.keys_nodup`, `Effects.at_most_once`, `Rpc.answered_le_called`, `Events.deliveries_le`, `Lanes/Outside/`; gate `Tests/Axioms/Outside.lean` | Of the model: an effect counts from the moment its request is sent, whether or not it happened | proved |
| A real payment or email service does only what its model allows | The assumptions listed in `docs/decisions/D65-models-of-external-services.md`; for email, a run through `Ses.handler` against moto's SES, `oracles/moto/ses.jsonl`; for payments, runs written by hand, `Tests/Outside.lean` | Keys that do not expire; webhooks within `maxDeliveries`; that moto answers as SES does | trusted; email tested against moto's SES, nightly; payments not tested against a service |
| A get from the object store's model is answered only with an object a put sent under that key, in every run the model allows | `ObjectStore.read_sent`, `Lanes/Outside/ObjectStore.lean`; gate `Tests/Axioms/Outside.lean` | None | proved |
| A head of the object store's model says a key holds an object only when a put, the system's or one it granted someone else, sent one under it, in every run the model allows | `ObjectStore.held_sent`, `Lanes/Outside/ObjectStore.lean`; gate `Tests/Axioms/Outside.lean` | None | proved |
| A queue's model gives each message at most `maxReceives` times a copy, at most `maxReceives` times from a FIFO queue, and never again once deleted with its latest receipt unless it is sent again | `Queue.received_le`, `Queue.fifo_received_le`, `Queue.deleted_not_received`, `Lanes/Outside/Queue.lean`; gate `Tests/Axioms/Outside.lean` | Of the model | proved |
| A consumer that applies every message it receives applies one twice; one with a table of the ids it applied applies each once, through redeliveries, a crash and a FIFO queue | `Tests/Queue.lean` | Two messages, two receives a copy, one crash | checked |
| A cache's model answers a get only with a value a write sent under its key, and never stores a fill sent when its token was not the key's lease | `Cache.read_sent`, `Cache.fill_unleased`, `Lanes/Outside/Cache.lean`; gate `Tests/Axioms/Outside.lean` | Of the model | proved |
| A read-through cache whose fill lands after the write's invalidation leaves the old value for later readers; with a lease every read begun after the update gives the new value, however the cache evicts; a cache that may answer stale values breaks that | `Tests/Cache.lean`, run by `lanesCheck` | Two readers, one writer, one key, no lost answers | checked |
| The wall clock's model is never set back by more than twice its skew; the monotonic clock's never goes back | `Clock.wall_back_le`, `Clock.wall_latest_le`, `Clock.outside_ge`, `Lanes/Outside/Clock.lean`; gate `Tests/Axioms/Outside.lean` | Of the model | proved |
| An expiry worked out from two wall-clock readings comes back after the clock is set back, and one worked out from the latest time seen does not | `Tests/WallClock.lean` | One token, two checks, skew 1 | checked |
| A throttled answer leaves the service as it was, the service never asks for a wait of more than `maxRetryAfter`, and within a limit of `burst` a call is not throttled | `Throttle.throttled_inner`, `Throttle.wait_le`, `Throttle.within_not_throttled`, `Lanes/Outside/Throttle.lean`; gate `Tests/Axioms/Outside.lean` | Of the model | proved |
| A caller that retries a `429` at once calls while told to wait and may give up; one that waits as told calls only when it may and gets through | `Tests/Throttle.lean` | Two requests, three attempts each, one call a tick | checked |
| A shared cache's model serves nothing `private` or `no-store`, and only to a request whose varying headers are the stored one's; with no `leaks` among some exchanges, it gives each of their requests what the origin gave it | `SharedCache.serve_storable`, `SharedCache.serve_reuses`, `SharedCache.serve_of_leaks`, `Lanes/Web/Http/SharedCache.lean`; gate `Tests/Axioms/Web.lean` | RFC 9111's rules for a shared cache (TRUSTED) | proved |
| A page that shows a session's records, sent without `Cache-Control`, is served to another client; sent `no-store` it is not | `Tests/SharedCache.lean` | The seeded case | checked |
| Every output of every run is one some actor's step or start emits | `System.Emits.outputs`, `Lanes/Proof/Outputs.lean`; gate `Tests/Axioms/Proof.lean` | None | proved |

Also:

- The clock adapter and the HTTP client each have a model, a handler and a conformance test; the clock gives wall time that never goes back, nor before the
  floor it was started with.
- The HTTP client's reader reads back a response framed by its length, in chunks, by the end of
  the connection, or after interim responses, as soon as its last byte is there and not before
  (`Response.read_wire`, `read_wire_extract`, `read_more`, `read_some`, `read_append`): proved;
  what it makes of other forms, and what it refuses, is tested. Its certificate and name checks
  are trusted and tested against `openssl s_server`, not proved.
- The cache, the queue, the throttling service, the shared cache (`SharedCache.leaks`) and the
  wall clock are each model-checked with a seeded bug and its fix.

### Limits

- The shapes are kept whole in the core, as library pieces, whether or not a service of
  `Lanes/Services/` uses them. Those with no run recorded from a real system are not yet checked
  against a real service: the cache (`Lanes/Outside/Cache.lean`), the throttling service
  (`Lanes/Outside/Throttle.lean`), webhooks (`Lanes/Outside/Events.lean`), idempotency keys
  (`Lanes/Outside/Idempotent.lean`), the shared cache (`Lanes/Web/Http/SharedCache.lean`) and the
  wall clock (`Lanes/Outside/Clock.lean`, a platform model). Each says so in its header, and
  `oracles/README.md` says why.

## The core and the services

The core is everything `import Lanes` gives: the semantics, the runtime, HTTP, the standard
library, the platform models and the shapes of outside services (`Lanes/Outside/`). A service is
a vendor's: its client, and, when it is checked, its model, built from a shape, and its oracle,
each in `Lanes/Services/<Name>/` with a README that says which and whether it is checked (model
plus oracle) or a client only (`Lanes/Services/README.md`, D110). A service imports the core and the core never
imports a service: lint `layering` fails otherwise (`LanesCli/Layers.lean`). An application
imports the services it calls (`import Lanes.Services.Postgres`), and Lake builds only those.
HTTP, Signature Version 4, OAuth and OpenID Connect are protocols, not services, and stay in the
core. A service gets a model and an oracle of its own only when an application's proof depends
on how it behaves (`docs/decisions/D113-service-models.md`): Postgres, S3, SES and payments are
checked, a model plus an oracle; the sign-in presets, AWS's role credentials, CloudFront and SQS
are clients only, with tests, and SQS's calls are paired with the queue shape when an
application needs it.

The platform models in the core are the clock, monotonic (`Clock.outside`) and the wall clock
(`Clock.wall`) in `Lanes/Outside/Clock.lean`, the file system with crash semantics
(`Lanes/Outside/FileSystem/`), the environment a process starts with, and the stop a signal
starts (both below). Randomness needs no model of its own: a step is told a seed, and every
theorem about a step holds for every seed (below). The network and DNS, and standard input and
output, have no model: the decision "The environment, signals and randomness, as platform
models" says what one would give and cost.

## The platform: the file system

The platform models are what the machine a program runs on may do (D110, the environment's
first layer); the clock is one, in the adapters above. The file system is a value (`Fs`): every
inode, a file being what is on the disk for sure and the changes since its last `fsync`, a
directory the same for its entries. `Fs.step` is what a call does, `Fs.failures` what an `io`
error may leave, since it may hide whether the call took effect, and `Fs.crash` what a loss of
power may leave, every outcome listed by `Fs.crashes` (`Fs.crash_mem_crashes`), so a test can
check every one. The model is pure, in the lowest package, so that the standard library and an
application's proofs use it without actors; as an outside (`FileSystem.server`, through
`Rpc.outside`) it adds `io` faults and a power loss as an event, for the checker and for runs
checked against it. `FileSystem.IO.perform` makes each call with Lean's `IO.FS` and the calls
bound in `native/lanes.c`, deciding nothing.

Two patterns are proved, the ones a journal, SQLite or Raft is built on. `Replace.plan` replaces
a file whole: it unlinks a temporary file a crash left, writes the new bytes beside the target,
syncs them, renames them over it and syncs the directory; `File.replace` runs it. `Log` is a file
only appended to and synced from time to time.

Where: `Lanes/Outside/FileSystem/`, `Lanes/Outside/FileSystem.lean`,
`Lanes/Outside/IO/FileSystem.lean`, `Lanes/Lib/File.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| After a crash at any point of `Replace.plan`, or an `io` error that stops it, the file holds what it held before or the new bytes; once the plan has run it holds the new bytes through any crash, and the plan may run again | `Replace.crash`, `Replace.failed`, `Replace.done`, `Lanes/Outside/FileSystem/Replace.lean`; gate `Tests/Axioms/Outside.lean` | Of the model: a directory with nothing a crash could lose on the way to it, `Replace.Ready` | proved |
| After a crash at any point, an append-only log reads as a prefix of everything appended and holds everything appended before the last `fsync`; after an `io` error the same holds of a program that stops appending | `Log.crash`, `Log.failed`, `Log.read`, `Lanes/Outside/FileSystem/Log.lean`; gate `Tests/Axioms/Outside.lean` | Of the model: the log's entry in a settled directory, `Log.Ready` | proved |
| Every crash the model allows is one `Fs.crashes` lists | `Fs.crash_mem_crashes`, `Lanes/Outside/FileSystem/Basic.lean`; gate `Tests/Axioms/Outside.lean` | None | proved |
| Without faults the file system outside is a function of the calls | `FileSystem.server_same`, `Lanes/Outside/FileSystem.lean`; gate `Tests/Axioms/Outside.lean` | None | proved |
| Both patterns hold at every crash point and after every error of small runs, and a rewrite in place fails the same check | `Tests/FileSystem.lean` | The runs there | checked |
| The binding answers as the model, errors included, on the local file system | `Tests/FileSystem.lean`, each `lake test` in a temporary directory | The script there | tested |
| A loss of power leaves what the model says: the file system honours `fsync` of a file and of a directory, a rename is atomic, a file's changes since its last `fsync` survive as their first few in order, the next torn, a directory's as their first few, each whole | `TRUSTED.md`, the file system's binding | ext4's behaviour; POSIX does not promise it | trusted |

### Limits

- The model's crash rules are ext4's, with its default `data=ordered`. XFS may leave zeros where
  an append did not reach the disk, and pages written in place may reach it in any order: a
  program must not rely on the order of writes it has not synced, and a log's reader should
  check each entry (a length and a checksum) as well as rely on `Log.crash`.
- There are no links, symbolic or hard, no permissions, no file times, no space limit and no
  concurrent writers. Calls take effect in the order they are sent.
- After an `fsync` fails the model lets the file be as a crash may leave it, on the disk and to
  reads; Linux may instead keep serving the lost pages from memory for a while. A program that
  sees a failed `fsync` should stop and recover from what is on the disk.
- A loss of power cannot be tested: the crash rules are trusted, and only their consequences are
  checked against the model.

## The platform: the environment and signals

The environment a process starts with is a value (`Environment.Vars`, any list of variables, an
empty value as unset), and an application's configuration is read from it once by a reader
(`Environment.Reader`, `Lanes/Outside/Environment.lean`): data that names each variable it asks
for, with its parser, default and text. A reader written with `do` goes on past a variable it
cannot read, so `Environment.read` and `Environment.load` list every problem at once; a variable
read as a `Secret` (`Lanes/Data/Secret.lean`, the one type of secret in Lanes) never has its
value in a problem or in a `Repr`. A test or the checker runs an application under several
configurations by giving each its `Vars`; `describe` lists the variables, for a deploy's
documentation. `Environment.load` (`Lanes/Outside/IO/Environment.lean`) runs the model's own
interpreter, `Reader.runM`, with `IO.getEnv`.

SIGTERM and SIGINT start a stop that loses nothing taken; SIGKILL and a loss of power are the
semantics' restart. A server drains as `Http.Shutdown.step` decides (`Lanes/Web/Http/Shutdown.lean`):
readiness answers `503` while it goes on serving, and it stops when nothing is in flight or
`drain_ms` has passed. The listener stays open while it drains, so that a request a load balancer
sends before it reads readiness is served; `Server.stop` then closes it, stops the runtime and
answers `503` to whatever still waits. A process without a server stops with
`Runtime.stopOnSignal`, and `Runtime.stop` returns once every input taken has reached its actor
(D116). Both wait through `awaitStopSignal` (`Lanes/Runtime/IO/Signal.lean`), over `Std.Async`'s
signal waiters, with no C of Lanes; it lets the waiters go after the first signal, so a second
ends the process at once.

Randomness: a step is told a `seed` (D121), and every theorem about a step quantifies over its
context, so the seed's model is any `UInt64`; the checker explores the seeds a scenario's
moments list. Pure code that needs more draws from `mkStdGen ctx.seed.toNat`, Lean's generator.
A key, token or nonce is never made from the seed (64 bits, recorded in a trace, from a generator
that is not cryptographic): it comes from `IO.getRandomBytes` (`Crypto.randomBytes`) in an
adapter or at start.

Where: `Lanes/Outside/Environment.lean`, `Lanes/Outside/IO/Environment.lean`,
`Lanes/Data/Secret.lean`, `Lanes/Web/Http/Shutdown.lean`, `Lanes/Runtime/IO/Signal.lean`,
`Lanes/Web/IO/Server.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A reader lists every problem it finds: those of each part, in order, whatever an earlier part found | `Environment.Reader.run_bind`, `Lanes/Outside/Environment.lean`; gate `Tests/Axioms/Outside.lean`; `Tests/Environment.lean` | A part read only because of an earlier value may be asked, or not, because of that value's stand-in | proved |
| A reader reads only the variables it asks for | `Environment.Reader.run_congr`; gate `Tests/Axioms/Outside.lean` | None | proved |
| A secret's value, and what its parser said of it, never reach a problem; a `Secret` prints as `<secret>` | `Environment.secret_problems`, `Environment.field_secret_problems`, `Secret.toString_eq`; gate `Tests/Axioms/Outside.lean` | What the application does with `reveal` | proved |
| `Environment.load` reads the process's environment as the model reads `Vars` | `Lanes/Outside/IO/Environment.lean` runs `Reader.runM`, the model's interpreter; `Tests/Environment.lean` | `IO.getEnv` gives the value the process started with | trusted, tested |
| A draining server stops only when nothing is in flight or its deadline has passed, at the first look past the deadline, and once | `Http.Shutdown.step_stop`, `step_deadline`, `step_signal`, `step_stopping`, `Lanes/Web/Http/Shutdown.lean`; `Tests/Signal.lean` | `Server.stopOnSignal` performs what `step` says and looks every ten milliseconds | proved; the IO trusted |
| At SIGTERM a server answers the request in flight, or `503` at the deadline, and exits 0; a runtime alone stops with every input it took taken | `Tests/Ops.lean` (a child process), `Tests/Signal.lean` (the test process sends itself SIGTERM) | `Std.Async`'s signal waiters | tested |

### Limits

- Lean cannot list the environment, so a reader names its variables; one that a reader builds
  from another's value (`{NAME}_CLIENT_ID`) is asked as it is built, and `describe` lists it only
  under the values it was given.
- The model of the environment allows every list of variables: it says nothing a real one could
  break, so there is nothing to record against it.
- Signals other than SIGTERM and SIGINT keep their default actions; SIGHUP does not reload the
  configuration, which is read once.

## S3 and Signature Version 4

S3 (`Lanes/Services/S3/IO/Client.lean`, `docs/decisions/D71-s3-and-signature-version-4.md`): put,
get with a range, head, delete and ListObjectsV2 on a bucket, named virtual-hosted or by path
at any endpoint (AWS, MinIO, LocalStack), and links a browser follows to get or put an object.
Pure: each operation as a call signed with Signature Version 4 (`Lanes/Web/Http/SigV4.lean`),
whose target is the canonical path and query that were signed (`SigV4.target_sign`), with the
query and the signed headers in order (`SigV4.sortQuery_sorted`, `canonicalHeaders_sorted`);
what an answer means (`S3.interpret`), and a reader of the XML S3 writes, which refuses a
document type and every entity it does not know (`Lanes/Services/S3/Xml.lean`), tested against Go's
`encoding/xml`. The signatures are tested against AWS's test suite, S3's documented examples and
botocore on generated requests, the client against a fake S3 that checks every signature from
the bytes it receives, and against moto's S3, whose run the object store's model allows
(`oracles/README.md`). Bodies are whole, in memory. The
credentials are read at each call from a `SigV4.Source`: fixed, or kept fresh by something
else, with their expiry. A link or a form signed with them at the moment (`S3.presignNow`,
`S3.Post.formNow`) lasts as asked or until they expire, whichever is sooner
(`S3.expiryWithin_le`). A browser uploads with a form under a policy (`Lanes/Services/S3/Post.lean`), which bounds
the size a presigned put cannot: the policy a form carries reads back, as S3 reads it, as
exactly the conditions and the expiry given (`S3.Post.form_policy`, `S3.Post.expiration_parse`),
and a file S3 admits under it is within its size range and before its expiry
(`S3.Post.admitted_bounded`); tested against AWS's documented example and botocore, and its
forms posted to moto, which reads them but checks no policy. A form may also name where S3
sends the browser after the upload, or the status it answers, both signed in its policy. Large
objects go in parts (`Lanes/Services/S3/Multipart.lean`): a plan proved to cut a body into at most
10,000 parts, each but the last of at least 5 MiB, together the body in order
(`Plan.count_le`, `Plan.range_full`, `Plan.range_next`, `Plan.range_last`); links for a
browser's parts with their length signed (`S3.presignPart`); and a server's upload as a pure
flow, retrying, aborting what it gives up and asking the object's `HEAD` after a Complete
whose answer was lost, which `S3.upload` performs, model-checked against the multipart model
below (`docs/decisions/D78-bounded-and-large-uploads.md`), and run against moto's S3, with
calls by hand, in a run the model allows.

Where: `Lanes/Web/Http/{SigV4,SigV4Sound}.lean`, `Lanes/Services/S3/`, `Lanes/Services/S3/IO/Client.lean`,
`Lanes/Outside/ObjectStore.lean`, `Lanes/Services/S3/MultipartModel.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A real object store does only what its model allows: a read sees the last write answered, unless a write that timed out, was refused or overlapped it came after | S3's documented read-after-write consistency; the S3 client against a fake S3, `Tests/S3.lean`; a run through `S3.handler` against moto's S3, with puts in flight together and one timed out, checked with `Outside.allows`, `oracles/moto/s3.jsonl` | A store that is only eventually consistent breaks it; that moto answers as S3 does | trusted; tested against moto's S3, nightly, not against AWS |
| A request signed by `SigV4.sign` sends the target that was signed: the canonical path and query, the query sorted by escaped name and value, the signed headers in lowercase, strictly in order | `SigV4.target_sign`, `SigV4.sortQuery_sorted`, `SigV4.sortQuery_perm`, `SigV4.canonicalHeaders_sorted`, `SigV4.canonicalHeaders_lower`, `SigV4.mem_canonicalHeaders`, `SigV4.encode_chunks`, `SigV4.decodePath_canonicalPath`, `Lanes/Web/Http/SigV4Sound.lean`; gate `Tests/Axioms/Web.lean` | None | proved |
| The signature is the one AWS computes | AWS's Signature Version 4 test suite and S3's documented examples, `Tests/SigV4.lean`; botocore 1.44.12 on generated requests, every difference decided (`oracles/botocore`, `Tests/Oracle/SigV4.lean`) | That the vectors written from memory are AWS's (`docs/decisions/D71-s3-and-signature-version-4.md`); botocore signs as AWS checks | tested against botocore |
| The S3 client's calls are accepted by a store that checks signatures as S3 does, and its answers read | The test kit's fake S3, which checks each signature from the bytes it received (`Lanes/Services/S3/Testing.lean`), `Tests/S3.lean`; moto's S3 answers each call and the client reads each answer (`oracles/moto`) | That the fake checks as S3 does; moto does not check signatures; not run against AWS | tested |
| The policy of an upload form reads back, as S3 reads it, as exactly the conditions and the expiry given, in well-formed base64 of JSON within the reader's limits | `S3.Post.form_policy`, `S3.Post.decode?_encode`, `S3.Post.expiration_parse`, `Lanes/Services/S3/PostSound.lean`; gate `Tests/Axioms/Web.lean` | That S3 reads the policy as `Post.decode?` does: tested on AWS's documented example and botocore's | proved |
| A file S3 admits under a form's policy is within the policy's size range and posted before its expiry, at most seven days after signing | `S3.Post.admitted_bounded`, `S3.Post.check_holds`; gate `Tests/Axioms/Web.lean` | That S3 checks a form as `Post.check` does (conditions met, every field named, unexpired): tested against AWS's example and a fake S3, not against S3; moto, which reads the forms (`oracles/moto/s3-post.jsonl`), checks no policy | proved |
| A policy is signed as AWS signs it | AWS's documented example (`8afdbf40…`) and botocore 1.44's `generate_presigned_post`, `Tests/S3Upload.lean` | That the example remembered is AWS's: its signature, computed, matches | tested |
| A multipart plan has at most 10,000 parts, each but the last of the part size and at least 5 MiB, together the body in order | `S3.Multipart.Plan.count_le`, `Plan.range_full`, `Plan.range_next`, `Plan.range_last`, `Lanes/Services/S3/Multipart.lean`; gate `Tests/Axioms/Web.lean` | None | proved |
| In the multipart model an object a read sees consists exactly of the parts a Complete of its key listed, in order, each sent as that part with the tag listed, whatever was lost, retried, out of order or completed twice | `Multipart.read_listed`, `Multipart.completed_sent`, `Lanes/Services/S3/MultipartModel.lean`; gate `Tests/Axioms/Outside.lean` | None | proved |
| A real store's multipart uploads do only what the model allows | S3's documentation; the client's run against a fake S3 checked with the model, `Tests/S3Upload.lean`; and against moto's S3, `oracles/moto/s3-multipart.jsonl`, replayed by `lake test` | ETags name a part's content; a Complete sent again with its listing is answered as the first | trusted; tested against moto, not S3 |
| The server's multipart flow lists exactly the plan's parts in order, is done only when the store may hold that object and failed only when no Complete was answered | `Tests/Multipart.lean`: the flow against the model, 20,610 states, and a browser's parts at once, 4,434 states | The small instance: three parts, two attempts | checked |

Also:

- A browser's upload to S3 by `POST` under a signed policy, whose base64 JSON is proved to read back as exactly the conditions given and the expiry given, and under which what S3 admits is proved within the size range and before the expiry (`S3.Post.form_policy`, `S3.Post.expiration_parse`, `S3.Post.admitted_bounded`), tested against AWS's documented example and botocore's `generate_presigned_post`, and its forms posted to moto's S3.
- Multipart uploads to S3, with presigned parts whose length may be signed, a plan proved to cut a body into at most 10,000 parts of at least 5 MiB but the last (`S3.Multipart.Plan.count_le`, `range_full`, `range_last`), and a server's upload as a pure flow model-checked against a model of multipart uploads proved to read only objects that are the parts a Complete listed, in order (`Multipart.read_listed`, `Multipart.completed_sent`), and a run of the flow and of calls by hand against moto's S3 checked against that model.

## AWS

AWS (`Lanes/Services/Aws/`, `docs/decisions/D74-aws-integration.md`): credentials found in the
order of AWS's SDKs, keys in the environment, then a container's endpoint, then an instance's
metadata service (IMDSv2) unless it is turned off (`Imds.chain`, `Imds.chain_keys`,
`Imds.chain_container`, `Imds.chain_instance`), and email through SES.
When to fetch and what may be handed out is a pure machine, `Aws.Refresh.step`: nothing is
handed out within `skew_ms` of its expiry, and only what an answer gave (`Refresh.current_fresh`,
`Refresh.current_answered`); credentials held are fetched again at the margin before they
expire, and an answer within the deadline replaces them while they are still handed out
(`Refresh.refresh_in_time`); the wait after failures is bounded (`Refresh.backoff_le`,
`Refresh.retry_within`); model-checked first against a model of the metadata service with
timeouts. A task in `Lanes/Services/Aws/IO/Credentials.lean` only performs. SES's `SendEmail` is a JSON document
proved to read back with exactly its recipients (`Ses.toAddresses_json`), its answers read as
the email model's (`Ses.Answer.modelled`), and runs against a fake SES and against moto's SES
are ones the model allows; SES takes no key, so each send is a request without one. An email
that must be sent once goes through an outbox: a job with one attempt is sent at most once
(`Lanes/Services/Aws/README.md`). SQS's
calls (`Aws.Sqs`: create a queue, send, receive, delete) are data, with no handler.
CloudFront's signed URLs and cookies (`Aws.CloudFront`) are pure: a canned policy is the
document AWS gives for the URL and the time (`CloudFront.cannedPolicy_eq`), CloudFront's base64
reads back (`CloudFront.decode_encode`) and every cookie is valid, for a path and a domain
that need no escaping (`CloudFront.cookies_valid`); a domain lets a distribution on another
host of the site's get them. The policy and the link, signature included, are botocore's on
generated links.

Where: `Lanes/Services/Aws/`, its tests in `Tests/Aws/`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| The AWS integration never hands out credentials within `skew_ms` of their expiry, nor any that no answer gave | `Aws.Refresh.current_fresh`, `Aws.Refresh.current_answered`, `Lanes/Services/Aws/Refresh.lean`; gate `Tests/Axioms/Services.lean`; model-checked, `Tests/Aws/Refresh.lean` | The wall clock is right to within `skew_ms`; the edge reads the state it keeps (TRUSTED, "The AWS credentials' IO") | proved |
| Credentials held are fetched again at the margin before they expire, and an answer within the deadline replaces them while they are still handed out | `Aws.Refresh.refresh_in_time`, `Aws.Refresh.accept_due`; gate `Tests/Axioms/Services.lean`; model-checked against a service that answers in time | `Config.Valid`; the edge ticks when the machine asks; the service answers within the deadline with credentials of more than the margin | proved; the edge trusted, tested against a fake metadata service |
| The wait between failed fetches of credentials stays within `maxBackoff_ms`, and a failed fetch is tried again within it | `Aws.Refresh.backoff_le`, `Aws.Refresh.retry_within`; gate `Tests/Axioms/Services.lean` | `Config.Valid` for the retry | proved |
| Credentials come from the environment's keys first, then a container's endpoint, and the metadata service is asked only when neither is there and it is not turned off | `Aws.Imds.chain_keys`, `Aws.Imds.chain_container`, `Aws.Imds.chain_instance`; gate `Tests/Axioms/Services.lean`; `Tests/Aws/Imds.lean` | The edge reads the variables `Imds.chain` names (TRUSTED, "The AWS credentials' IO") | proved |
| A link or a form signed with credentials that expire ends no later than they do, and no later than asked | `S3.expiryWithin_le`, `Lanes/Services/S3/Basic.lean`; gate `Tests/Axioms/Services.lean`; `Tests/Aws/Imds.lean` against a fake metadata service and the fake S3 | The source gives the true expiry (`Refresh.currentHeld_creds`); the wall clock is right | proved; the IO trusted |
| A message sent through SES carries exactly the recipients given | `Aws.Ses.toAddresses_json`, `Aws.Ses.json_parse`, `Lanes/Services/Aws/SesSound.lean`; a fake SES that reads them from the JSON | That SES reads the document as `Json.parse` does | proved; tested against a fake |
| SES does only what the email model allows | A run through `Ses.handler` against a fake SES checked with `Outside.allows`, `Tests/Aws/Ses.lean`; and against moto's SES, a sender refused then verified, a send timed out, `oracles/moto/ses.jsonl` | That moto answers as SES does; not run against SES | trusted; tested against moto's SES, nightly |
| An email sent from an outbox whose jobs have one attempt is sent at most once; with two, it may be sent twice | `Tests/Worker.lean`: the worker beside the store's model and SES's (`Aws.Ses.outside` through `Aws.Ses.jobPort`), with a crash, a restart, lost answers and lost commits that take effect late; at most once rests on `Jobs.Config.claimed` and `Queue.claim_attempts` | `attempts_max := 1` and no period; `Ses.perform` makes one call for each attempt (TRUSTED); an attempt whose answer is lost leaves its job failed, sent or not | checked |
| A CloudFront canned policy is byte for byte the document AWS gives for the URL and the time | `Aws.CloudFront.cannedPolicy_eq`, `Lanes/Services/Aws/CloudFrontSound.lean`; gate `Tests/Axioms/Services.lean` | That AWS's document is botocore 1.44.12's and AWS's SDKs' (`docs/decisions/D82-cloudfront-signed-urls.md`); not run against CloudFront | proved |
| CloudFront's base64 reads back, and every parameter and cookie of a signed link needs no escaping, so every cookie is set, for a path and a domain that need no escaping | `Aws.CloudFront.decode_encode`, `Aws.CloudFront.fields_safe`, `Aws.CloudFront.cookies_valid`; gate `Tests/Axioms/Services.lean` | None | proved |
| A CloudFront signed URL is the one botocore writes, signature included | `Tests/Aws/CloudFront.lean` against botocore 1.44.12's `CloudFrontSigner` with `cryptography`'s signatures on generated links, canned and custom, RSA and P-256, SHA-1 and SHA-256; every difference a resource ours refuses | That botocore and AWS's SDKs write what CloudFront takes; not run against CloudFront | tested |

Also:

- A role's credentials from an instance's metadata service (IMDSv2) or a container's endpoint, refreshed by a pure policy proved never to hand out credentials within `skew_ms` of their expiry or that no answer gave, to fetch again at the margin so that an answer within the deadline replaces them while they are still handed out, and to bound its backoff (`Aws.Refresh.current_fresh`, `current_answered`, `refresh_in_time`, `backoff_le`, `retry_within`), model-checked against a model of the metadata service with timeouts and tested against a fake one.
- SES's `SendEmail`, its document proved to carry exactly its recipients (`Aws.Ses.toAddresses_json`), tested against a fake SES that checks signatures and against moto's SES, its runs checked against the email model, and its address check against Go's `net/mail`.

## PostgreSQL and the store model

PostgreSQL (`Lanes/Services/Postgres/`): the frontend/backend protocol 3.0 in Lean, not libpq
(`docs/decisions/D68-postgres-protocol-in-lean.md`): start-up with trust, cleartext (only when
allowed), MD5 or SCRAM-SHA-256; the extended query protocol with parameters, text both ways;
errors; transactions; plain TCP or TLS. The messages are proved to read back as written
(`Backend.read_encode`, `Frontend.decode_encode`) and tested against recorded sessions of
`psql` and of this client. A connection is a pure `Postgres.Conn.step` (`Lanes/Services/Postgres/Conn.lean`), as
the HTTP server's is: replies answer requests in the order sent (`Conn.run_fifo`), a request is
sent only to an open connection and is read by the server as sent (`Conn.step_query`,
`Conn.valid_decode`), `committed` is answered only for a `COMMIT` the server committed from a
transaction in progress (`Conn.step_committed`), the server is trusted after SCRAM only once
it proved it knows the password (`Conn.onMessage_saslFinal`), and a connection that ends
answers every request in flight `unknown` (`Conn.step_lost`); model-checked first
(`Tests/PostgresConn.lean`). With TLS (`docs/decisions/D83-postgres-over-tls.md`), after
`SSLRequest` or direct, nothing but `SSLRequest` leaves before the handshake is done
(`Conn.tls_first`) and `N` closes the connection (`Conn.step_refusedTls`); SCRAM binds the hash
of the server's certificate (`SCRAM-SHA-256-PLUS`), the one the handshake gave
(`Conn.run_bound`, `Conn.onMessage_binds`), which `Certificate.endPoint` chooses by the
certificate's signature algorithm, tested against `openssl dgst` and a real server. The IO
(`Lanes/Services/Postgres/IO/Client.lean`) only performs, the TLS handshake through `Tls.Session`
included, and resolves the host's name at each connect. Unless asked otherwise, a host on
this machine gets no TLS and any other full verification, and the default goes without TLS
only to a loopback address (`SslMode.defaultFor_disable`); `Postgres.Client.fromEnv` reads
a connection string or URI, then the service file, then libpq's variables, then a deploy's,
through `Settings.read`, pure and tested (`Lanes/Services/Postgres/Settings.lean`); its readers of
strings and service files (`Lanes/Services/Postgres/ConnInfo.lean`) are compared with libpq 18's
on generated ones (`oracles/libpq`). With several hosts it tries each in order and keeps the
first of the kind `target_session_attrs` asks for (`TargetSessionAttrs.accepts`); with several
hosts the default goes without TLS only when every one is on this machine
(`SslMode.defaultForAll_disable`). A password file others may read is refused
(`PassFile.ownerOnly_bits`). A pool (`Postgres.Pool`) is a pure policy proved to keep at most `max` connections
open and never to hand out again one handed back broken (`Pool.run_size`, `Pool.never_again`),
and an IO file that performs it (`Lanes/Services/Postgres/IO/Pool.lean`).

A transactional store (`Lanes/Outside/Store/Basic.lean`): what a store may answer at read
committed or serializable, as an `Outside` that keeps every database the answers are consistent
with, so that a `COMMIT` whose answer is lost has both outcomes, and its effect may appear
later. Its litmus runs are theorems (`Lanes/Outside/Store/Sound.lean`: `Store.write_skew`,
`Store.lost_update`, `Store.lost_commit_either`, `Store.lost_commit_later`). A table of
PostgreSQL runs it (`Lanes/Services/Postgres/Table.lean`, `Postgres.Store.handler`); that the server
behaves like the model at the level chosen is the premise of a theorem proved against it,
tested on runs recorded from PostgreSQL 16, some interleaved at random
(`oracles/postgres/store.jsonl`). The typed store (below) is the API applications use.

Where: `Lanes/Services/Postgres/`, `Lanes/Lib/Crypto/{Certificate,Sha512}.lean`, `Lanes/Outside/Store/`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| PostgreSQL's messages read back as written: every backend message in a frame wherever it starts and whatever follows, and every frontend message | `Backend.read_encode`, `Frontend.decode_encode`, `Lanes/Services/Postgres/MessageSound.lean`; gate `Tests/Axioms/Lib.lean` | Messages within their bounds (`Backend.Ok`, `Frontend.Ok`) | proved |
| The decoders read what PostgreSQL 16 and libpq 16 send, and the encoders write the same bytes again | `Tests/Postgres.lean`, recorded sessions in `Tests/Postgres/` | The sessions recorded: trust, cleartext, MD5, SCRAM, a wrong password, simple and extended queries, errors, transactions | tested |
| A PostgreSQL connection answers requests in the order sent, sends one only when open and as submitted, and never reports a failed transaction committed | `Conn.run_fifo`, `Conn.step_query`, `Conn.valid_decode`, `Conn.step_committed`, `Conn.outcome_committed`, `Lanes/Services/Postgres/ConnSound.lean`; gate `Tests/Axioms/Lib.lean`; model-checked in `Tests/PostgresConn.lean` | The IO tells `Conn.step` what happened and performs what it answers (`Lanes/Services/Postgres/IO/Client.lean`, trusted); the server reports the transaction's state in `ReadyForQuery` truly | proved; the IO trusted |
| With a password, the client trusts the server only once it proved by SCRAM that it knows the password: an `AuthenticationOk` before that, MD5 and cleartext close the connection unless `requireScram` is turned off | `Conn.onMessage_requireScram`, `Conn.onMessage_saslFinal`, `Conn.onMessage_sasl_authOk`; gate `Tests/Axioms/Lib.lean`; SCRAM's computation tested against RFC 7677 and libpq; model-checked in `Tests/PostgresConn.lean` against a server that skips SCRAM | That the computation is SCRAM-SHA-256 is tested, not proved; without channel binding (the next rows), SCRAM shows the server knows the password, not that it is the server meant | proved for the state machine |
| With TLS, the PostgreSQL client sends nothing but `SSLRequest` before the handshake is done, closes on `N`, starts the handshake only on an `S` alone and sends the start-up after it only with the ALPN protocol allowed | `Conn.tls_first`, `Conn.run_beforeTls`, `Conn.step_refusedTls`, `Conn.step_startTls`, `Conn.step_secured`, `Lanes/Services/Postgres/ConnSound.lean`; gate `Tests/Axioms/Lib.lean`; model-checked in `Tests/PostgresConn.lean` against a server that refuses TLS | The IO says `secured` only once the handshake is done and from then on sends and receives through the session (`Lanes/Services/Postgres/IO/Client.lean`, trusted); OpenSSL's TLS (`native/tls.c`, trusted) | proved for the state machine; the IO trusted |
| SCRAM over TLS binds the hash of the certificate the handshake gave (`SCRAM-SHA-256-PLUS`, `tls-server-end-point`), always with `channelBinding := .require`: the client's last message carries `c=` the GS2 header and that hash in base 64 | `Conn.run_bound`, `Conn.onMessage_binds`, `Conn.choose_endPoint`, `Conn.choose_require`, `Scram.respond_binds`, `Scram.Binding.data_endPoint`; gate `Tests/Axioms/Lib.lean`; model-checked in `Tests/PostgresConn.lean` against a relay with another certificate and one that hides the offer | That the hash is RFC 5929's for the certificate is tested (`Tests/PostgresTls.lean`: `openssl dgst`, and PostgreSQL 16 accepting it for a certificate signed with SHA-384), not proved; the DER is OpenSSL's (`native/tls.c`, trusted) | proved for the state machine; the hash tested |
| A PostgreSQL server reached through a relay that holds another valid certificate refuses a client that binds, as it refuses libpq | `Tests/PostgresTls.lean`, against PostgreSQL 16 with TLS and `Tests/Postgres/relay.py` (`LANES_POSTGRES_TLS` set), beside `psql` with `channel_binding=require` | A local server | tested against PostgreSQL 16, nightly |
| The PostgreSQL pool never has more than `max` connections open or being opened, nor more than `waiting_max` clients waiting, and never hands out again a connection handed back broken | `Pool.run_size`, `Pool.run_waiting`, `Pool.never_again`, `Lanes/Services/Postgres/Pool.lean`; gate `Tests/Axioms/Lib.lean`; model-checked in `Tests/PostgresPool.lean`; live in `Tests/PostgresTls.lean` | The IO never reports a connection opened under a number used before, and tells the policy what happened (`Lanes/Services/Postgres/IO/Pool.lean`, trusted); a connection is reusable as `Conn.reusable` says | proved for the policy; the IO trusted |
| Unless asked otherwise, the PostgreSQL client uses no TLS to this machine and full verification to any other host, and goes without TLS only to a loopback address, or with several hosts only when all are | `SslMode.defaultFor_disable`, `SslMode.defaultFor_loopback`, `SslMode.defaultFor_remote`, `SslMode.defaultForAll_disable`, `Lanes/Services/Postgres/Settings.lean`; gate `Tests/Axioms/Lib.lean`; `Tests/PostgresSettings.lean` | That `localhost` is `127.0.0.1` (RFC 6761) and that the IO connects where `Address.of` says (`TRUSTED.md`) | proved |
| The PostgreSQL client reads connection strings, URIs and service files as libpq 18 does | `oracles/libpq` on generated strings and files (`Tests/Oracle/Libpq.lean`), every difference a known one: bytes that are not UTF-8; which source wins, tested by hand from libpq's documentation (`Tests/PostgresSettings.lean`) | The libpq 18 psycopg-binary 3.3.9 ships, as recorded | tested against libpq |
| The client works against a real PostgreSQL | `Tests/PostgresLive.lean`, against PostgreSQL 16 (`LANES_POSTGRES` set); `oracles/postgres/run.sh`, nightly in the Services workflow | A local server | tested against PostgreSQL 16, nightly |
| The store model allows write skew and lost updates at read committed and refuses them at serializable; a lost `COMMIT` may or may not have taken effect, and later | `Store.write_skew`, `Store.lost_update`, `Store.lost_commit_either`, `Store.lost_commit_later`, `Lanes/Outside/Store/Sound.lean`; gate `Tests/Axioms/Outside.lean` | The runs stated | proved |
| PostgreSQL behaves like the store model at the isolation level chosen | Runs against PostgreSQL 16 at both levels, recorded and checked with `Store.State.run`, nightly, and the record again in `lake test`: write skew, a lost `COMMIT` and 50 runs of transactions interleaved at random (`oracles/postgres/store.jsonl`, `Tests/Oracle/Service/Postgres.lean`) | Every theorem proved against the store model rests on it; no two transactions open at once write one key, so no request waits on a lock | trusted, tested against PostgreSQL 16 |

Also:

- A transactional store model at read committed and serializable with lost `COMMIT` answers (`Store.outside`), run on a PostgreSQL table by `Postgres.Store.handler`.

### Limits

- That a PostgreSQL server behaves like the store model at an isolation level is a premise, tested on a few recorded runs, not proved. The model keeps at most `history_max` transactions in its serial order while one is open, and a run beyond its bounds is outside it. At read committed, `append` is checked for a free key at its answer only.

## The typed store

Durable state in PostgreSQL through typed tables and pure transactions
(`docs/decisions/D111-typed-store.md`). A table (`Lanes/Db/Basic.lean`) has typed columns of
64-bit integers, bytes, text compared byte by byte and booleans, each nullable or not, a primary
key on its first columns, and secondary indexes, unique or not. The query subset
(`Lanes/Db/Query.lean`) is a row by key, a scan on the key or an index with equality on its first
columns and a range on the next, ordered, with a limit, and an insert, update, upsert or delete
of one row by key; each means a pure function of the database (`Op.apply`). A write that would
take a key or a unique value already taken does nothing and answers `false`.

A request handler is `Q → Txn A` (`Lanes/Db/Txn.lean`): a free monad over the operations, so
that an operation may depend on what earlier ones answered, with no IO and room for one
transaction only. `Txn.run` is what it means; `TableOf α` puts a Lean type on a table, and
`lanes_data`'s `table` line derives one from a structure (`Lanes/Db/Columns.lean`). The
driver (`Lanes/Services/Postgres/IO/Db.lean`) runs it at `SERIALIZABLE`, one statement per operation
(`Lanes/Services/Postgres/Sql.lean`, pure), and tries again after a serialization failure, a deadlock,
a unique violation or a connection lost before `COMMIT`, up to `attempts_max` attempts, as
`Retry.next` says (`Lanes/Db/Retry.lean`). The model (`Lanes/Db/Model.lean`) is an `Outside`: a
call takes effect at one moment between its request and its reply, as one run of its handler; a
failed call never did; a call answered unknown may have taken effect, or may later, or never.

Where: `Lanes/Db/`, `Lanes/Services/Postgres/Sql.lean`, `Lanes/Services/Postgres/IO/Db.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| An invariant of the database that every transaction of a handler keeps holds in every database the model allows after every run, with lost `COMMIT`s, failures and calls taking effect late | `Db.invariant`, `Lanes/Db/Sound.lean`; gate `Tests/Axioms/Db.lean` | The start satisfies it; PostgreSQL behaves like the model | proved |
| A call that committed after retries answers what one run of its transaction answers on the state it committed against, and leaves that run's state | `Retry.loop_committed`; gate `Tests/Axioms/Db.lean` | Failed attempts were rolled back; the driver follows `Retry.next` (trusted) | proved |
| A transaction answered operation by operation with their meanings is its meaning | `Txn.interp_apply`; gate `Tests/Axioms/Db.lean` | The driver feeds each answer to the next step (trusted) | proved |
| A derived table reads a value back from its row, and a row that reads back is the row of what it read | `TableOf.ofRow_toRow` of the table `Columns.table` builds, `Columns.toRow_of_ofRow`; gate `Tests/Axioms/Db.lean` | None | proved |
| A value reads back from the text the driver sends it as | `Postgres.Sql.decode_param`, `Postgres.Sql.decodeRow_param`; gate `Tests/Axioms/Lib.lean` | Values of their columns' types | proved |
| PostgreSQL answers every operation of the subset as its meaning says, and behaves like the model at `SERIALIZABLE` | `Tests/Oracle/Service/Db.lean` against PostgreSQL 16: generated transactions one at a time, every answer compared with `Txn.run`, and three at once, checked with `Db.State.run`; nightly, recorded in `oracles/postgres/db.jsonl` and checked again by `lake test` | Every theorem proved against the model rests on it | trusted, tested against PostgreSQL 16 |
| The meaning, the SQL, the replies, the retry decision and the model's litmus runs | `Tests/Db.lean`, in `lake test` | | tested |
| A transaction each of whose operations writes a table only under keys of a set leaves every row of that table whose key is outside it as it was: what one user's requests cannot touch of another's | `Txn.All.others`, `Lanes/Db/Sound.lean`; gate `Tests/Axioms/Db.lean`; used by `Rookery.others_kept` | None | proved |
| At its start an application runs the migrations not yet run, each once even with instances started at once, and refuses to start when the tables it declares differ from the database's | `Postgres.Typed.prepare`, `Postgres.Typed.migrateOnce` (`lanes_migrations`, an advisory lock), `Postgres.Sql.tablesDiff`; `examples/counter/Check.lean` and `examples/rookery/Rookery/Live.lean` on PostgreSQL | The IO is trusted (`TRUSTED.md`) | tested against PostgreSQL 16, when `LANES_POSTGRES` is set |
| SQL migrations leave exactly the tables, columns, types, nullability and primary keys the schema declares | `Tests/Oracle/Service/Db.lean`: `Tests/Fixtures/migrations/` against PostgreSQL 16 in a schema of their own, compared by `Postgres.Sql.catalogDiff`, and a column left out of the schema found; `examples/todo-db` `todoLive` | Indexes are not compared | tested against PostgreSQL 16, nightly |

### Limits

- A call takes effect at one moment between its request and its reply, an order that follows
  real time. PostgreSQL's `SERIALIZABLE` promises a serial order only; that it also follows real
  time for transactions that do not overlap is tested on the recorded runs, not documented.
- No SQL arithmetic, `LIKE`, floats, JSON, joins or engine-assigned ids: that logic is in Lean.
  Key and index columns are never `NULL`.
- A lost `COMMIT` is not in the recorded runs of the typed store; the key-value store's runs
  record one at the protocol.

## Jobs, the outbox and acting once

Work that must outlive the process is a row (`docs/decisions/D114-outbox-jobs.md`). A jobs table
(`Lanes/Db/Jobs.lean`) holds jobs, each with its work, the time it is due, a key its requester
chose (unique: a second `enqueue` under it is a no-op), its attempts and its lease. The outbox is
a jobs table whose jobs are effects (an HTTP call, an email, a payment, an object to put),
written in the transaction that causes them, due at once. A schedule is a job that runs again
`every_ms` after each success. Each decision is a pure function of a job (`Config.claimed`,
`Config.finished`); the transactions (`enqueue`, `claim`, `finish`, `cancel`) only read and
write rows.

The worker (`Lanes/Db/Worker.lean`) is an actor whose step is pure. At each tick it claims the
jobs due, which leases each for one more attempt; it hands each to the job's adapter as an
attempt under the job's id as the idempotency key (`Worker.runPort`); it records the answer with
`finish`, which counts only for the current lease. A claim, an attempt or a `finish` lost, or a
restart, leaves the job leased: it is due again when the lease runs out. So a job is attempted
until it is done, refused for good or out of attempts, and the key makes a repeat take no
effect. `Lanes/Services/Postgres/IO/Worker.lean` runs it on PostgreSQL and only performs;
`Lanes/Web/IO/Jobs.lean` makes an attempt an HTTP call with the key in a header.

Acting once is an idempotency key stored in the transaction (`Lanes/Db/Once.lean`):
`Keys.once key body` runs `body` and stores the key with its answer; a later run under the key
runs nothing and answers the same. The key is the table's primary key, so two runs at once
conflict, and the one retried finds the key.

Where: `Lanes/Db/{Jobs,JobsSound,Worker,WorkerSound,Once,OnceSound}.lean`,
`Lanes/Services/Postgres/IO/Worker.lean`, `Lanes/Web/IO/Jobs.lean`; `examples/reminders`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| No effect is sent for a transaction that did not commit: every attempt the worker hands over is of a job, with its work, in every database the store's model may hold, once any call outstanding or lost takes effect too | `Worker.committed_only`, `Lanes/Db/WorkerSound.lean`; gate `Tests/Axioms/Db.lean`; `Tests/Worker.lean` checks it beside the models, with a crash, a restart and lost answers | The application's transactions keep the table (`Queue.Keeps`: they add jobs and leave those there alone), as `enqueue` does (`Queue.enqueue_keeps`); every environment model, crashes and process restarts included (`Outside.Beside.restart`); PostgreSQL behaves like the model | proved |
| With a receiver that honours idempotency keys, each job takes effect at most once, however often it is attempted | `Worker.once_each`, from `Idempotent.keys_nodup`; gate `Tests/Axioms/Db.lean` | The receiver behaves as `Idempotent.server`; the adapter sends the job's id as the key (trusted) | proved |
| A claim answers jobs of the table, at most its limit and `batch_max`; each for one more attempt of a job whose attempts were not spent | `Queue.claimed_has`, `Queue.claim_length`, `Queue.claim_attempts`, `Lanes/Db/JobsSound.lean`; gate `Tests/Axioms/Db.lean` | None | proved |
| Every job due is taken: a claim whose scan finds no more jobs due than its limit leases every one whose attempts are not spent, and answers it for an attempt; the worker hands every job of a committed claim to its adapter in the step that reads it | `Queue.claim_takes`, `Worker.stored_runs`; gate `Tests/Axioms/Db.lean` | That this happens in every fair run is not one theorem: the store's model may fail every call | proved, per transaction and per step |
| At most one job per key, and only the current attempt's answer counts | `Queue.one_per_key`, `Queue.finish_stale`, from `Op.unique_apply`; gate `Tests/Axioms/Db.lean` | The application's operations on a table of the jobs table's name are on that table | proved |
| Acting once: a run under a key that committed makes every later run under it, of any body, a no-op that answers the same | `Keys.once_again`, `Lanes/Db/OnceSound.lean`; gate `Tests/Axioms/Db.lean` | None | proved |
| Behind a service that honours keys, every effect the service may have had is under the key of a job, and of its work, in every database the store may hold | `Worker.slots_held`; gate `Tests/Axioms/Db.lean` | As for `Worker.committed_only` | proved |
| An application's transaction that only adds jobs (`Queue.Adds`) keeps the table, is on it, and keeps any property of each job it adds that no claim or finish changes | `Queue.keeps_of_adds`, `Queue.onTable_of_adds`, `Queue.fixed_of_adds`, `Queue.handler_fixed`, `Queue.enqueue_adds`; gate `Tests/Axioms/Db.lean` | None | proved |
| A job done had an attempt the service took | `Tests/Worker.lean`: beside the store's model and an idempotent service, with crashes and lost answers | | checked |
| With one attempt per job (`attempts_max := 1`, no period), each job is attempted at most once, so a service that takes no key has each effect at most once | `Tests/Worker.lean`: beside the store's model and SES's, with a crash, a restart and lost answers; from `Jobs.Config.claimed` and `Queue.claim_attempts` | An attempt not answered leaves its job failed, the effect had or not | checked |
| The worker on PostgreSQL: three effects, one written twice under one key, one refused once; each attempt under its job's id, every job done | `Tests/Worker.lean`, when `LANES_POSTGRES` names a server | | tested against PostgreSQL 16, nightly |

### Limits

- A lease (`lease_ms`) must outlast an attempt (`attempt_ms`) on the worker's clock, or a job
  may be attempted twice at once; the key makes the second take no effect (`TRUSTED.md`).
- An attempt counts at its claim: a worker that dies between a claim and the attempt spends one.
- Ids are one more than the largest: a table whose newest rows are deleted gives their ids again,
  and with them their idempotency keys. Jobs that are over are kept.
- That a job is attempted until it is done or given up, in every fair run, is not proved as one
  theorem; its ingredients are (`Queue.claim_takes`, `Queue.claim_attempts`, `Worker.stored_runs`).

## Behaviours: servers and acting once

`Server.system spec` runs a service's spec as one actor. `Once.actor` acts once on a request its
client names by identity and sequence number, and answers a repeat with what it did, one entry
per client. Its memo lives as long as the process: across a restart, acting once is an
idempotency key stored in the transaction (`docs/decisions/D114-outbox-jobs.md`).

Where: `Lanes/Behaviours/Server.lean`, `Lanes/Behaviours/Once/`,
`Lanes/Semantics/{Service,Once}.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| `Server.system spec` implements its spec | `Server.implements`, `Lanes/Semantics/Service.lean`; gate `Tests/Axioms/Semantics.lean` | An environment that loses, duplicates, crashes and restarts nothing (`EnvModel.Faultless`) | proved |
| A server behind `Once.actor` implements `once` of its service in every environment, links duplicating included | `Once.server_implements`; gate `Tests/Axioms/Semantics.lean` | The memo is kept: no restart between a request and its repeat (`docs/decisions/D48-a-request-named-by-its-client.md`) | proved |

### Limits

- `Once.actor`'s memo is lost at a restart, as every actor's state is
  (`docs/decisions/D110-volatile-actors.md`).

## The checker

`Check.system` (`Lanes/Check/System.lean`) explores every interleaving of a small instance under
an environment model: every order of deliveries and timeouts, every input a driver may send,
every loss, duplicate and crash allowed. It runs the actors' own `step` through `SysState.step`,
so what is checked is the code that runs. The engine (`Lanes/Check/Search.lean`) is breadth-first
over exact states, so traces are shortest (D8, D33). `Service.monitored` and `Check.refines`
(`Lanes/Check/Monitor.lean`) check a system against a `Service` spec with no refinement mapping
(D42). `Check.fuzz` runs seeded random runs for instances too large to explore, with the
environment's faults, against `always` and `sometimes` properties, and reports the seed and the
trace of a failure; the
deterministic scheduler (`Lanes/Core/Scheduler.lean`, `Lanes/Core/FairScheduler.lean`)
replays any run.

What a result means is proved: the checker lists exactly the enabled events
(`SysState.mem_successors_iff`); a complete PASS means each `always` property holds in every
reachable world of the instance (`Check.search_sound`, `Check.system_sound_of_respects`, under
lawful `==` and `Model.Respects`: properties and a constraint that give one verdict on the worlds
the checker merges); a bounded pass is not a complete one: it prints `PASS (bounded)` and the
runner exits 2 (`Check.Report.verdict`); a reported violation is a real run (`Check.system_violated`); and a complete PASS of
a refinement check means every run's inputs and outputs are a trace of the spec
(`Check.refines_sound`, `Check.refines_traces`). Under D45 a PASS finds bugs; the claim rests on a
theorem.

Two other searches reach further (`docs/decisions/D92-checker-scale.md`). `Check.fingerprint`
(`Lanes/Check/Fingerprint.lean`) keeps a hash of each state instead of the state: what it reports
replays and is checked again (`Check.fingerprint_violated`, `Check.systemFingerprinted_violated`),
but a pass is not exhaustive, and the report says it was fingerprinted. `Check.systemReduced`
(`Lanes/Check/Reduce.lean`) searches the worlds through a representative of each: a complete pass
is a pass of `Check.system` when the representative is a `World.Reduction`
(`Check.systemReduced_sound`).

Where: `Lanes/Check/`, `Lanes/Semantics/Monitor.lean`, `Lanes/Semantics/MonitorSound.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A complete PASS of the checker means each `always` property holds in every reachable state of the instance | `Check.search_sound`, `Check.system_sound_of_respects`; gate `Tests/Axioms/Check.lean`; a bounded pass says `PASS (bounded)` and exits 2 (`Check.Report.verdict`, `Check.Report.ok_iff`) | `==` on actor states is equality and on the driver an equivalence, with a matching hash; the model respects `==` (`Model.Respects`, which `Check.model_respects` gives for `Check.system`): the driver respects its `==` (`Driver.Respects`), and the properties and the constraint give one verdict on worlds the checker merges (`World.Equiv`: the order of messages on a link that does not order them, and of pending outputs), so a property that reads such an order makes a PASS unsound; only the instance checked, within its bounds | proved |
| A reported violation is a real run | `Check.system_violated`; gate `Tests/Axioms/Check.lean` | None | proved |
| A violation, deadlock or witness the fingerprinted checker reports is real, though its pass is not exhaustive | `Check.fingerprint_violated`, `Check.fingerprint_deadlock`, `Check.fingerprint_witness`, `Check.systemFingerprinted_violated`, `Lanes/Check/FingerprintSound.lean`; gate `Tests/Axioms/Check.lean`; the report says "fingerprinted" (`Check.fingerprint_fingerprinted`) | None for what it reports; a pass covers only the states whose hash no other state seen had | proved; the pass not exhaustive |
| Computing successors in tasks changes nothing: the fingerprinted search in tasks stores the same states in the same order and gives the same report | `Fingerprint.Search.runParallel_eq`, `Check.fingerprint_tasks`; gate `Tests/Axioms/Check.lean`; compared as text by `lake exe lanesCheck` (`Tests/Election.lean`) | None | proved |
| A complete PASS of a reduced check is a PASS of the check, for invariants, refinement checks and deadlocks | `Check.search_reduce_sound`, `Check.search_reduce_deadlock_free`, `Check.search_reduce_unreached`, `Check.systemReduced_sound`, `Lanes/Check/ReduceSound.lean`; gate `Tests/Axioms/Check.lean`; applied to `Tests/Reduce.lean` in `Tests/ReduceProofs.lean` | The reduction is a `Model.Reduction` (or a `World.Reduction`, for instance a driver's state in a canonical form, `Check.World.Reduction.ofDriver`), and keeps equivalent worlds equivalent; the premises of `Check.system_sound_of_respects` | proved |
| States the checker merges have one hash, which tells apart orders of the messages on an ordered link | `Check.Node.trafficHash_eq`, `Lanes/Check/SystemSound.lean`; gate `Tests/Axioms/Check.lean` | None | proved |
| A complete PASS of a refinement check means every run's inputs and outputs are a trace of the spec | `Check.refines_sound`, `Check.refines_traces`, `Lanes/Semantics/MonitorSound.lean`; gate `Tests/Axioms/Semantics.lean` | `==` on the spec's state is equality; the instance only | proved |

Also:

- A fingerprinted mode, off by default (`Check.fingerprint`, `Check.systemFingerprinted`), keeps a 64-bit hash of each state seen instead of the state: about a third of the memory and two thirds of the time, a pass not exhaustive and said so (`Report.fingerprinted`), and every trace it reports replayed from its choices and checked again (`Check.fingerprint_violated`, `Check.systemFingerprinted_violated`); with `Options.tasks` its levels' successors are computed in tasks, the same function (`Fingerprint.Search.runParallel_eq`).
- Proved of the checker: it lists exactly the enabled events of a state, merging states is safe, a complete PASS means every `always` property holds in every world of the instance (`Check.system_sound_of_respects`; `==` must be equality on actor states, and on the driver's state an equivalence that the driver respects, `Driver.Respects`; the hash only decides how many states are stored; `Check.system_sound` is the case where it is equality), the spec monitor accepts exactly what the spec allows, deadlines included (`Check.Monitor.ok_iff`), a monitor never holds a candidate twice (in its type), so monitors compare and hash as sets and a monitored driver respects `==` (`Service.monitored_respects`), a complete PASS of a refinement check means the monitor has a candidate in every world (`Check.refines_sound`) and the inputs, outputs and deadlines passing of every run of the instance are a trace of the spec (`Check.refines_traces`; the spec's state must have `==` as equality), and a reported violation is a real run of the semantics (`Check.system_violated`).
- Reductions (`Model.reduce`, `Check.systemReduced`): a complete pass of a model reduced by a `Model.Reduction` is a pass of the model, for invariants, refinement checks and deadlocks (`Check.search_reduce_sound`, `Check.systemReduced_sound`, `Check.search_reduce_deadlock_free`), with a driver's state kept in a canonical form as the instance proved in general (`Check.World.Reduction.ofDriver`).
- Refinement to a `Service` without a mapping, with the spec's deadlines passing as the system's timers named for them fire, or as the messages named for them are delivered (`Service.monitored svc driver deadlines delivered`, which sees deliveries through `Driver.deliver`; `docs/decisions/D42-a-spec-names-its-inputs-and.md`, `docs/decisions/D56-a-deadline-passes-where-it-is-served.md`), and to `once` of one (`Service.onceMonitored`, not yet proved sound).
- Restarts are explored as crashes are: where the environment model allows them
  (`EnvModel.mayRestart`) and at most `Scenario.maxRestarts` times in a run, and a complete pass
  covers them (`Check.system_sound_of_respects`); `Tests/Restart.lean` finds a counter falling
  below a count the outside saw, after a restart.
- `Options.tasks` computes successors in tasks; the search is the same function with or without them (`Check.Search.explore_eq`), so the report does not depend on timing, but on four shared cores the tasks are slower and they are off by default.

## The proof layer

`Lanes/Semantics/` is the proof layer; nothing executable imports it (D11, rule 1.6).

- `System.sem` presents `SysState.step` as a labelled transition system, and `System.Refines` is weak
  simulation to a spec (`Lanes/Semantics/System.lean`, `Lanes/Semantics/Refinement.lean`,
  `Lanes/Semantics/Simulation.lean`).
- `Service.spec` turns a sequential `Service` into what a concurrent implementation must refine,
  with deadlines as visible steps, and `System.Implements` is refinement to it: linearizability,
  stated as refinement (`Lanes/Semantics/Service.lean`, D42); that this is the textbook definition is argued, not proved.
  What it gives is proved: every run of a system that implements a service has a sequential
  history of the service's acts that produces each output it hands over, takes each input
  after it arrives, and respects real-time order, with each deadline passing where the run
  shows it (`System.Implements.history`, `Lanes/Semantics/History.lean`), so what is proved of
  the service's functions holds of the system's outputs. A deadline passes in the system
  as a timer it names fires, or as a message it names is delivered
  (`docs/decisions/D56-a-deadline-passes-where-it-is-served.md`). `Server.implements` proves the
  `Server` behaviour (`Lanes/Behaviours/Server.lean`) implements its spec in an environment
  without faults.
- A request named by its client takes effect once (`Lanes/Semantics/Once.lean`, D48):
  `Service.once` is the spec, `Lanes/Behaviours/Once/Basic.lean` the memo that meets it, and
  `System.Refines.of_handles` the relation rule that a duplicated message cannot break. The
  key-value store implements it with no premise on its links
  (`KV.implements_once`, `examples/kv-cache`). `System.Refines.filterMapIO` carries a refinement through
  hiding outputs the spec allows at any time (`Spec.showing`).
- Liveness (`Lanes/Semantics/Liveness.lean`, D27): infinite runs (`System.Run`), weak fairness
  per obligation (`System.Run.Fair`), `System.LeadsTo` and its rule
  (`System.LeadsTo.ensures_of_invariant`). Every finite run extends to a fair one
  (`System.exists_fair_run_of_run`), and fair runs project through views and joins
  (`System.View.Projects`, `Lanes/Semantics/FairJoin.lean`).

Where: `Lanes/Semantics/`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A request named by its client takes effect at most once, under every fault but a process restart | `KV.implements_once` (`examples/kv-cache`); gate in its example | The memo (`Once.actor`) is in the system; the process does not restart, since a restart forgets the memo | proved |
| `System.Implements` is linearizability | Its definition: weak simulation to `Service.spec` (`Lanes/Semantics/Service.lean`, D42) |  | a definition; not proved equal to Herlihy and Wing's |
| A leads-to proved where the process never restarts holds where it may, from any position after which it does not restart | `System.LeadsTo.unlessRestart`, `Lanes/Semantics/Restart.lean`; gate `Tests/Axioms/Semantics.lean` | A fair run with no restart from the position of `P` on | proved |
| A system that implements a service has, for every run, a sequential history of the service that produces each output, takes each input after it arrives, and orders an output handed over before an input arrives before that input's effect | `System.Implements.history`, `System.Implements.produced`, `Lanes/Semantics/History.lean`; gate `Tests/Axioms/Semantics.lean` | `System.Implements` | proved |

Also:

- A fair run of `a.join b w`, seen from either side without the messages from outside in
  flight, is a fair run of that side alone (`System.Run.Fair.left`, `System.Run.Fair.right`;
  Composition, above).
- Fair runs and leads-to carry over to a system behind hidden inputs and outputs, when the output map is injective where it shows (`System.underView_projects`, `System.LeadsTo.filterMapIO`).
- Fair runs project: a view under which each step of one system is a finite run of another and the obligations match carries fair runs to fair runs and leads-to with them (`System.View.Projects.fair_run`, `leadsTo`).
- Liveness: infinite runs with stuttering (`System.Run`), weak fairness for each `Obligation` of the system on its own (deliveries, timers, starting an actor that has mail, outputs; never the environment's events), where a timer is obliged to fire only if it stays pending and no step arms it again, as in the runtime (`Obligation.Restarted`; a watchdog that is pinged forever never barks in a fair run, `examples/watchdog/Watchdog/Proofs.lean`), `System.LeadsTo` with its proof rule (`LeadsTo.ensures_of_invariant`), transitivity and monotonicity.
- The standard simulation of a service behind actors (`Account`: inputs pending and outputs owed on messages, in states and in a witness, the value as a relation), with which an application proves only what each step of an actor does to it (`Account.Handles`, `Account.implements`), and with deadlines what a step that passes one does (`Account.HandlesFire`, `Account.implements_timed`), each case knowing where its message came from (`System.Sent`, `System.Armed`: every message in flight is an input or one some step sends, every timer one some step arms, `System.traced`, for every system), the messages on one link in order (`linkMsgs`) with what sending, delivering the oldest, losing and a crash do to them, and refinement case by event with only the losses the environment has (`System.Refines.of_timed_events`, `of_events`; `docs/decisions/D52-standard-simulation.md`).
- What one side emits and the wiring routes to the other, which neither view shows, is handled by the other side, on a link that loses nothing, by an actor the environment does not crash and that never stops (`System.Run.Fair.routed_right`, `routed_left`, `handled_right`, `handled_left`).
- `Service.spec`, over inputs and outputs (`Service In Out S T`, written before the actors), with deadlines `T` that pass as visible steps, and `System.Implements sys env svc deadlines delivered`, refinement with the system's timers that `deadlines` names firing them and the deliveries that `delivered` names passing them where a message is served (`docs/decisions/D42-a-spec-names-its-inputs-and.md`, `docs/decisions/D56-a-deadline-passes-where-it-is-served.md`; how long a deadline lasts is not modelled).
- `Spec`, `Refines` (weak simulation with a label map), `of_map`, `trans`, trace inclusion.

### Limits

- Liveness theorems are about fair runs of the semantics. That the runtime's runs are fair is not proved, and "eventually" carries no bound.
- No liveness holds across a process restart: a restart loses what was owed. A leads-to holds only from a position after which the process does not restart (`System.LeadsTo.unlessRestart`), and nothing obliges a run to stop restarting.

## Data and the standard library

What every layer uses is in `Lanes/Data/`: `Enum`, `lanes_data`, and the queue. A type has three
mappings out of the process, each derived by `lanes_data` from its declaration with its laws
(`docs/decisions/D115-serialization.md`): JSON for HTTP (`deriving ToJson, FromJson`, through
`Lanes/Lib/Encoding/Json/Derive.lean`), rows for the typed store (a `table` line, through
`Lanes/Db/Columns.lean`), and CBOR, the standard binary encoding, for messages, files and caches
(`deriving ToCbor, FromCbor`, through `Lanes/Lib/Encoding/Cbor/Derive.lean`;
`docs/decisions/D118-cbor.md`). JSON and CBOR are built by the same code from the same pieces
(`Lanes/Lib/Encoding/Fields.lean`), so a type's CBOR has the shape of its JSON. CBOR is not in
`import Lanes`: a program imports `Lanes.Lib.Encoding.Cbor` to build and link it.
The standard library is in `Lanes/Lib/`: encodings, addresses and URLs, time, media types,
metrics, rate limits, the PostgreSQL protocol (below) and cryptography, with the C it binds
(Bound C). All of it is total and `Std`-only. A parser or encoder is proved against its
RFC and compared with a reference implementation on generated inputs, and every difference is
decided (rule 5.9, D50, `docs/decisions/D80-oracles.md`); `oracles/README.md` names the oracle
of each module, and `lake exe lanesOracle` asks them.

Where: `Lanes/Data/`, `Lanes/Lib/`, `Lanes/Lib/Net/Percent.lean`, `native/`, `oracles/`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A type `lanes_data` derives JSON for reads back what it writes, and is never `null` | `LawfulJson` and `NonNullJson`, from the laws of `Json.Fields` and `Json.Alts`, which each piece carries (`Json.Fields.readObject_object`, `Json.Codec.ofAlts`); gate `Tests/Axioms/Lib.lean` | None | proved (by construction) |
| The shapes of derived JSON: a structure an object of its fields, `null` fields left out; a constructor its name, or an object of its name holding its arguments; what Lean's own derived encoders write reads | `Tests/Derive.lean`, in `lake test` | | tested |
| The CBOR decoder reads back what the encoder writes, for every value within its limits, in any mode | `Cbor.decode_encode`, `Lanes/Lib/Encoding/Cbor/Sound.lean`; gate `Tests/Axioms/Lib.lean` | None | proved |
| The deterministic encoding is canonical: values equal but for the order of their maps' entries have the same bytes; the deterministic decoder takes each such encoding, and a strict decoder takes one encoding of each value | `Cbor.encodeDeterministic_eq_of_equiv`, `Cbor.decode_encodeDeterministic`, `Cbor.eq_of_decode_strict`; gate `Tests/Axioms/Lib.lean` | None | proved |
| The CBOR decoder refuses an input over its size, and what it reads is within its depth and length | `Cbor.decode_tooLarge`, `Cbor.size_of_decode`, `Cbor.fits_of_decode`; gate `Tests/Axioms/Lib.lean` | None | proved |
| A type `lanes_data` derives CBOR for reads back what it writes, and is never `null` | `LawfulCbor` and `NonNullCbor`, from the laws of `Lanes.Fields` and `Lanes.Alts` (`Cbor.Fields.readObject_object`, `Cbor.Codec.ofAlts`); gate `Tests/Axioms/Lib.lean` | None | proved (by construction) |
| CBOR reads and writes as RFC 8949 and cbor2 do: Appendix A written and read, Appendix F refused, a type's CBOR in its JSON's shape | `Tests/Cbor.lean`, in `lake test`; `oracles/cbor2`, replayed in `lake test` | That cbor2 reads RFC 8949 rightly | tested |

Also:

- Base64 (RFC 4648, each byte string with exactly one spelling: `Base64.decode_eq_some_iff`), compared with Go's standard library on generated cases (`lake exe lanesOracle`).
- CBOR (RFC 8949: the preferred and the deterministic encodings, a decoder with limits and three modes of strictness, `ToCbor`/`FromCbor` with bignums), compared with Python's cbor2 on generated cases.
- CSV (RFC 4180 with a delimiter, a quote and LF or CRLF of one's choice; a reader fed in pieces, with limits), read back as written for every table of fields within the limits (`Csv.parse_write`), compared with Go's standard library on generated cases. Its own root: `import Lanes.Lib.Encoding.Csv`.
- Civil dates with day numbers and POSIX seconds (`Civil.ofDays_toDays`, `Civil.toDays_ofDays`).
- IP addresses and CIDR prefixes (RFC 4291 text forms, RFC 5952 output, `Ip.parse_print`, `Ip.Prefix.parse_print`, `Ip.Prefix.contains_iff`), compared with Go's standard library on generated cases.
- JSON (parser, printers, `ToJson`/`FromJson`; the parser accepts exactly RFC 8259's grammar within its limits, `Json.parse_iff`, and reads back what the printers write, `Json.parse_compress`; JSONTestSuite passes).
- Media types (RFC 9110 §8.3.1, `MediaType.parse_format`, case-insensitive by `MediaType.parse_format_eq`), compared with Go's standard library on generated cases.
- Metrics in the Prometheus text format, whose histograms' buckets count the observations at or below their bounds (`Metrics.Histogram.observeAll_eq`) and whose label values and help text a reader reads back as written (`Metrics.readLabelValue_escapeLabel`, `Metrics.readHelp_escapeHelp`), tested against text checked by hand and against Prometheus's `expfmt`, which parses what it writes.
- Paths of names separated by `/`: Go's `path.Clean`, idempotent (`Path.clean_clean`), and `path.Join`; `Path.under`, the file a request names below a root, refusing a `..` that would climb out of it, whose result is the root followed by names that are none of `.`, `..` or empty (`Path.under_names`); glob patterns as Go's `path.Match`, with `**` as a whole name matching across `/` (`Lanes/Lib/Glob.lean`, run as an automaton, no backtracking). Compared with Go's standard library on generated cases. Their own roots: `import Lanes.Lib.Path`, `import Lanes.Lib.Glob`.
- RFC 3339 and HTTP dates (`TimeFormat.parseRfc3339_print`, `TimeFormat.parseHttpDate_print`), compared with Go's standard library on generated cases.
- SHA-256, HMAC-SHA-256, the comparison of byte strings, and Argon2id from OpenSSL's libcrypto (`Native`, bound from `native/lanes.c`), random bytes from its `RAND_bytes` (`Lanes.randomBytes`), with SHA-256, HMAC-SHA-256 and the comparison also in pure Lean as references, both tested against the NIST and RFC 4231 vectors and compared on thousands of random inputs (`Bytes.same_iff`, `Bytes.unhex?_hex` proved).
- The token bucket of x/time/rate with exact arithmetic (`RateLimit.allowed_le`: at most `burst + rate · w` in a window of `w`; `RateLimit.allow_after_reserve`), compared with Go's on generated cases.
- URI references (RFC 3986: `Url.parse_print`, resolution as §5.2 with §5.4's examples evaluated and no dot segment left, `Url.dotFree_resolve`, idempotent normalization, `Url.normalize_normalize`), compared with Go's standard library on generated cases.
- Structured logs (`Lanes/Lib/Log.lean`): a record of a time, a level, a message, attributes and a request id, rendered as one line of JSON in the field order of Go's `slog`, with no control character whatever it holds (`Log.render_oneLine`) and read back by the JSON parser as the record (`Log.parse_render`); a `Log.Logger` writes records at or above its level to standard error or a function (`Lanes/Runtime/IO/Log.lean`). The runtime's own faults and the server's access log are written through it. The logger and what it renders with are in the lowest package (`docs/decisions/D120-stdlib-wave-1.md`).
- `multipart/form-data` (RFC 7578, RFC 2046 §5.1): `Multipart.parse` within limits on the body's size, the parts and each part's header lines, refusing what is over them (`Multipart.parse_tooLarge`, `Multipart.length_le_of_parse`, `Multipart.headers_le_of_parse`), and `Multipart.write`, read back by `parse` for parts that are `valid` and `clear` of the delimiter (`Multipart.parse_write`); a field's name and a file's name read back (`Multipart.name?_field`, `Multipart.filename?_file`). Compared with Go's `mime/multipart` on generated and edited bodies, where Go is laxer (`oracles/README.md`). `Request.form` reads a multipart body's text fields and `Request.file?` its files; `Loopback.postParts` posts one in a test.
- DEFLATE, gzip and zlib's format (RFC 1951, 1952, 1950) in pure Lean (`Lanes/Lib/Compress/`): `Inflate` decodes every block type, bounded by its `max`, which no output passes (`Inflate.size_le`, `Gzip.size_le`, `Zlib.size_le`), and is compared with Go's on streams our encoder writes, on dynamic blocks with codes made at random, and on those edited; `Deflate` writes the fixed code with matches, or stored blocks. CRC-32 is compared with its bitwise definition. The server compresses responses with gzip for clients that take it when `ServerConfig.compression` is set, and the client asks for gzip and decodes gzip and `deflate` within `maxResponseBytes` (`Lanes/Web/Http/Compress.lean`, tested over a socket in `Tests/Compress.lean`).
- `lanes_data` (a structure or an inductive type declared once, deriving JSON, a table, `Enum` and a field-by-field `LawfulBEq` from the declaration's text, without linking `Lean`).

### Limits

- A recursive type has no derived JSON or CBOR: a codec is a value, and `lanes_data` cannot define one that refers to itself.
- A CBOR value holds no float width (the data model has none): the encoder writes the shortest that holds the value. The decoder does not refuse a map with a key twice, nor check what a tag holds, and reads one item, not a sequence.
- A table's columns are 64-bit: `Int` and `Nat` have no column, since a value that does not fit would not read back.
- `Path.under` reads text, not the file system: a symbolic link below the root can lead outside it.
- IPv6 zones (`fe80::1%eth0`) are refused, also in URLs, and a leap second (`23:59:60`) is not a time.
- `Deflate` has no code of its own per block, so it compresses text less than zlib does; that `Inflate` reads back what `Deflate` writes is tested and compared with Go, not proved.
- A multipart body is read whole, as the server reads every body: a large upload is bounded by `ServerConfig.maxBodyBytes`, or streams in pieces (`ServerConfig.streams`) and is then not parsed as a form. Header lines of a part are read as RFC 5322 has them now: no folding, names that are tokens, values in UTF-8.
- The server compresses on the connection's thread and only whole responses, not streamed ones; it does not compress by default, since a compressed page that holds a secret and text an attacker chose leaks the secret through its size (BREACH).

## Bound C

What Lean cannot express or check is bound, as other languages bind it (D46): the file calls
`IO.FS` lacks, `fsync`, a write at an offset or at the end of a file that is there and a
truncation (the platform area above), and from
OpenSSL's libcrypto SHA-256, HMAC-SHA-256, constant-time comparison, Argon2id and random bytes
(`RAND_bytes`, as `Lanes.randomBytes`: `IO.getRandomBytes` makes no promise that its bytes are
fit for keys) (`native/lanes.c`, declared in `Lanes/Lib/Crypto/Native.lean` and `Lanes/Outside/IO/FileSystem.lean`). A bound
function with a Lean reference (`Sha256.reference`, `Hmac.reference`, `Bytes.sameReference`) has
that reference as its body, so its theorems (`Bytes.same_iff`) are about the reference, and what
is trusted is that the C computes the same, which `Tests/Crypto.lean` tests.

TLS is a client from OpenSSL, the copy Lean's toolchain ships and links into every executable
(`native/tls.c`, declared in `Lanes/Web/IO/Tls.lean`; `docs/decisions/D67-a-tls-client-from-the-openssl-lean-ships.md`).
It does no IO: the client hands it the bytes that arrive and sends those it gives back, so what
is sent and what the bytes mean stay the pure writer and reader. The certificate is always
verified, against the system's trust store or a file given, and so is the name or address it is
for. A response is ended only by the server's `close_notify`. That TLS is done right is trusted,
not proved: `Tests/Tls.lean` checks the refusals against `openssl s_server`.

Signatures under RSA and P-256 public keys are checked by the same OpenSSL's libcrypto
(`native/verify.c`, declared in `Lanes/Lib/Crypto/Verify.lean`), with SHA-256: the key's DER and an
ECDSA signature's are written in Lean, which also decides which keys are valid and what size a
signature has (`Lanes/Lib/Crypto/PublicKey.lean`), and RSA's check has a Lean reference,
`Rsa.verifyReference`, that `Tests/Signature.lean` compares with it beside RFC 7515's and RFC 7520's
vectors. Signatures are made by the same libcrypto with a private key read from PEM once and
kept by OpenSSL (`native/sign.c`, `Lanes/Lib/Crypto/Sign.lean`): RSASSA-PKCS1-v1_5, and ECDSA with
RFC 6979's nonce, so signing is a function and pure. Lean takes a key only if its public half,
read back from OpenSSL's DER (`PublicKey.ofSpki?_spki`), is valid; trusted, and tested against
RFC 6979's vectors, `openssl dgst -sign` and `cryptography` (`Tests/Sign.lean`, `oracles/botocore`).

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| A signature made with a private key is the one OpenSSL's command and Python's `cryptography` make, ECDSA's as RFC 6979 makes it | `Tests/Sign.lean`: RFC 6979 A.2.5's signatures with SHA-256, `openssl dgst -sign` with SHA-1 and SHA-256 under RFC 9500's RSA key, `openssl dgst -verify` for ECDSA; `cryptography` 50.0.2 through the CloudFront oracle (`oracles/botocore/cloudfront.jsonl`) | OpenSSL's PEM, RSA and ECDSA code; that `native/sign.c` declares OpenSSL's functions as the linked OpenSSL 4.1.0 does, checked only against the system's headers, 3.0 on Ubuntu 24.04 (`scripts/tls-declarations.py`) | trusted, tested |
| A key is signed with only if its public half, read back from OpenSSL's DER, is a valid RSA or P-256 key | `PublicKey.ofSpki?_spki`, `Lanes/Lib/Crypto/PublicKey.lean`; gate `Tests/Axioms/Lib.lean`; `SigningKey` holds the proof; keys of other kinds and sizes refused in `Tests/Sign.lean` | That `i2d_PUBKEY` gives the public half of the key that signs | proved of the reading; trusted, tested |
| Bound C computes what its Lean reference computes | `Tests/Crypto.lean` against the references and published vectors | That HMAC-SHA-256 is a pseudorandom function makes tokens unforgeable | trusted, tested |
| An HTTPS call reaches only a server whose certificate chains to the trust store and is for the name or address called, and a response framed by the end of the connection is taken only after the server's `close_notify` | `Tests/Tls.lean` against `openssl s_server`, and the mutants of `scripts/mutants.py` named `tls` and `https client` | OpenSSL's TLS and certificate code; the trust store, which `SSL_CERT_FILE` names when set; that `native/tls.c` declares OpenSSL's functions as the linked OpenSSL 4.1.0 does, checked only against the system's headers, 3.0 on Ubuntu 24.04 (`scripts/tls-declarations.py`) | trusted, tested |
| A signature checks under an RSA or P-256 key as the published vectors say, and RSA's check agrees with its Lean reference | `Tests/Signature.lean`: RFC 7515 A.2 and A.3, RFC 7520 §4.1, keys made by `openssl`, `Rsa.verifyReference` on every signature changed in a byte; the mutants named `signature` | OpenSSL's signature code; that `native/verify.c` declares OpenSSL's functions as the linked OpenSSL 4.1.0 does, checked only against the system's headers, 3.0 on Ubuntu 24.04 (`scripts/tls-declarations.py`) | trusted, tested |
| `Bytes.same a b` holds exactly when `a = b` | `Bytes.same_iff`, `Lanes/Lib/Crypto/Native.lean`; gate `Tests/Axioms/Lib.lean` | Of the Lean reference; that the C computes the same is tested | proved of the reference; the C trusted |

## The test kit

`Lanes.Testing` (`Lanes/Testing.lean`) is the test kit an application's tests run against: a
fake S3 that checks signatures, a fake identity provider, a scripted browser, a server of a
handler and readers of a response. `import Lanes.Testing` is for an application's tests and
not in `import Lanes`, so no binary that serves links it (`docs/decisions/D77-a-test-kit.md`).
`Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/OAuth.lean` and `Tests/TutorialWeb/` run against it.

Where: `Lanes/Testing/`.

### Claims

- A fake S3 on a local port that checks every signature as S3 would, presigned links' included, takes a browser's form only under its signed policy and refuses one over its size as S3 does (`EntityTooLarge`), takes multipart uploads with S3's part sizes, order and ETags, and keeps the objects.
- A scripted browser that keeps cookies by name and path and sends forms from its origin.

### Limits

- The fake S3 checks signatures with the functions the client signs with, so it agrees with the client by construction; that they are S3's is tested against AWS's vectors (`Tests/SigV4.lean`).
- Without the `openssl` command the fake provider issues no ID token.

## Tooling

The `lanes` command (`LanesCli/`) creates an application (`lanes new`, which writes
`templates/app/`, its types declared with `lanes_data`), checks the text of a project
(`lanes lint`, `LanesCli/Lint.lean`: the rules `AGENTS.md` lists, among them that every
repository path a doc cites exists), writes what is derived from other files (`--fix`,
`LanesCli/Generated.lean`: the line counts of `TRUSTED.md`, the index of decisions and
the numbers of new ones), runs the model checks (`lanes check`). Lint's rule `layering` keeps each module
of `Lanes/` from importing a package above its own: `LanesCli/Layers.lean` gives the packages of
`docs/decisions/D99-layered-packages.md`, what each requires, and each file's package by the
longest prefix of its path. CI (`.github/`) runs the build with warnings as errors, lint,
the tests, the model checks, the differential tests against the oracles, the examples and a
generated app on every pull request, and the build and tests on macOS; a pull request that
changes only documentation is built and linted only. Model checks run at small bounds on a pull
request.
The axiom gate (`Tests/Axioms.lean`) stops compiling when a `sorry` or a new axiom reaches a
headline theorem.

Where: `LanesCli/`, `Lanes/Core/ByCases.lean`, `.github/`, `infra/`, `scripts/`, `Tests/Axioms.lean`.

### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| The number of trusted lines, and each trusted file's size | Written by `lake exe lanes lint --fix`; lint `trusted-size` fails when a file differs |  | checked |
| Each known way of breaking trusted code fails a test | `scripts/mutants.py`, nightly (`.github/workflows/mutants.yml`) | A list of known mutants, not a measure of coverage | tested |
| No module of `Lanes/` imports a module of a package its own does not require | `LanesCli/Layers.lean`, `Cli.Lint.checkLayers`; lint `layering`; `Tests/Lint.lean`; a file in no package is reported too |  | checked |

Also:

- The mutation gate in parallel shards, nightly, by hand and on pull requests labelled `mutants`, on GitHub's runners or a warm EC2 machine the workflow starts and stops (`infra/README.md`).
- `instance_by_cases` for instances defined by cases on an identity (`Inspect` of a system whose actors differ).
- `lanes stats`: the totals no committed file holds, since each would change with every item (trusted lines, decisions).
- `scripts/lean-goals` for a file's errors and goals from a language server kept open.

## Applications

`examples/` holds the applications, each its own Lake package that requires Lanes as a user
would, in the order `examples/README.md` reads them: the counter `lanes new` writes
(`examples/counter`); the bank (`examples/bank`), also served over HTTP (`examples/bank-web`); a
key-value store with front ends, whose read cache breaks refinement (`examples/kv-cache`,
`KV.implements`, `KV.caching_not_implements`); a watchdog
(`examples/watchdog`); a shop that charges each order at most once through a model of a payment
service from an outbox (`examples/payments`, `Shop.charged_at_most_once`); a to-do list kept in PostgreSQL
(`examples/todo-db`); `examples/sign-in`, members of a video site signed in with Google or
GitHub, with sessions; uploads that stream (`examples/upload`); reminders in a jobs table
(`examples/reminders`); a chat room over WebSockets (`examples/chat`);
and `examples/rookery`, a small social network for bots kept in PostgreSQL, whose claims are
proved per transaction and so of every database the store's model allows (`Rookery.others_kept`,
`Rookery.bounded_always`). The tests import none of them; the systems of `examples/kv-cache` and
`examples/watchdog` are copied into `Tests/Fixtures/`, and
`Tests/Copies.lean` fails when a copy differs from its example. Each application
below has its claims, their evidence and premises, and its limits.

### Counter

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Counter (what `lanes new` writes): the count never passes its limit, in every database the store may hold | `Counter.within_always`, from `Counter.preserves` and `Db.invariant`, `examples/counter/Counter/Proofs.lean` | PostgreSQL at `SERIALIZABLE` behaves like the store's model | proved, no axiom gate |
| Counter: two instances started at once run the migrations once and both start; it refuses to start when the database's tables differ from the declared ones; a restart keeps the count | `examples/counter/Check.lean` on PostgreSQL, when `LANES_POSTGRES` names one | | tested |

### Bank

Where: `examples/bank/Bank.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Under lossy links the checker finds the credit the bank loses | `examples/bank/Check.lean` ("lossy links"), run by `lake test`; the trace in `README.md` reproduced on 2026-11-27 | None | checked |
| Bank: no balance is ever negative | `Bank.balance_nonneg`, `examples/bank/Bank.lean`; gate `examples/bank/Bank/Proofs/Axioms.lean` | None | proved |
| Bank: money is conserved, for any number of accounts | `Bank.money_conserved`, `Bank.money_conserved_restarts`, `examples/bank/Bank/Proofs.lean`; same gate | An environment that loses, duplicates and crashes nothing; the process may restart (back to the opening balances) | proved |

Also:

- Checked: a lost-credit bug found under lossy links.
- Checked: conservation on 2 accounts.
- Checked: runs on the runtime and over HTTP.

### Key-value store

Where: `examples/kv-cache/KV.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Key-value store: implements the map spec; with a read cache it does not | `KV.implements`, `KV.caching_not_implements`, `examples/kv-cache/KV/Proofs.lean`; gate `examples/kv-cache/KV/Proofs/Axioms.lean` | `KV.implements`: links that do not duplicate, and no process restart | proved |

Also:

- Checked: a stale-read bug of a read cache found, with one front end already.
- Checked: refines the map spec on one key, two values and two front ends, also with links that lose and reorder messages and a crash; a duplicating link breaks it, whichever of the three it uses.
- Checked: with the store behind `Once.actor` (`onceSystem`) it refines `once` of the map spec with every link duplicating, and with every link losing, reordering and duplicating and a crash.
- Proved: with caching it does not implement the map spec, in any environment, for any instance
  with a key, a value and a front end: the checker's run replays in every one (by the standard
  simulation `Lanes.Account`).
- Proved: without caching it implements the map spec for all keys, values and front ends in every environment whose links do not duplicate and where the process does not restart.

### Watchdog

Where: `examples/watchdog/Watchdog.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Watchdog: a fair run in which the dog never barks; an impatient run barks | `Watchdog.exists_fair_run_never_barks`, `Watchdog.impatient_barks`; gate `examples/watchdog/Watchdog/Proofs/Axioms.lean` | None | proved |

Also:

- Checked: under the fair scheduler a dog whose keeper keeps pinging never barks, and one whose keeper rests barks.
- Proved: there is a fair run in which the keeper pings forever, the dog's timer is pending at every position and the dog never barks.

### Payments

A shop whose orders are rows: placing one, under the customer's idempotency key (`Keys.once`), adds the order and its charge to an outbox under `charge-<order>`; the worker charges it through the payment model under the job's id; a webhook's transaction marks the order paid or declined.

Where: `examples/payments/Shop.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Payments: the service makes at most one payment for each order, in every run, under every fault the payment model allows, with retries, lost commits and process restarts | `Shop.charged_at_most_once`, from `Worker.slots_held`, `Queue.one_per_key`, `Idempotent.keys_nodup` and `Shop.shop_adds` (the shop only adds charges, each under its order's key), `examples/payments/Shop/Proofs.lean`; gate `examples/payments/Shop/Proofs/Axioms.lean` | The payment service behaves as `Payments.outside` (trusted, above); PostgreSQL behaves like the store's model; a payment counts from the moment it is asked for | proved |
| Payments: an order paid has a payment that succeeded, made for it | `examples/payments/Check.lean`, run by its `lake test`: one order, webhooks in any order, a restart | One order | checked |

### Reminders

Reminders over HTTP, each a job of a jobs table in PostgreSQL, posted by the worker to a notification service at its time and again until it is taken, refused, out of attempts or cancelled; a restart loses none and delivers none again that was taken.

Where: `examples/reminders/Reminders/App.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Reminders: every transaction keeps the table | `Reminders.keeps`, `examples/reminders/Reminders/Proofs.lean`; gate `examples/reminders/Reminders/Proofs/Axioms.lean` | None | proved |
| Reminders: a reminder is delivered only once every database the store may hold has it; at a service that honours keys, none takes effect twice | `Reminders.delivered_committed`, `Reminders.delivered_once`; same gate | Every environment model; PostgreSQL behaves like the model; the service as `Idempotent.server` | proved |
| Reminders: no more than `maxReminders` wait; a reminder sent was taken | `examples/reminders/Reminders/Check.lean`, run by its `lake test` | A reminder refused and sent on a retry; a cancel and a second reminder | checked |
| Reminders: a reminder refused twice is sent on its third attempt, under one key; one that waits is cancelled; after a restart on the same database the reminders are as they were and none is delivered again | `examples/reminders/Test.lean`, when `LANES_POSTGRES` names a server | A local notification service | tested against PostgreSQL 16, nightly |

Also:

- Tested: over HTTP, a reminder refused twice is sent on its third attempt under one key, one that waits is cancelled, and after a restart the list is empty.

#### Limits

- After a start the sweep runs at once, and a reminder due while the process was down is late.

### To-do list

Stores to-dos in PostgreSQL through the typed store: one pure transaction per request, a user's
to-dos unique by title with no constraint saying so.

Where: `examples/todo-db/TodoDb.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| To-do list: every transaction keeps a user's to-dos unique by title and to-dos unique by id, so every database the store model allows after every run does | `TodoDb.preserves`, `TodoDb.unique_always` (through `Db.invariant`), `examples/todo-db/TodoDb/Proofs.lean`; gate `examples/todo-db/TodoDb/Proofs/Axioms.lean` | PostgreSQL behaves like the typed store's model | proved |
| To-do list: adding without looking the title up, and retrying a lost answer, stores a title twice; the checked handler never does, with failures and lost answers | `examples/todo-db/Check.lean`, run by `lake test` in the example and by CI | One user, up to three requests, two attempts | checked |
| To-do list: the answers on a real PostgreSQL | `examples/todo-db/Live.lean` (`lake exe todoLive`) | A local server | tested against PostgreSQL 16, nightly |

### Uploads

Uploads of any size over HTTP, each handed to the system in pieces of 64 KiB through the gate and answered with its size and Adler-32 checksum.

Where: `examples/upload`, a package of its own.

#### Claims

Also:

- Checked: the service model-checked on pieces in any order, and driven through the whole front end with no socket on bodies framed by their length and in chunks.
- Checked: `curl -T` of 20 MB answered with zlib's checksum.
- Proved: no more uploads are under way than the bound (`Upload.system_uploads_le`).
- Proved: the piece an upload waits for is taken and the next goes on from it (`Upload.step_piece`), and pieces taken one after another leave the size and the checksum of their bytes together (`Upload.take_take`, `Upload.start_take`).
- Proved: the system implements its spec (`Upload.implements`, by `Server.implements`).

### Sign-in

The start of a video site: members sign in with Google or GitHub through Lanes' sign-in and get a session, signed out with a form token.

Where: `examples/sign-in/Videos.lean`.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Sign-in: the same person signing in again is the same member | `Videos.register_again`, `Videos.register_lookup`, `examples/sign-in/Videos.lean`; gate `examples/sign-in/Videos/Axioms.lean` | A member is the issuer and subject the sign-in verified | proved |

Also:

- Checked: what the bridge and the steps make of requests is tested without a socket.
- Proved: the sign-in's own guarantees are Lanes'.

### rookery

A small social network for bots and their owners as a web application with a JSON API: sign-up, log-in, sessions, API tokens, posts, follows, timelines, deletes and a rate limit. Its data is in PostgreSQL, each request one pure transaction behind a front that keeps nothing; its failed log-ins and sessions are rows (`Lanes/Web/Auth/Rows.lean`), its API memo `Keys.once`. Its README says which claims moved from proved to checked when it left its one actor, and its friction log.

Where: `examples/rookery`, a package of its own.

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Rookery: a request changes only the rows of the account it is made as, so only a post's author deletes it | `Rookery.others_kept`, from `Rookery.run_good` and `Txn.All.others`, `examples/rookery/Rookery/Proofs.lean`; gate `examples/rookery/Rookery/Proofs/Axioms.lean` | Of each transaction | proved |
| Rookery: no window holds more than `maxPerWindow` posts and no account more than `maxFailures` failed log-ins, in every database the store may hold | `Rookery.bounded_always`, from `Db.invariant`; same gate | PostgreSQL at `SERIALIZABLE` behaves like the store's model | proved |
| Rookery: a response names the account its request was made as, the only one a session or token is signed for; an API change sent again with its `seq` writes nothing while its key is stored | `Rookery.handler_name`, `Rookery.api_again`; same gate | | proved |
| Rookery: a deleted post is in no later read, a retried change is answered the same, a lock and the oldest session closed where due, the bounds on accounts, posts kept, follows and sessions | `examples/rookery/Check.lean`, beside the store's model, with lost answers and a restart | Small bounds | checked |
| Rookery: a request is made as the account its cookie or token verifies; no password, cookie or token reaches the system; passwords are checked against the stored PHC hash and stored again at a new cost; after SIGKILL and a restart everything is as it was | `examples/rookery/Check.lean` (`Bridge`), `examples/rookery/Rookery/Live.lean` on PostgreSQL (CI, through `scripts/with-postgres`) | HMAC is a pseudorandom function | tested |

### Every application

#### Claims

| Claim | Evidence | Premises | Status |
| --- | --- | --- | --- |
| Every request to an application is answered | Only the gate's: an admitted request is answered, at the latest with `504` |  | not proved for the applications' own logic |
