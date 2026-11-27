# Architecture

What Lanes is made of, how a request goes through it, and where each piece is proved. The rules
are in `AGENTS.md`; what works and its limits in `docs/STATUS.md`; what is trusted, and why, in
`TRUSTED.md`; why each piece is the way it is in `docs/decisions/`. The status of every public
definition (proved, with its theorems; trusted; checked; tested; a spec; or none) is generated
from the built library in `docs/INVENTORY.md` (D47), and what has none is on
`docs/inventory-none.md`: that is where a claim is checked, and this page only names the
headline theorems. `import Lanes` gives the API; the soundness theorems named here are in
`Lanes.Proofs` (`Lanes/Proofs.lean`), which `Lanes.Semantics` imports. Those are gated in `Tests/Axioms/`, which stops compiling if a `sorry` or a
new axiom reaches them.

The idea in one line: all logic is pure step functions, the semantics is one executable function
over them, and the code that runs, the checker that explores and the proofs that cover are all
about that function. IO happens only in a few small shells, each of which performs what a pure,
proved function tells it to.

| Piece | Where | Proved by |
| --- | --- | --- |
| Actors and systems | `Lanes/Core/{Actor,System,World,Step,Run}.lean` | the definition everything else is about |
| Proof tools for systems | `Lanes/Proof/{Lift,Ghost,Monotone,Equiv,Deed}.lean` | `System.invariant_of_actor`, `Inductive.of_monotone`, `System.Invariant.of_ghost` |
| The kernel | `Lanes/Runtime/{Kernel,KernelSound,KernelTimers,Wave}.lean` | `Kernel.exec_reachable`, `Kernel.exec_outputs`, `Kernel.exec_wellFormed`, `Kernel.runWaves_eq` |
| The shell | `Lanes/Runtime/IO/Shell.lean`, `Lanes/Runtime/{Batch,Mailbox,MailboxSound,Pace}.lean` | `Batch.run_kernel`, `Batch.run_sound`, `Batch.run_spread`, `Mailbox.batch_since_take`; the shell itself is trusted |
| Journal, snapshots, disk | `Lanes/Durable/{Journal,Snapshot,Disk,Frame}.lean`, `Lanes/Durable/IO/Journal.lean` | `Journal.open?_cut`, `Journal.recover_kernel`, `Journal.resume_eq_recover`, `Journal.Disk.Holds.save_crash` |
| Migrations | `Lanes/Durable/{Migration,Upgrade}.lean` | `Migration.inv_exec`, `Journal.Upgrade.begin_crash`, `Journal.Upgrade.holds`, `Journal.Upgrade.inv_load` |
| Joins | `Lanes/Core/Join.lean`, `Lanes/Proof/{JoinSound,MapIOSound}.lean`, `Lanes/Semantics/FairJoin.lean` | `System.Reachable.left`, `SysState.run_left`, `System.Run.Fair.left` |
| Shards and the transport | `Lanes/Runtime/{Shard,ShardSound,ShardsSound}.lean`, `Lanes/Net/{Courier,CourierSound}.lean`, `Lanes/Net/IO/{Peers,Node}.lean` | `System.ShardsReachable.unsharded`, `Peers.Courier.written_sublist_sent` |
| The gate and the HTTP server | `Lanes/Web/Http/{Gate,Front,FrontSound,Waiting,Conn,ConnSound}.lean`, `Lanes/Semantics/Front.lean`, `Lanes/Web/IO/Server.lean` | `Http.served_answered_le_arrived`, `Http.served_pending_answered`, `Http.Waiting.exec_answered`, `Http.Conn.run_writes` |
| Metrics, health and the access log | `Lanes/Lib/Metrics.lean`, `Lanes/Web/Http/{Ops,OpsSound}.lean`, `Lanes/Web/IO/Ops.lean` | `Metrics.Histogram.observeAll_eq`, `Metrics.readLabelValue_escapeLabel`, `Http.Ops.route?_default`, `Http.Ops.answer_ready`, `Http.Ops.Access.parse_line`; that none of it reaches a system is trusted and tested |
| Other adapters | `Lanes/Outside/Basic.lean`, `Lanes/Outside/IO/Clock.lean`, `Lanes/Web/IO/Client.lean`, `Lanes/Web/Http/{Grammar,Wire,WireSound}.lean` | `Response.read_wire`, `Request.fields_framing`; conformance tests |
| Models of external services | `Lanes/Outside/{Rpc,Idempotent,Events,ObjectStore}.lean`, `Lanes/Outside/Effects/`, `Lanes/Proof/Outputs.lean` | `Idempotent.at_most_once`, `Rpc.answered_le_called`, `Events.deliveries_le`, `ObjectStore.read_sent`, `System.Emits.outputs`; that a real service conforms is trusted |
| Signature Version 4 and the S3 client | `Lanes/Web/Http/{SigV4,SigV4Sound}.lean`, `Lanes/Web/S3/{Basic,Xml}.lean`, `Lanes/Web/IO/S3.lean` | `SigV4.target_sign`, `SigV4.sortQuery_sorted`, `SigV4.canonicalHeaders_sorted`, `SigV4.encode_chunks`; signatures tested against AWS's vectors, the client against a fake S3; its IO trusted |
| PostgreSQL and the store model | `Lanes/Lib/Postgres/{Bytes,Message,MessageSound,Scram,Conn,ConnSound,Table}.lean`, `Lanes/Lib/Postgres/IO/Client.lean`, `Lanes/Outside/Store/{Basic,Sound}.lean` | `Backend.read_encode`, `Frontend.decode_encode`, `Conn.run_fifo`, `Conn.step_committed`, `Conn.step_query`, `Store.write_skew`, `Store.lost_commit_either`; the IO is trusted, and that the server behaves like the model is a premise |
| Jobs: work outside a step | `Lanes/Behaviours/Jobs/{Basic,Sound}.lean`, `Lanes/Semantics/Jobs.lean`, `Lanes/Behaviours/Jobs/IO/Pool.lean` | `Jobs.answered_le_handled`, `Jobs.retry_same`, `Jobs.submitted_answered`; the pool is trusted |
| Web | `Lanes/Web/Http/{Basic,Route,RouteSound,Cookie,CookieSound}.lean`, `Lanes/Web/Html/`, `Lanes/Web/Auth/` | `Html.lex_render`, `Html.safeUrl_scheme`, `Http.dispatch_link`, `Http.parseForm_encodeForm`, `Http.readSetCookie_header`, `Auth.verify_eq_some`, `Auth.checkForm_other` |
| The checker | `Lanes/Check/`, `Lanes/Semantics/{Monitor,MonitorSound}.lean` | `Check.search_sound`, `Check.system_sound_of_respects`, `Check.refines_traces` |
| The proof layer | `Lanes/Semantics/` | refinement, specs, fairness, leads-to |
| Data and the standard library | `Lanes/Data/`, `Lanes/Lib/` | codec laws, `Quorum.majority_inter`, `Bytes.same_iff`, `Json.parse_iff`, `Url.parse_print` |
| Sign-in with OAuth 2.0 and OpenID Connect | `Lanes/Web/Auth/{Jose,IdToken,OAuth}.lean`, `Lanes/Web/IO/SignIn.lean` | `OAuth.Pending.callback_ok`, `OAuth.Pending.accepted_le_issued`, `OAuth.IdToken.verify_accepted`, `Jose.verify_ok`, `OAuth.Keys.no_fetch_within`; the edge is trusted, tested end to end against a provider run in the test |
| Bound C | `native/lanes.c`, `Lanes/Lib/Crypto/Sodium.lean`; `native/verify.c`, `Lanes/Lib/Crypto/Verify.lean` | trusted; tested against the Lean references and published vectors |
| TLS client | `native/tls.c`, `Lanes/Web/IO/Tls.lean` | trusted; tested against `openssl s_server` |

## Actors and the semantics

An actor (`Lanes/Core/Actor.lean`) is `init`, `step` and `recover`: a pure, total function from
a state and one message to a new state and a list of effects. A `Signature` names a system's
actors, each with its own message type, and its inputs and outputs; an identity is a typed
reference, and identities may be infinite families, since every identity names an actor that
always exists and starts on its first message (D2). The effects are `send`, `emit` (an output),
`after` and `cancel` (timers named by their message) and `stop` (D3). A `System` adds the actors,
which actors boot, and `accept`, which actor an input goes to (D4).

The semantics is one function, `SysState.step` in `Lanes/Core/World.lean`: a state holds every
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

The kernel (`Lanes/Runtime/Kernel.lean`) is every runtime decision as pure functions over a hash
map of actors, a queue of messages and an agenda of timers: accept an input, deliver the oldest
message (starting its receiver if it is down), fire a due timer, say how long nothing will
happen. Time is data: the shell says what the clock reads. Whatever sequence of operations the
shell asks for, in any order and with any clock readings, the kernel stays in a state the
semantics reaches and the events it reports are a run reaching it (`Kernel.exec_reachable`),
and its outputs are exactly that run's (`Kernel.exec_outputs`). Its agenda holds exactly the
pending timers (`Kernel.exec_wellFormed`), it never sleeps past one, and neither due timers nor
queued messages starve the other (`Kernel.WellFormed.step_of_queued`, `step_of_due`).

The shell (`Lanes/Runtime/IO/Shell.lean`) is one thread per shard. Senders put commands in a
bounded inbox (`Lanes/Runtime/Mailbox.lean`, pure: who is refused, who waits, who is woken). The
shell takes everything that has arrived at once and calls `Batch.run` (`Lanes/Runtime/Batch.lean`),
a pure function that returns the kernel after the batch and a list of acts: append these journal
entries, hand over these outputs, save this image, answer this peek. The shell performs the acts
in order and decides nothing. Proved: the journal describes the kernel (`Batch.run_kernel`); an
output is handed over only after the entries that produce it are appended, and a save falls
only where every output is handed over (`Batch.run_sound`); a take returns exactly what went in
since the last, in order, and the inbox never holds more than its capacity
(`Mailbox.batch_since_take`, `Mailbox.Reachable.bounded`). Trusted: that the shell performs the
acts as given (`TRUSTED.md`, the first row).

Unless `Runtime.Config.parallel` is `off` or there is one worker, the inputs that arrive together
are one turn (`Journal.turnAll`), a group of at most `min batch snapshotEvery`, and its work is
done a wave at a time (`Lanes/Runtime/Wave.lean`): the steps of the actors with mail in the wave
are worked out on Lean's task pool, each actor's in the order of its messages, and the kernel then
does the wave as `runBatch` does, taking each step from that plan. Handling one actor's message
changes no other actor's state (`Kernel.frame_handle`), so the result is `runBatch`'s, value for
value, however the wave is spread over threads (`Kernel.runWaves_eq`), and the journal and
everything proved of the kernel are unchanged
(`docs/decisions/D64-actors-run-in-parallel.md`).

Steps cheaper than a few microseconds cost more to hand to another thread than they save, and
whether costlier ones gain depends on the cores free. With `parallel` `auto`, the default, the
shell times each batch and `Pace` (`Lanes/Runtime/Pace.lean`, pure) chooses from those times
whether the next runs on the shard's thread or on the pool: cheap work never goes to the pool,
costlier work goes the way that has been faster, and the other is measured again now and then.
A batch is the same whatever the choice (`Batch.run_spread`), so the timing and the choice are
trusted only for speed (`docs/decisions/new-adaptive-waves.md`).

## Journal, snapshots and the disk model

Durability is a journal of what the kernel was asked, not of actor states (D24): replaying it
through the same pure kernel gives the same state, so a restart is not a fault any proof has to
account for. Pure, in `Lanes/Durable/Journal.lean` and `Lanes/Durable/Frame.lean`: a file reads back
as the entries written (`Journal.open?_file`); a file cut at any byte opens and gives exactly the
entries wholly written before the cut, and anything else wrong with it is refused, not repaired
(`Journal.open?_cut`); recovery rebuilds exactly the kernel those entries lead to
(`Journal.recover_kernel`), and hands over again exactly what was produced after the last mark
(`Journal.recover_handed`).

A snapshot is the kernel's image (`Lanes/Durable/Snapshot.lean`), saved with codecs the
application gives for its actors; a shard that saves goes on with the restored kernel, so a
snapshot is a restart without the crash (D29). Starting from a snapshot gives what replaying the
whole history gives (`Journal.resume_eq_recover`).

What is written, in what order, and what a start makes of the files are pure functions over a
model of the two files (`Lanes/Durable/Disk.lean`: `Journal.Disk.start`, `Disk.mend`,
`appendWrites`, `saveWrites`), in which an append may stop at any byte and a rename is atomic. If
the process dies anywhere in an append or a save, the files load as the kernel the shard had
(`Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.save_crash`), and a start mends what a
death left (`Journal.Disk.Torn.mend`), so this holds over any number of starts, saves and deaths.
`Lanes/Durable/IO/Journal.lean` performs the writes, each synced with `fsync` before the next, so a loss
of power leaves what a death would; that the file system is the model is trusted.

The files carry a label, the application's name for the system and the version of its types
(`Journal.label`; version 0 is the name alone, as every journal was named before versions). A
deploy that changes a type keeps the old version's system and reads its files through an
upgrade (`docs/decisions/D66-a-migration-carries-the-kernel-across.md`,
`Lanes/Durable/Upgrade.lean`): the start replays them with the old codecs and step
functions, migrates the kernel (`Migration`, `Lanes/Durable/Migration.lean`), hands over the old
outputs not yet handed over, saves the result under the new label and begins the journal at
that mark, whose index is the old history's length. Dying anywhere in those writes, the next
start gives the same migrated kernel (`Journal.Upgrade.begin_crash`). `Disk.Holds` and
`Disk.Torn` take the kernel a history starts from, boot or a migrated kernel, and the files after
a migration are those of a running shard that started there (`Journal.Upgrade.holds`), so the
crash theorems go on. What the proofs of the new version still say is what is inductive: a
`Migration` carries an invariant of each new actor that its steps and restarts keep, and the
proof that every state an old actor reaches migrates into it; it then holds of every actor in
every state the new shard reaches (`Migration.inv_exec`, `Kernel.exec_inductive`) and at every
later start (`Journal.Upgrade.inv_load`). An invariant proved only from boot, and refinement,
do not carry over.

## Composition: joins, shards and the transport

`System.join a b wiring` (`Lanes/Core/Join.lean`) is two systems as one: an output of one that
the wiring routes to the other becomes a message to the actor its `accept` names. Every tool
applies to a join, because it is an ordinary `System` (D25). What is proved of `a` for every
environment holds of `a` inside any join: of states (`System.Reachable.left`,
`System.Invariant.join_left`), of runs (`SysState.run_left`) and of fair runs
(`System.Run.Fair.left`, `System.LeadsTo.join_left`, D41); for `b`, up to `SysState.Equiv`.
`System.filterMapIO` renames inputs and outputs and hides some; a system behind it does what it
does in the open (`SysState.run_filterMapIO`).

A shard is a system too (D28): `System.shard sys hosts` (`Lanes/Runtime/Shard.lean`) is `sys` as a
shard sees it, where a message to an actor hosted elsewhere leaves as a parcel and a parcel that
arrives is an input. It runs on the unchanged kernel and keeps the ordinary journal. Shards
joined behave as the one system, for two (`System.SplitReachable.merged`) and for any number
(`System.shards`, `System.ShardsReachable.unsharded`), under a condition on booting
(`System.SteadyBoot`), so the system's invariants hold of them (`System.Invariant.split`,
`System.Invariant.shards`).

Shards in different processes are joined by TCP, with a link that promises no more than
`Link.network` (D30). There is no router inside a process (D37); a machine's cores are used by
running a process per core. Every decision of the transport is the courier, `Peers.Courier.step`
(`Lanes/Net/Courier.lean`), a pure function proved for every limit and every sequence of
events (`Lanes/Net/CourierSound.lean`): one write at a time on a connection, writes only where
it dialed and only what it was sent, in order and at most once
(`Peers.Courier.written_sublist_sent`), a bounded queue, everything closed at `stop`
(`Peers.Courier.stop_closes`), and what it delivers is what its reader makes of the bytes
(`Peers.Courier.delivered_read`). `Lanes/Net/IO/Peers.lean` only performs. That the running
processes implement `System.shards` is trusted.

## The gate and the HTTP server

The HTTP server's logic is a system of its own, the gate (D19, D31, D43). `Gate.step`
(`Lanes/Web/Http/Gate.lean`) decodes each request into an input through the application's `Bridge`,
remembers which requests are waiting, arms a deadline for each, and answers with the system's
response or with `504` when the deadline fires. `Http.gateSystem` is the gate as one actor;
`Http.fronted sys` is the gate joined in front of `sys` (`Lanes/Web/Http/Front.lean`), and
`Http.served sys` is `fronted sys` with requests its only inputs and responses its only outputs,
which is what `Http.serve` runs.

Proved of `served sys` for every system, bridge and configuration: no request is answered more
often than it arrived where the link from outside to the gate does not duplicate
(`Http.served_answered_le_arrived`), a waiting request keeps its deadline armed
(`Http.served_deadlines_armed`), and in a fair run in which the gate does not crash every request
the gate admits is answered (`Http.served_pending_answered`). These come from the gate alone
(`Http.Gate.answered_le_handled`, `Http.Gate.pending_answered`) by projection through the join.
That an arrival reaches the gate is checked, not proved.

The server (`Lanes/Web/IO/Server.lean`) reads a request, prepares it with `Bridge.prepare` on the
request's own task, so a password or a cookie the bridge turns into what the system needs never
reaches the journal (D44), takes an id from `Http.Waiting` (pure: each id handed out once, each
answered at most once and to its own waiter: `Http.Waiting.exec_handed_nodup`,
`Http.Waiting.exec_answered`), and hands the input to the shard. It answers `503` itself when the
inbox is full and `405` for a method an application cannot handle. With `ServerConfig.ioThreads`
above zero (four by default), the connections run on that many threads of the server's own, each on one for its
whole life; Lean has one libuv loop a process, which every read and write still goes through. `Http.serveFronted` serves
`fronted sys`, whose other inputs and outputs pass the gate by, and `Http.serveShard`
(`Lanes/Net/IO/Node.lean`) runs it with the transport: one process with an HTTP front and peers.

The server tells its operators how it is, each part off by default (`ServerConfig.ops`,
`docs/decisions/D69-observability.md`): a metrics page in the Prometheus text format, liveness,
readiness, request ids and a JSON access log. What is decided is pure. `Lanes/Lib/Metrics.lean`
renders counters, gauges and histograms, whose buckets count the observations at or below their
bounds (`Metrics.Histogram.observeAll_eq`) and whose label values a reader reads back as written
(`Metrics.readLabelValue_escapeLabel`). `Lanes/Web/Http/Ops.lean` says which request is the
operators', none with nothing configured (`Http.Ops.route?_default`), that readiness answers
`200` exactly when the shard has recovered and the server is not stopping or draining
(`Http.Ops.answer_ready`), and what a log line holds, the JSON text of its record
(`Http.Ops.Access.parse_line`). `Lanes/Web/IO/Ops.lean` answers an operator's request before it
is prepared or has an id, so it never reaches the shard, and passes every other request on as it
came; it counts the journal's appends by wrapping its storage. So a run writes the same journal
with all of it on as off, which is trusted and tested (`Tests/Ops.lean`).

Around it, pure and in `Std` only: requests and responses as data; typed routes whose links the
server reads back and `dispatch` hands to their route's handler (`Http.dispatch_link`); forms
(`Http.parseForm_encodeForm`); HTML values that a browser reads as the tree they were rendered
from, so text stays text (`Html.lex_render`, against a model of the HTML tokenizer), with URL
attributes limited to `Html.allowedSchemes` (`Html.safeUrl_scheme`), and a template macro
(`Lanes/Web/Html/Syntax.lean`, trusted); htmx attributes taken from routes (`Hx.request_match?`);
cookies a browser stores with exactly the attributes they name (`Http.readSetCookie_header`,
against RFC 6265's algorithm); and `Lanes/Web/Auth/`: signed tokens and form tokens that accept
exactly what was signed for their purpose and session (`Auth.verify_eq_some`,
`Auth.checkForm_iff`) and another's only through an HMAC collision (`Auth.verify_sign_other`,
`Auth.checkForm_other`), Argon2id password digests, failed attempts that lock at their limit
(`Auth.Attempts.locked_unlock_repeat`) and sessions that keep the newest (`Auth.Sessions.ids_starts`).

Sign-in with another service (`docs/decisions/D72-sign-in-with-oauth.md`) is OAuth 2.0's authorization
code flow with PKCE and OpenID Connect on it, decided in `Lanes/Web/Auth/OAuth.lean` and done
where a request arrives, before the system (`serve`'s `arrive`, `Lanes/Web/IO/SignIn.lean`), so no
code or token is journalled. A callback is accepted only for a state issued to its browser and
provider and not expired (`OAuth.Pending.callback_ok`), and no state more often than it was issued
(`OAuth.Pending.accepted_le_issued`), which is also model-checked against an attacker's browser;
an ID token only if its header names RS256 or ES256, a key of the provider's set of that
algorithm and `kid` checks it, and every claim passes (`OAuth.IdToken.verify_accepted`,
`Lanes/Web/Auth/Jose.lean`). The system gets the identity in headers a client cannot send
(`OAuth.identity?_strip`). Vendors' presets are packages under `integrations/` (D61).

## Adapters

Whatever a system does not contain reaches it through outputs and inputs, never through an effect
that does IO (D26). An adapter is a model of the outside, an `Outside`
(`Lanes/Outside/Basic.lean`) that the checker explores the system against, and a handler that
performs; a conformance test records a real run and checks it with `Outside.allows`. Where an
adapter has something to decide, it is a pure function with its theorems (rule 3.9).

- **Clock** (`Lanes/Outside/IO/Clock.lean`): the time as an input, never earlier than one given before,
  also across a restart.
- **HTTP client** (`Lanes/Web/IO/Client.lean`): HTTP/1.1, or HTTPS through the TLS binding
  below, one request per connection; a `HEAD` is read without a body (`Response.readHead`). The bytes are pure (`Lanes/Web/Http/Wire.lean`): the request writer frames the message
  itself (`Request.fields_framing`), and the reader is proved to read a response written as a
  server writes it as soon as its last byte is there, to stay within its limit and to end
  (`Lanes/Web/Http/WireSound.lean`: `Response.read_wire`, `Response.read_more`; D39).
- **S3** (`Lanes/Web/IO/S3.lean`, `docs/decisions/D71-s3-and-signature-version-4.md`): put,
  get with a range, head, delete and ListObjectsV2 on a bucket, named virtual-hosted or by path
  at any endpoint (AWS, MinIO, LocalStack), and links a browser follows to get or put an object.
  Pure: each operation as a call signed with Signature Version 4 (`Lanes/Web/Http/SigV4.lean`),
  whose target is the canonical path and query that were signed (`SigV4.target_sign`), with the
  query and the signed headers in order (`SigV4.sortQuery_sorted`, `canonicalHeaders_sorted`);
  what an answer means (`S3.interpret`), and a reader of the XML S3 writes, which refuses a
  document type and every entity it does not know (`Lanes/Web/S3/Xml.lean`). The signatures are
  tested against AWS's test suite and S3's documented examples, the client against a fake S3
  that checks every signature from the bytes it receives. Bodies are whole, in memory.
- **Sign-in** (`Lanes/Web/IO/SignIn.lean`): the random values of a beginning, the pending
  sign-ins and each provider's keys held in references, and the calls to the token endpoint,
  the JWK Set and a user API; every decision is `Lanes/Web/Auth/OAuth.lean`'s (above).
- **HTTP server, journal, transport**: above.
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
  answered only with an object a put sent (`ObjectStore.read_sent`). `Effects` is the class of services that hold things with a lifecycle,
  made under a key and reported by webhooks, with two instances: payments, with the statuses
  Stripe documents for a PaymentIntent (`Lanes/Outside/Effects/Payments.lean`), and email
  (`Lanes/Outside/Effects/Email.lean`). A system's part of a proof is a fact about what its steps
  emit, lifted to every run by `System.Emits.outputs`; `examples/payments` proves a shop charges
  each order at most once that way (`Shop.charged_at_most_once`). That a real service does only
  what its model allows is trusted; the S3 client's runs against a fake are checked against the
  object store's, and no adapter talks to a real service yet.
- **PostgreSQL** (`Lanes/Lib/Postgres/`): the frontend/backend protocol 3.0 in Lean, not libpq
  (`docs/decisions/D68-postgres-protocol-in-lean.md`): start-up with trust, cleartext (only when
  allowed), MD5 or SCRAM-SHA-256; the extended query protocol with parameters, text both ways;
  errors; transactions; plain TCP. The messages are proved to read back as written
  (`Backend.read_encode`, `Frontend.decode_encode`) and tested against recorded sessions of
  `psql` and of this client. A connection is a pure `Postgres.Conn.step` (`Lanes/Lib/Postgres/Conn.lean`), as
  the HTTP server's is: replies answer requests in the order sent (`Conn.run_fifo`), a request is
  sent only to an open connection and is read by the server as sent (`Conn.step_query`,
  `Conn.valid_decode`), `committed` is answered only for a `COMMIT` the server committed from a
  transaction in progress (`Conn.step_committed`), the server is trusted after SCRAM only once
  it proved it knows the password (`Conn.onMessage_saslFinal`), and a connection that ends
  answers every request in flight `unknown` (`Conn.step_lost`); model-checked first
  (`Tests/PostgresConn.lean`). The IO (`Lanes/Lib/Postgres/IO/Client.lean`) only performs.
- **A transactional store** (`Lanes/Outside/Store/Basic.lean`): what a store may answer at read
  committed or serializable, as an `Outside` that keeps every database the answers are consistent
  with, so that a `COMMIT` whose answer is lost has both outcomes, and its effect may appear
  later. Its litmus runs are theorems (`Lanes/Outside/Store/Sound.lean`: `Store.write_skew`,
  `Store.lost_update`, `Store.lost_commit_either`, `Store.lost_commit_later`). A table of
  PostgreSQL runs it (`Lanes/Lib/Postgres/Table.lean`, `Postgres.Store.handler`); that the server
  behaves like the model at the level chosen is the premise of a theorem proved against it,
  tested on recorded runs (`Tests/PostgresLive.lean`). `examples/todo-db` is checked against it.
- **Jobs** (`Lanes/Behaviours/Jobs/Basic.lean`): work that must not run in a
  step, an outbound call or slow pure work, is submitted to the jobs actor under a key the
  requester chooses, beside the system that submits it (`Jobs.attach`). The actor dispatches
  each attempt as an output carrying the key, gives each a deadline, retries after a backoff,
  keeps at most `maxInFlight` jobs active and refuses beyond, and answers each key once; its
  pool (`Lanes/Behaviours/Jobs/IO/Pool.lean`) performs attempts on tasks of their own, as a pure function or
  an HTTP call with the key in `Idempotency-Key`, and hands results back as inputs. Proved: no
  key is answered more often than it is submitted, in every environment
  (`Jobs.answered_le_handled`); a retry carries its job's key and work (`Jobs.retry_same`);
  in a fair run without crashes every job is answered, whatever the workers do
  (`Jobs.submitted_answered`, by `System.LeadsTo.induction` on attempts left).

## The checker

`Check.system` (`Lanes/Check/System.lean`) explores every interleaving of a small instance under
an environment model: every order of deliveries and timeouts, every input a driver may send,
every loss, duplicate and crash allowed. It runs the actors' own `step` through `SysState.step`,
so what is checked is the code that runs. The engine (`Lanes/Check/Search.lean`) is breadth-first
over exact states, so traces are shortest (D8, D33). `Service.monitored` and `Check.refines`
(`Lanes/Check/Monitor.lean`) check a system against a `Service` spec with no refinement mapping
(D42). `Check.fuzz` runs seeded random runs for instances too large to explore, and the
deterministic scheduler (`Lanes/Core/Scheduler.lean`, `Lanes/Core/FairScheduler.lean`)
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
  stated as refinement (`Lanes/Semantics/Service.lean`, D42); that this is the textbook definition is argued, not proved. A deadline passes in the system
  as a timer it names fires, or as a message it names is delivered
  (`docs/decisions/D56-a-deadline-passes-where-it-is-served.md`). `Server.implements` proves the
  `Server` behaviour (`Lanes/Behaviours/Server.lean`) implements its spec in an environment
  without faults.
- A request named by its client takes effect once (`Lanes/Semantics/Once.lean`, D48):
  `Service.once` is the spec, `Lanes/Behaviours/Once/Basic.lean` the memo that meets it, and
  `System.Refines.of_handles` the relation rule that a duplicated message cannot break. The
  key-value store implements it with no premise on its links
  (`KV.implements_once`, `examples/kv-cache`), and so does Raft with the memo in its replicated machine
  (`RaftKV.implementsMachine_once`). `System.Refines.filterMapIO` carries a refinement through
  hiding outputs the spec allows at any time (`Spec.showing`).
- Liveness (`Lanes/Semantics/Liveness.lean`, D27): infinite runs (`System.Run`), weak fairness
  per obligation (`System.Run.Fair`), `System.LeadsTo` and its rule
  (`System.LeadsTo.ensures_of_invariant`). Every finite run extends to a fair one
  (`System.exists_fair_run_of_run`), and fair runs project through views and joins
  (`System.View.Projects`, `Lanes/Semantics/FairJoin.lean`).

## Bound C

What Lean cannot express or check is bound, as other languages bind it (D46): `fsync`, and from
libsodium SHA-256, HMAC-SHA-256, constant-time comparison, secure random bytes and Argon2id
(`native/lanes.c`, declared in `Lanes/Lib/Crypto/Sodium.lean` and `Lanes/Durable/IO/Journal.lean`). A bound
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
vectors.

## A request, end to end

One process running `Http.serve` on a journal:

1. `Lanes/Web/IO/Server.lean` reads the request from its socket and, on the request's own task,
   applies `arrive` if it was given one (which may answer it instead) and `Bridge.prepare`.
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

`examples/` holds the applications, each its own Lake package that requires Lanes as a user
would, in the order `examples/README.md` reads them: the counter `lanes new` writes
(`examples/counter`); the bank (`examples/bank`), also served over HTTP (`examples/bank-web`); a
key-value store with front ends, whose read cache breaks refinement (`examples/kv-cache`,
`KV.implements`, `KV.caching_not_implements`); leader election (`examples/election`); a watchdog
(`examples/watchdog`); a shop that charges each order at most once through a model of a payment
service (`examples/payments`, `Shop.charged_at_most_once`); `examples/raft-kv`, a replicated key-value store proved to implement the
map it replicates (`RaftKV.implementsMachine`), and `once` of it in every environment with the
memo in the map (`RaftKV.implementsMachine_once`); `examples/ledger`, a multi-user web ledger;
`examples/sign-in`, members of a video site signed in with Google or GitHub, with sessions;
and `examples/rookery`, a small social network for bots whose claims are proved of its spec,
which it is proved to implement with deadlines (`Rookery.implements`); the theorem that joins the
two is not written. Each claim, its evidence and its premises are in `docs/CLAIMS.md`. The tests use copies of
the small ones' systems, and the bank's two theorems, in `Tests/Fixtures/`, so an example can change for its reader alone. `lanes new`
(`LanesCli/New.lean`, `templates/app/`) creates an application; `lanes lint`
(`LanesCli/Lint.lean`) checks the rules of `AGENTS.md` that the text can show, the generated files
and the inventory (`LanesCli/Inventory.lean`).
