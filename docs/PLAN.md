# Plan: make the unproved part small

Written 2026-11-27, after a code review found ten defects in the first slice. Supersedes the
"Next, in order" list in `STATUS.md` until its steps are done.

## What went wrong

Nine of the ten defects were in code that nothing proves: the concurrent runtime (5), the web
layer (3) and the lint tool (1). The tenth was a docstring the code did not match. None was in
the proved core.

So the proofs did their job and covered too little. Eleven files, about 1,900 lines with their
docstrings, are IO or tooling that no theorem covers: the runtime, the HTTP adapter, the search
engine, the monitor, the scheduler, the template macro and the CLI. That is the number to drive
down.

**The rule from here on:** logic is a pure function with a spec and a theorem. IO code is a
loop that calls it. Anything that stays unproved is listed with its line count, and the count
is checked in CI.

## 1. Replace the runtime with a kernel that is the semantics

Today the runtime is 400 lines of concurrent IO: gates, a logical clock, an outbox, a restart
budget. All of it is decision logic, and all of it is trusted. The review found five bugs
there and I introduced a sixth while fixing them.

**New design.** A *shard* is a set of actors run by one thread.

- `Shard.step : Shard → Inbound → Shard × List Outbound` is a pure, total function. It holds
  every decision: routing, start and recovery, timers, stop and which mail a stopped actor
  loses, restart budgets, admission and back-pressure.
- The shell is one loop per shard: take from the inbox, call `Shard.step`, hand the outbound
  items to other shards and to adapters. Time enters as data.
- **Theorem:** every `Shard.step` is a sequence of `SysState.step` events. Proved once. After
  that a running shard cannot leave the semantics, by construction.
- Several shards are several systems joined by links, which the semantics already models. A
  composition theorem covers them.

This is the shared-nothing, thread-per-core design of Seastar and TigerBeetle, and it is what
the name Lanes describes. One shard is fully deterministic, so the production runtime and the
deterministic scheduler become the same code.

**Assuming the worst about `Std.Async`.** There is no formal semantics of it, and we do not
need one. The shell uses exactly one thing from it: a channel into each shard. So the whole
assumption is one line: *the inbox delivers each item once*. That assumption is written as an
`EnvModel` link, like the network in a Raft proof. To assume less, weaken the link (unordered,
duplicating) and prove under that. The model checker then explores every interleaving of
shard steps against the real `Shard.step`, so the runtime itself is model-checked.

**What this removes.** The per-actor tasks, the gate mutexes, the logical clock, the outbox
task, and the stress loop that took 20 minutes. What is left to trust is the shell, which I
estimate at under 100 lines; that is a target, not a measurement.

**Cost.** Actors in one shard do not run in parallel with each other. Parallelism comes from
more shards. For request/response services that is the right trade; it is also faster per
message, because the 50 µs task hop per `await` disappears.

Supervisors and restart policy become library actors with specs, as `DESIGN.md` asked. I
hard-coded them in the runtime, which was a mistake.

## 2. Prove the tools that say PASS

A wrong PASS from the checker is worse than no checker. These are pure functions, so they get
theorems, and their repeated tests go away:

| Claim | Status |
| --- | --- |
| Every state the checker explores is a real step | Proved |
| The checker lists every enabled event | Proved (`SysState.mem_successors_iff`) |
| States the checker merges enable the same events and step to states it merges | Proved (`SysState.Equiv.step`, `SysState.equiv_iff`) |
| PASS and complete ⇒ the invariant holds in every reachable state of the instance | Proved (`Check.system_sound_of_respects`): every `always` property holds in every world of `Scenario.Reachable`, which is `SysState.step` with the driver's inputs, the crash budget and the constraint. It assumes that `==` is equality on actor states (`LawfulBEq`); that `==` on the driver's state is an equivalence with a matching hash (`EquivBEq`, `LawfulHashable`) which the driver respects (`Driver.Respects`: `==` states offer the same inputs leading to `==` states, and stay `==` after an output); and that the properties and the constraint do not tell merged worlds apart (`World.Equiv`: message order no actor sees, and the driver's state up to `==`; `World.Equiv.congr` discharges this). `Check.system_sound` is the case where `==` on the driver's state is equality, which every driver respects (`eq_of_quiet` and `eq_of_perm` discharge the last assumption there) |
| PASS and complete of a refinement check ⇒ every run of the instance is a trace of the spec | Proved (`Check.refines_sound`, `Check.refines_traces`): under `svc.monitored driver` with `Check.refines` among the properties, the monitor has a candidate in every world of `Scenario.Reachable`, and for every run of the instance (`Scenario.Run`: the events, in order, that lead to a world) its inputs and outputs are a trace of `Service.spec`. It assumes the above of actor states, of the wrapped driver's state and of the properties and the constraint (`World.Equiv.holds_refines` for the refinement property itself), and that `==` on the spec's state is equality (`LawfulBEq`; `Enum.funLawfulBEq` for a function on a finite type). A monitor holds no candidate twice, which is part of its type (`Monitor.distinct`); that makes its `==`, equal length and inclusion one way, equality of the candidates as sets (`Monitor.beq_iff`, `Monitor.beq_iff_abs_eq`) and its hash agree with it, and so a monitored driver respects `==` when the driver it wraps does (`Service.monitored_respects`). Applied to the key-value store's check in `Tests/SystemSound.lean` |
| A reported trace is a real run ending in a violation | Proved (`Check.system_violated`: the trace's events are a run of `SysState.step` from the initial state to a state where the property is false) |
| `states ≤ maxStates` | Proved (`Check.search_states_le`) |
| The spec monitor accepts exactly the traces of `Service.spec` | Proved |

## 3. Testing: deterministic first, live last

| Tier | What | Speed | When |
| --- | --- | --- | --- |
| Build | Proofs, axiom gate, compile-fail tests for template misuse | seconds, cached | every edit |
| Fast | Pure tests: engine, examples on small instances, golden state counts | under 5 s | every edit |
| Check | Model checks of examples and of the shard kernel | under 1 min | every commit |
| Sim | Seeded simulation of the kernel with fault injection; a failure prints its seed | thousands of runs per second | every commit, long runs nightly |
| Live | Real threads, real sockets | seconds | every commit, few tests |

Other rules:

- Every example keeps a switch that seeds a known bug, and a test that the checker finds it.
- Every bug found later becomes a seeded-bug test or a theorem before it is fixed.
- A fresh agent reviews each chunk of work before it is called done. The one review so far
  found ten defects; it should be routine, not an event.
- Cross-check the checker's state counts against TLC on the models Veil ships counts for.

Today one binary holds everything and takes 12 s, of which 10 s is one model check. The split
alone makes the inner loop about 2 s.

## 4. Web layer

**Adapter as an actor.** The HTTP adapter keeps a table of waiting requests in a mutex. That
table becomes the state of an adapter actor, as `DESIGN.md` says every adapter should be. Then
"every accepted request gets exactly one response or a timeout" is an invariant the checker
and a proof can reach. The 503 and deadline bugs from the review were in that table.

**What templ has that Lanes lacks** (from memory of templ's documentation, not re-read):

- bare text children (Lanes needs `"quotes"`);
- a URL type and a raw-HTML escape hatch, both explicit;
- conditional class lists;
- fragments, so one template renders a page or a piece of it.

**htmx.** htmx 4.0 was released on 2026-08-28. It is built on `fetch`, has first-class SSE and
WebSocket extensions, makes attribute inheritance explicit and renames its events. It is not
the default install yet. Lanes should emit *intent* through a small typed vocabulary
(`Hx.post route`, `Hx.target id`) and render it for the htmx version in use, so views do not
hard-code attribute spellings that changed between 2 and 4.

**Typed routes.** One `Router` value produces both the request decoder and the links, so a
link to a route that does not exist fails to compile.

**Server push.** `Std.Http` can stream, so SSE works today. A session actor that pushes
fragments gives LiveView-style pages with all state on the server.

**Proofs.** `safeUrl` only returns allow-listed or relative URLs. Rendering then parsing a page
gives the page back, which is the precise statement that text never becomes markup.

## 5. Examples

Two kinds, kept apart:

- **`Examples/`**: small, one idea each, checked and proved, run in seconds in CI, quoted in
  the docs. Bank, key-value store, election stay here.
- **`systems/`**: serious applications, each its own Lake package with its own CI job and
  long nightly checks. They are the acceptance tests of the framework: a framework change
  that breaks one does not merge.
  1. `systems/raft-kv`: Raft-backed key-value store, the benchmark `DESIGN.md` names.
  2. `systems/ledger`: a full web application with sessions, persistence and a payment saga.
  3. `systems/gateway`: a rate-limited HTTP gateway.

## 6. Code style

The code has 12 inline comments and 515 docstrings: I required a docstring on every
declaration and every field, and most of them restate the name. That rule goes.

- A comment or docstring is allowed only for a *why* that a name, a type or a theorem cannot
  carry.
- A module keeps a short header saying what it is for. A public declaration gets a docstring
  only when its name and type do not already say what it is.
- `Lanes/Semantics/` is the exception: CSLib's linter requires a docstring on every
  declaration, and that code is meant to go upstream.
- Existing files get one pass to remove the rest.

## Order of work

Each step is its own commit on the branch.

Progress, 2026-11-27: step 1 is done. Step 2 is done for `always` properties: a complete PASS
of `Check.system` is a theorem (`Check.system_sound`). A reported violation
is a real run (`Check.system_violated`). A complete PASS of a refinement check under a monitored
driver is a theorem too (`Check.refines_sound`, `Check.refines_traces`). Step 3 is done for
one shard: the kernel is proved and the old runtime is deleted; several shards are open.
Step 4 is done: the gate actor replaces the adapter's logic. Step 5: typed routes with their
proofs, the htmx vocabulary, fragments, attribute splices and class lists are done; the render
and parse round trip is open. Step 6 has started: ghost histories, the monotone proof rule and
quorums exist, and election safety is proved for every cluster under every environment model.

A second independent review (2026-11-27) found eight defects, six of them in the 156-line
shell, and that no theorem constrained what the kernel tells the shell to do. All are fixed or
pinned by a test:

| Finding | Outcome |
| --- | --- |
| A message cost time linear in the number of actors | Fixed: the shard is a thread, not a task (D23); `Tests/Scale.lean` |
| `idle`, `state` and `input` hung or lost data after `stop` | Fixed: they fail; tested |
| An output handler calling back into the runtime deadlocks | Documented on `Runtime.start`; `tryInput` is safe |
| `batch := 0` never made progress | Fixed in the kernel's caller; tested |
| Cancelled timers kept sleeping and were waited for | Fixed: timers are kernel data (D23); tested |
| The gate loses a request if it crashes | Pinned: `Tests/Gate.lean` shows the precondition; one shard has no crashes |
| Reused request ids break exactly-once | Pinned by a test; the server's runtime is private, so only the adapter allocates ids |
| No theorem mentioned the kernel's commands | Fixed: there are no commands; `Kernel.exec_outputs` |
| Back-pressure, timer delay and `stop` were untested | Tested without depending on timing |

A third review (2026-11-27), of the rewritten runtime and the web layer, found six defects:

| Finding | Outcome |
| --- | --- |
| `Server.stop` with a request in flight panicked and the process could not exit | Fixed: waiters are released at stop and never awaited unsafely; tested over a socket |
| Due timers starved messages | Fixed: the kernel alternates between a due timer and the oldest message, with theorems (`step_of_queued`, `step_of_due`) and their two exceptions, which come from the semantics: a step may stop the receiver or cancel the timer |
| `stop` never ended a shard that always has work | Fixed: a closed inbox ends the loop; `stop` returns when the shard has ended; tested |
| `HEAD` and `OPTIONS` got the application's 404 | Fixed: `HEAD` is `GET` without the body, other methods get `405`; tested |
| A timer could fire early by the length of its batch | Documented on `Runtime.start`: nothing may depend on a timer not firing early |
| A link with an empty or dot segment did not round-trip and could name another host | Fixed: a `Path` carries a proof that its segments are clean; text segments are `Slug`s; tested through the real server |
| The shell's one duty, handing outputs on, was not tested | Tested: several outputs per batch and boot outputs compared exactly |
| `exec_reachable` was cited for a loop that calls `runBatch` | Fixed: `batch` is an operation the theorems cover |
| `Kernel.fire` could drop another timer's agenda entry | Fixed, found independently by the agenda proof |
| `system_sound` did not reach the gate check | Fixed: `Tests/SystemSound.lean` applies it |
| An htmx event name built from data could carry script | Fixed: names are filtered; tested |

A fourth review (2026-11-26), of phase A, could not break anything that is proved: sixty
SIGKILLs at random moments, four million entries, lost inputs, long timers, parser fuzzing.
Every defect it found was in trusted IO or in code that is tested and not proved, and three of
its mutants passed the whole test suite. The lesson is the one the first review taught, applied
one layer further out: a decision made in IO code is a decision nobody proved. What a journal
file means when it is opened was such a decision, and is a pure function now.

| Finding | Outcome |
| --- | --- |
| A journal opened with another codec, or with one flipped bit, was cut at the first unreadable entry and lost for good | Fixed: `Journal.open?` cuts only a write that did not finish and refuses everything else, with the theorem that a crash never causes a refusal (`open?_cut`); a header names the system; tested, and the file is byte for byte as it was |
| A second process could start on a journal the first was still writing | Fixed: the lock is a file beside the journal, taken before anything is read; the tail is cut in place, not by renaming; tested |
| When a journal write failed the shard died, the server kept running and callers hung | Fixed: the shard releases every caller, reports the error (`Runtime.ended`), and the server answers what is in flight and ends; tested on the runtime and over a socket |
| `serve` on a taken port left a shard running and the journal locked | Fixed and tested |
| The clock adapter left its model after a restart on a journal | Fixed: wall time that never goes back, started no earlier than the journal's last time; tested |
| `Outside.both` lost runs when both sides could send the same input | Fixed: the caller says whose each input is; a pair of models cannot guess |
| Outputs before the journal write, nothing handed over again after a restart, no lock, ids from zero: each mutant passed every test | Each now fails a test; `Journal.recover_handed` proves which outputs are handed over again, where the old theorem allowed none |
| `Journal.decode_torn` said "a prefix", which the empty list satisfies | Replaced by `open?_cut`, which says which prefix |
| HTTP client: leaked sockets on timeout, a keep-alive response read as a timeout, quadratic chunk parsing, header injection in the writer, a lenient response parser | Fixed. When a response is whole is a pure function (`Response.read`); the writer's framing is proved (`Request.fields_framing`, `head_plain`: one `Content-Length`, no `Transfer-Encoding`, no CR or LF in a line); the reader refuses what it does not understand, one test per case; live tests against a server that holds the connection fail on the mutants without a timeout and without a size limit |

Not fixed, and written down as limits: `Kernel.performAll` appends outputs one at a time, so a
step that emits tens of thousands of outputs is quadratic; a pending timer makes the shard
wait with a select and costs about 120 µs per input; a timer loses the time since the last
journal entry as well as the time the process was down; `System.join` leaves wired inputs open
to the outside until `mapIO` hides them; the gate is not yet built with `join`.

Not done from the third review: `election_safety` speaks of leaders that coexist, not of a term
having had two leaders at different times; a duplicate attribute from a splice renders twice;
`trusted-size` accepts only the exact wording `` `path`, N lines ``.

1. Comment rule in `AGENTS.md`; strip comments; split the test binaries.
2. Proofs of the checker and the monitor (section 2).
3. Shard kernel, its refinement theorem, simulation harness; port the conformance tests; delete
   the old runtime when the new one passes them (section 1).
4. HTTP adapter as an actor, with its invariant (section 4).
5. Web proofs and typed routes (section 4).
6. `systems/raft-kv`, starting with the quorum library and election safety.

## Phase A: settle the contracts

`ROADMAP.md` has the phases. This is phase A in the order it is being done, with the design of
each step written down before it is built.

### A.1 Durability: a journal, replayed (D24)

Pure and proved: `Journal.Entry` (input, clock reading, batch), its records, reading back a
whole or cut journal (`Journal.read_write`, `Journal.read_prefix`); byte framing with the
torn-write theorem (`Lanes/Data/Frame.lean`); the kernel theorems, which hold for any list of
requests and so for a replayed one.

Trusted: appending to the file and flushing before outputs leave; reading it at start.

Limits known in advance: Lean's `IO` has `flush` and no `fsync`, so a journal survives the death
of the process, not loss of power, until there is a sync primitive. No snapshots yet, so the
journal grows and replay takes time proportional to it. Outputs since the last "handed over"
mark are handed over again after a restart.

Done when: the bank, killed with `kill -9` in the middle of transfers and started again, has
the balances the journal says, and the test that does this is in CI.

**Done.** `Tests/Durable.lean` does exactly that. Next for durability: snapshots, releasing
idle actors, a sync primitive, and batching several inputs per flush.

#### Snapshots (built, D29)

A snapshot is the kernel written down: the cells, the queue, the agenda, the clock, the next
token and whose turn it is. Recovery restores it and replays the journal written after its
mark. The application gives three codecs: for an identity, for the state of each actor and for
the messages of each (`Kernel.Image.Codecs`).

The first design asked for a theorem that two kernels alike in everything observable stay
alike under every operation, because a hash map restored is not the same value as the one
saved. That theorem is not needed. Saving is a kernel operation, and a shard that saves goes on
with the restored kernel, so the shard that keeps running and a shard started from the
snapshot compute the same values. A snapshot is a restart without the crash, and the recovery
path is run every time one is taken, not only after a failure.

The order of the three steps of a save (mark the journal, put the snapshot in place, replace
the journal) is a pure function over a model of the two files, `Journal.saveWrites` in
`Lanes/Actors/Disk.lean`, with the theorem that every prefix of the steps, the first cut at any
byte, loads as the kernel the shard had or the one the save restores
(`Disk.Holds.save_crash`), and an invariant that a start, a turn and a save keep, so that it
holds however often the shard is started and killed. The adapter runs the list of writes.

Open: what is trusted is that the operating system's rename is atomic and that a flush survives
the process. There is no `fsync` in Lean's `IO`, so a save is not proved, or likely, to survive
loss of power: the model would need a write that is not yet on the disk. The invariant is
stated for a store with codecs for its actors. One without never saves, and has the theorem
for a journal cut at any byte (`Disk.load_cut`) and no invariant of its own. Releasing idle
actors is a different thing and waits: a cell that is not in memory has to be brought back
before a batch that needs it, and the kernel cannot do IO.

### A.2 Composition: join two systems, and what survives it

`System.join a b wiring` is one `System`, so every tool applies to it. Its actors are those of
both. An output of one that the wiring routes to the other becomes a message to the actor the
other's `accept` names; the rest are the composite's outputs. `System.mapIO` renames inputs and
outputs at the boundary. The gate in front of a system is the first instance.

The theorem is projection: every run of the composite, seen from `a`, is a run of `a` alone, in
which what `b` sent arrives as inputs and what `a` sent to `b` leaves as outputs. So whatever
is proved of `a` for every environment and every input holds of `a` inside any composite. That
is the form of compositionality the semantics already supports, because a system's theorems
already quantify over everything its environment may send.

The outside link of `a` alone has to be the most permissive one (unordered, lossy,
duplicating): messages from several actors of `b` share one link once projected, so their order
on it is not the composite's.

Proved, in `Lanes/Actors/JoinSound.lean`:

- `System.Reachable.left`: a reachable state of `a.join b w`, seen from `a` (`SysState.left`),
  is a reachable state of `a` alone under `EnvModel.left`. The links between actors of `a`,
  its crashes and its restarts are those of the join; the link from outside is `Link.network`.
- `System.Invariant.join_left` carries any invariant of `a` under that environment into the
  join, and `join_left_state` does the same in one line for a property of actor states proved
  for every environment. `Tests/Join.lean` has one at work.
- For `b`: `System.Reachable.right`, up to `SysState.Equiv` (the order of messages on different
  links, which no actor can observe), and exactly (`right_of_quiet_boot`) when the boot of `a`
  sends `b` nothing. `join_right` carries invariants that do not depend on that order,
  `join_right_state` those of actor states.

The two sides differ because `join` boots `a` first. What the boot of `a` sends `b` is in
flight before the first messages of `b` itself, and `b` alone receives inputs only once it has
booted, so alone it never has an input ahead of what its own boot sent. `Tests/Join.lean`
proves the exact statement false for two one-actor systems (`heralded_right_not_alone`). The
proof for `b` is the proof for `a` through `SysState.step_swap`: a
join and the join with its sides exchanged take the same steps.

What the permissive outside link costs. A theorem about `a` transfers only if it was proved
with inputs that may be lost, repeated and reordered. The gate's `answered_le_arrived` assumes
its link from outside does not duplicate, so it does not transfer to a gate whose arrivals come
from another system through a join. Projection cannot do better with one outside link: the
join loses and repeats per sender, and the senders are gone once projected. Giving a system
several outside links, one per wire, would let each keep the link model it has in the join.

Not covered: properties that relate the two systems ("every ask gets a result") are properties
of the join and are proved or checked there; projection only brings each side's own theorems
along.

Refinement as a precongruence (if `a` refines `A` then the join with `a` refines the join with
`A`) comes after, from the same projection and the same symmetry.

### A.3 The outside world: adapters with a model (D26)

**Done for the pattern and two adapters.** An `Outside` says what something outside may do; the
checker explores against it and a recorded run is tested against it. The HTTP server is tested
against `Http.outside` (ids are never reused) over a real socket, and the clock adapter
(`Lanes/Env/Clock.lean`) is the first outbound one: model, handler, a model-checked
application and a conformance test.

The HTTP client (`Lanes/Env/HttpClient.lean`, wire format in `Lanes/Http/Wire.lean`) is the
first adapter that does work for applications: HTTP/1.1 without TLS, one request per
connection.

Next: a database adapter; TLS; and proofs for the wire format (what is written is read back).

### A.4 Time and liveness (D27)

**Done for the theory and one theorem.** `Lanes/Semantics/Liveness.lean` has infinite runs
(`System.Run`: at each position an enabled event or a stutter), what a system owes
(`Obligation`: deliver to an actor that is up, fire an armed timer of an actor that is up,
start a stopped actor that has mail, hand over an output), fair runs (weakly fair to each
obligation on its own), `System.LeadsTo`, and its proof rule
(`System.LeadsTo.ensures_of_invariant`, Lamport's WF1) with transitivity and monotonicity.

Fairness agrees with the runtime about timers: a timer that stays pending and is not armed
again fires (`Obligation.Restarted`). An actor that keeps arming a timer again keeps it from
firing, in the runtime and in a fair run alike, and the semantics is unchanged. A leads-to proof
that rests on a timer shows that no step arms it again (the rule's premise `quiet`, filled in
for other obligations). `Examples/WatchdogProofs.lean` has the run this allows: a watchdog
whose keeper pings forever never barks, in a fair run.

`Lanes/Semantics/GateLive.lean` is the first use, for every system behind the gate and any
environment that does not crash the gate: a request waiting in the gate stops waiting
(`Http.pending_leaves`, by its deadline, which no step arms again:
`Http.deadline_not_restarted`), it stops waiting only in a step that emits its answer
(`Http.answered_of_leaves`), and the answer is handed over (`Http.pending_answered`).

`Lanes/Semantics/FairRuns.lean` proves that fair runs exist: every finite run extends to a fair
run (`System.exists_fair_run_of_run`), for every system and environment model, with no
assumption on the signature. So a leads-to theorem is about runs through every reachable state
(`System.Reachable.exists_fair_run`, `System.LeadsTo.reachable`). The run is that of
`FairScheduler`, which takes the event owed longest and counts a timer that is armed again as
owed from then.

Still open, roughly in the order it will be needed:

- **From arrival to admission.** That an arrival in flight reaches the gate needs fairness of
  delivery and a measure, the message's place on its link. With it, "every arrival is
  answered" for distinct ids. This is also the first leads-to chain.
- **A concrete application.** The gate's theorem says a request is answered, by the system or
  with `504`. That the bank answers a transfer with its result needs delivery through the
  application's actors, and a ranking rule (a well-founded measure that fair steps decrease).
- **Restart.** Nothing obliges starting a crashed actor that has no mail, so no liveness
  theorem yet survives a crash of the actor it is about. It needs supervision in the
  semantics, or restart as a stated assumption.
- **Strong fairness**, for an obligation that is due again and again without staying due, such
  as delivery to an actor that keeps crashing. Not needed so far.
- **Real time.** Fairness says a timer fires, not when, and says of a keep-alive only that it
  may stay quiet. That a follower does not time out while heartbeats arrive in time is a
  statement about delays, which neither the semantics nor a fair run has.
- **The runtime's runs are fair.** The kernel lets neither messages nor due timers starve the
  other (`Kernel.WellFormed.step_of_queued`, `step_of_due`). That its runs are fair runs of
  the semantics, given a clock that advances, is not stated.
- **Checking.** The checker has no lasso search, so a leads-to property cannot be checked
  before it is proved. `Tests/Gate.lean` checks the four premises of the rule instead.

## Phase B: scale

### B.1 Shards are a composition, not a new kernel

A shard runs an ordinary system on the ordinary kernel and runtime. `System.shard sys hosts` is
`sys` seen from one shard: the actors it hosts are themselves, except that a message to an
actor hosted elsewhere leaves as an output carrying the envelope, and an envelope arriving from
elsewhere is an input. An actor the shard does not host only forwards, so a misrouted message
is passed on and never handled twice. Nothing in the kernel changes, and each shard's journal
is the journal it already has, with envelopes among its inputs (so messages need a codec).

A cluster is one runtime per shard plus a router that carries each envelope output to the
inbox of the shard that hosts its receiver. Envelopes between shards travel on a lane of their
own that is never full, so two shards cannot block each other; back-pressure stays at the
outside inbox.

The theorem to prove is about kernels, where order is kept: the state of all shards together,
with the envelopes in flight between them, stands for a state of `sys`, and every step of any
shard or of the router is a run of `sys` under reliable ordered links, up to the reordering of
unrelated messages that the checker's state merging already allows (`SysState.Equiv`).

Durable clusters come after: each shard numbers what it sends to each other shard, and after a
restart a shard is sent again what the receiver's journal does not have.

**Done so far:** `System.shard`, the cluster and its router, tested (D28). And the theorem at
the level of the semantics, for two shards (`Lanes/Actors/ShardSound.lean`): `System.split sys
hosts` is the two shards joined with every parcel of one an input of the other, and in a run
where each input from outside goes to the shard that hosts its receiver, every state, read as
one state (`SysState.merged`), is a state of `sys` up to `SysState.Equiv`
(`System.SplitReachable.merged`). One event of the split is one event of `sys`, and the copies
that only forward never run. Invariants of `sys` hold of the split (`System.Invariant.split`),
those proved for every environment with no condition on booting (`split_of_forall`,
`split_state`).

What the proof found: the statement needs an assumption on booting (`System.SteadyBoot`),
because shards boot one after another and a boot actor that stops as it starts loses whatever
was already sent to it; and it is exact only up to the order of equal outputs of different
shards. Both have counterexamples in `Tests/Split.lean`.

**Open:**

- *N shards.* A split in two can be split again, but `System.split (System.split sys h) h'` is
  a system over a larger signature, not over `sys`; the N-shard statement needs either an
  N-ary join or the theorem restated for a shard of a split.
- *The kernel-level statement.* That one runtime per shard and the router implement the join:
  the states of the kernels together, with the parcels in the router's lanes, stand for a state
  of `System.split`, and every step of a shard or of the router is a run of it. The theorem
  above then gives the run of `sys`. Each shard's kernel is already proved to follow
  `System.shard`; what is missing is the router as a pure function and its refinement.
- A journal for clusters, and a measurement of what the threads buy on an idle machine.

### B.2 Node to node

The same `System.shard` with a router that speaks over a socket is a system spread over
machines. The link is then lossy and unordered, which is `EnvModel.distributed`: what holds
there is what was proved for every environment, such as election safety.

Built (D30): `Lanes.Peers` joins shards in different processes by TCP and promises no more
than `Link.network`. The bank runs on three shards joined that way. Open: running a system
with an HTTP front on each process, which needs the gate as a system of its own, joined to the
shard by the general operator, so that parcels pass it by.

### B.3 Snapshots, then checker v2

Snapshots are built (A.1 above, D29). Checker v2 is open.

## Decisions that are yours

- **One thread per shard** (section 1). This is the large one. I will start it after steps 1
  and 2, so there is time to say no.
- **`systems/` in this repository**, as separate packages, not separate repositories.
- **The Raft invariant set.** `kv-lean` on GitHub holds only a README. Without its source I
  will port from Veil's Raft model and Ongaro's `raft.tla`.

## What proofs will not cover

- Parser ambiguity and developer experience: compile-fail tests, not theorems.
- Liveness of the running program: the proof layer has fair runs and leads-to (A.4), and
  that the runtime's runs are fair is assumed. Deadlock-freedom of the kernel is a safety
  property and is checkable.
- The shell, `Std.Async`, `Std.Http`, the Lean runtime and compiler.

## Phase C: `systems/raft-kv`

Started before phase B is finished, because it is what says which parts of B matter.

Done: the protocol as one actor, generic over the machine it replicates
(`systems/raft-kv/RaftKV/Protocol.lean`); the spec, which is the machine; the invariants of
Raft's safety argument as checkable functions; model checks on three nodes against the spec
and the invariants, with witnesses; one seeded bug found.

What it has shown about the framework so far:

- The spec and the refinement check needed nothing new: the service monitor that checked the
  key-value store with front ends checks Raft.
- The checker's speed is the limit. One crash on three nodes in one term is six million
  states and takes ten minutes; two terms with a crash is out of reach. Checker v2 is what
  phase C needs first from phase B.
- A state of the node cannot derive `DecidableEq` when the replicated machine's state is a
  function, so its `BEq` is written by hand, and the lawfulness the checker's theorem asks for
  will have to be proved by hand too. `Inspect` should derive both.
- A heartbeat makes the state space infinite unless the messages in flight are bounded by a
  constraint. A checker option that bounds the net would say so in one place.

Next: the proofs, starting with election safety carried over from the election example, then
log matching; the seeded old-term commit bug found by the checker; the node-to-node transport,
so that three processes run it.

