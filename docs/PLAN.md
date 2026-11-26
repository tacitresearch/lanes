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
| PASS and complete ⇒ the invariant holds in every reachable state of the instance | Proved (`Check.system_sound`): every `always` property holds in every world of `Scenario.Reachable`, which is `SysState.step` with the driver's inputs, the crash budget and the constraint. It assumes that `==` is equality on actor states and on the driver's state (`LawfulBEq`), and that the properties and the constraint do not depend on message order (`World.Equiv`; `eq_of_quiet` and `eq_of_perm` discharge this). Not covered: a driver whose `==` is not equality, which is every monitored driver, so a PASS of `Check.refines` |
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
is a real run (`Check.system_violated`). Open there: refinement checks under a monitored driver. Step 3 is done for
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

Not done from that review: `election_safety` speaks of leaders that coexist, not of a term
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

#### Snapshots (designed, not built)

A snapshot is the kernel written down: each cell (state, whether it is up, its timers with
their deadlines), the queue, the clock, the next token and whose turn it is. The agenda is not
saved; it is what `Kernel.WellFormed` says it is, the pending timers. Recovery restores the
snapshot and replays the journal written after it; the switch to a new snapshot is one rename.

It needs two codecs from the application, for an actor's state and for a message, each over
all actors at once (`Codec ((i : σ.Id) × sys.State i)`). Writing those by hand is the cost, and
is why a declaration macro that defines a type together with its codec comes first.

The theorem is not `restore (snapshot k) = k`: a hash map restored is not the same value. It is
that the two cannot be told apart: the same `abs`, timers, clock, token and turn, and that
kernels alike in those stay alike under every operation with the same events and outputs. The
second half is a lemma about the kernel worth having anyway.

Releasing idle actors is a different thing and waits for shards: a cell that is not in memory
has to be brought back before a batch that needs it, and the kernel cannot do IO.

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

Refinement as a precongruence (if `a` refines `A` then the join with `a` refines the join with
`A`) comes after, from the same projection.

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

### A.4 Time and liveness

Fairness as a property of runs (an event enabled forever is taken), so that "every request is
eventually answered" can be stated for the gate: it needs timers to fire, which the kernel's
fairness theorem provides at the level of steps.

## Decisions that are yours

- **One thread per shard** (section 1). This is the large one. I will start it after steps 1
  and 2, so there is time to say no.
- **`systems/` in this repository**, as separate packages, not separate repositories.
- **The Raft invariant set.** `kv-lean` on GitHub holds only a README. Without its source I
  will port from Veil's Raft model and Ongaro's `raft.tla`.

## What proofs will not cover

- Parser ambiguity and developer experience: compile-fail tests, not theorems.
- Liveness: needs fairness, which the semantics does not have yet. Deadlock-freedom of the
  kernel is a safety property and is checkable.
- The shell, `Std.Async`, `Std.Http`, the Lean runtime and compiler.
