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
| The checker lists every enabled event (`candidates` is complete) | To prove |
| State equality used for deduplication is a bisimulation | To prove |
| PASS and complete ⇒ the invariant holds in every reachable state of the instance | To prove |
| A reported trace is a real run ending in a violation | To prove |
| `states ≤ maxStates` | To prove |
| The spec monitor accepts exactly the traces of `Service.spec` | To prove |

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

Progress, 2026-11-27: step 1 is done except the comment pass, which is in review. From step 2,
checker completeness is proved; search correctness and the monitor are open. Step 3 is done for
one shard: the kernel is proved and the old runtime is deleted. Several shards and the seeded
simulation harness are open.

1. Comment rule in `AGENTS.md`; strip comments; split the test binaries.
2. Proofs of the checker and the monitor (section 2).
3. Shard kernel, its refinement theorem, simulation harness; port the conformance tests; delete
   the old runtime when the new one passes them (section 1).
4. HTTP adapter as an actor, with its invariant (section 4).
5. Web proofs and typed routes (section 4).
6. `systems/raft-kv`, starting with the quorum library and election safety.

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
