# Roadmap

The direction, the work in progress, the phases and the risks. `docs/STATUS.md` says what
exists. Review this file whenever a phase ends: is this still the right direction, and is there
a better design than the one written here? The reviews held so far are in
`docs/history/roadmap-reviews.md`; the plan of the first slice and the findings of the five
review rounds, with what each fixed, are in `docs/history/plan-review-rounds.md`.

## Direction

Decided 2026-11-26 (`docs/decisions/D45-everything-is-proved.md`). Lanes is for software an agent
writes and nobody reads line by line, so its claim has to rest on proofs, not on checks, tests or
review. The order of work:

1. **Proving an application becomes cheap enough to be routine.** A simulation-relation library
   from what the key-value store's proof repeated, a cheaper invariant rule, then a
   counterexample-to-induction finder. The ledger's refinement, proved, is the measure; the
   flagship application is proved, not checked.
2. **A generated proof inventory** gives every public definition a status, and library code has
   none without one. Built (`docs/INVENTORY.md`, D47); `docs/inventory-none.md` lists what still
   has none, and only shrinks.
3. **A standard library on the scale applications need**, triaged from Go's (`docs/STDLIB.md`):
   what Lean already has; what is pure, built here and proved, and tested against Go's
   implementation on generated inputs; what touches the operating system or cryptography and is
   bound (D46); what is not needed.
4. **Trusted and assumed things keep shrinking**: exactly-once requests in place of the premise
   that links from clients do not duplicate, idle actors saved to storage when they rest. The
   server reads requests with its own reader (`Lanes/Web/Http/ReadRequest.lean`, D49); `fsync`
   and cryptography bound to OpenSSL are done (D46); exactly-once requests are in for the
   key-value store (D48); actors back where a start puts them are released
   (`docs/decisions/D51-release-actors-at-rest.md`).
5. **Specs are what a person reviews.** Each system's spec and its premises sit in one place, and
   a person reads them before any public claim.

Launch work (the flagship application, deployment, the write-up) follows 1 to 4, because a launch
claim is what a critic tests first.

## In progress

What is being worked on now, and why. When a step is done, take it off and put its result in
`docs/status/`.

1. **Proving an application is cheap** (direction 1). Done towards it: a request named by its
   client takes effect once (`Service.once`, D48), `System.Refines.of_handles`, a relation rule
   that a duplicated message cannot break, and deadlines that pass where a message is served,
   with which the ledger's timed refinement is proved (`Account.implements_timed`,
   `Ledger.implements_timed`). Left: the relation library, a cheaper invariant rule, a
   counterexample-to-induction finder.
2. **Evidence for every definition of `Lanes/`** (direction 2). Take entries off
   `docs/inventory-none.md` by proving, testing or listing them in `TRUSTED.md`.
3. **The standard library** (direction 3). Of its P0 in `docs/STDLIB.md`, all is built but a
   table of rate-limit buckets per key.
4. **Less trusted, fewer premises** (direction 4). The premise that a client's link does not
   duplicate taken off the gate and Raft, as D48 took it off the key-value store; idle actors
   not at their start saved when they rest and read back when mail comes, which waits for a
   place to keep their state.
5. **Slow work that is not one request's**, as the ledger's friction log asks
   (`examples/ledger/README.md`). The jobs actor (`Lanes/Behaviours/Jobs/Basic.lean`) and the
   scheduler (`Lanes/Behaviours/Schedule/`) are in. Left: the answer carried to its requester
   through the join, at most once there, as the gate's is; ending sessions in bulk and
   statements in the ledger.
6. **Models of external systems.** Classes of external system are models under
   `Lanes/Outside/`, built from combinators on `Outside`, and vendors are packages under
   `integrations/` whose conformance to a class is a premise tested against the real service or
   a reference (D61, D65, D81; the service oracles of `oracles/`). Left: runs recorded from the
   real services, not only from references.
7. **A first app that deploys as it is made.** A `lanes new` app passes the stack's health
   check and is told its origin (`docs/DEPLOY.md`); the deploy path has not run on AWS yet.
   Left: run it once and record the run; signing forms and links with the instance role's
   credentials, which the bridge, being pure, cannot fetch, so that the tutorial and
   `examples/videos` need no long-lived key.

## Phases

| Phase | What | Done when | State |
| --- | --- | --- | --- |
| A. Settle the contracts | Durability; a composition operator with its theorem; adapters with a model of the outside; fairness, so liveness can be stated; codecs for inputs | The bank survives `kill -9` with recovery covered by a theorem; the gate is rebuilt with the general operator; one real adapter passes conformance against its model | Done: the journal (D24) and its crash theorems, `System.join` (D25) with the gate joined in front (D31, D43), `Outside` and conformance tests for the server, the clock and the client (D26), fair runs and leads-to (D27), `lanes_data` (D38) |
| B. Scale | Several shards; node-to-node transport; checker v2; snapshots | A Raft-sized model check finishes in minutes; a shard restarts from a snapshot in time that does not grow with its history | Shards proved for any number (D28), the transport with its courier proved (D30), snapshots (D29), the checker 3.5 times faster (D33): Raft's largest check, 7.8 million states, takes minutes. Open: checker v2 (states as flat data, symmetry, parallel search, a lasso search), and a proof that the running processes implement `System.shards` |
| C. Acceptance test | `examples/raft-kv` | Linearizability proved against the map spec; runs on three machines; survives fault injection | Met but for three machines: proved to implement the map it replicates (`RaftKV.implementsMachine`), run as three processes on one machine through `kill -9` and pauses. Frozen as a regression suite. Not done: liveness, membership change, log compaction |
| D. Batteries | Database, HTTP client, sessions and auth, server push, jobs, observability | `examples/ledger` is a full web application using all of them | The HTTP client with TLS (D67), PostgreSQL's protocol over TLS with a pool (D68, D83, `examples/todo-db`), sessions and authentication, sign-in with OAuth and OpenID Connect (D72), server push (Server-Sent Events, `Lanes/Web/Http/Sse.lean`), jobs and a scheduler, the server's metrics, health checks and access log (D69), S3, SES and SQS (D71, D74), migrations of a journal (D66). `examples/ledger` runs with sessions and a journal, and is proved to implement its spec with its deadlines (`Ledger.implements_timed`). Not built: a TLS server, observability beyond the server's own pages, the ledger on a database. Now ordered by the standard library's P0 (`docs/STDLIB.md`) |
| E. Developer experience | A macro that hides signature boilerplate; `lanes prove`; counterexample-to-induction; a cheaper proof API; tutorial; trace viewer | A new user ships a checked application in a day | `lanes_data` and `instance_by_cases`; `lanes new` with a proved counter. In progress: the cheaper proof API (direction 1). `docs/TUTORIAL.md`. Not built: `lanes prove`, counterexample-to-induction, a trace viewer |

A came first because B to D build on its contracts; C came before D because Raft found the
mistakes in A and B while they were cheap to fix. Since D45 the direction above sets the order
inside D and E.

## Serious applications

`examples/` holds small pieces, one idea each, that run in seconds, and the serious
applications, each its own Lake package that requires Lanes as a user would; the serious ones
have a CI job each.
They stay in this repository while the API they use is changing, so that a framework change that
breaks one cannot merge. One moves to its own repository when that API has settled or the
application needs its own releases.

`examples/raft-kv` is frozen as a regression suite: its checks, proofs and process tests stay in
CI, and no Raft feature is added unless the framework needs it. `examples/ledger` is the stress
test of phase D and the measure of direction 1.

## Assumptions made without an answer

- **The Lean runtime is the production target for now.** If it becomes a reference
  implementation instead, the kernel is run from another host and the investment moves to
  proofs.

## Standing risks

- **Lean as a production runtime.** A thread crossing costs tens of microseconds; Std has no TLS
  and no database client, so Lanes binds the OpenSSL Lean's toolchain links (D67) and speaks
  PostgreSQL's protocol itself (D68); `Std.Async` is young. There is no preemption, so one
  slow `step` stalls its shard.
- **Proof cost.** The key-value store's refinement took about 300 lines, Raft's safety about a
  thousand and its refinement some 800 more; how much a relation library and automation close
  the gap is unmeasured, and every kernel change re-proves hundreds of lines.
- **Trusted code grows with features.** The shell is flat; file IO, the transport and the
  adapters are what grew. `lanes lint` pins each file's size and `scripts/mutants.py` holds the
  known ways of breaking it, each of which has to fail a test.
- **A spec can say the wrong thing.** A theorem says the code meets its spec, not that the spec
  says what was meant; a property can also be too strong on states never reached. Specs are
  short and reviewed by a person (direction 5), proved code is tested against a reference where
  one exists, and checks seed bugs and widen bounds one at a time.
- **Model-checker state explosion.** Raft on three nodes with a crash is millions of states;
  larger instances wait for checker v2.
- **Lean churn.** The toolchain is upgraded deliberately, and Lanes requires no other package.
