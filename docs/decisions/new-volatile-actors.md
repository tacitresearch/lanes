# D?. Actors are volatile, and durable state lives in outside services with models

Status: Accepted

The owner approved this redesign (issue #239). It reverses D24, the journal, and what was built
on it. It says what Lanes is, where durable state lives, what the runtime is, and what leaves the
main branch.

## What Lanes is

Lanes is a runtime and library for building software in Lean 4. It says "library", not
"standard library": Lean already has `Std`.

- Programs are actors whose logic is a pure step function.
- The runtime runs them, and the same step functions are model-checked and proved against a
  spec.
- The plain library must be usable without actors: encodings, cryptography, time, HTTP and
  PostgreSQL are useful to a program that has none.
- Core grows only with what two unrelated programs would both want. The rest is a package.

## Actors are volatile

After a process restart every actor is back at its initial state, as in Go, Tokio or Erlang.
Each starts again from `init`, through `recover` as at its first start (D5). What was inside the
process is gone: actor states, timers, messages in flight, and outputs not yet handed over.

The semantics gets a restart event. It resets every actor at once. The checker explores it as it
explores a crash, and a proof states whether its environment allows it.

## Why the journal goes

The journal had one property: a restart is not a crash. A process that died replayed its inputs
through the same kernel and came back in the state it had (D24). Everything proved for an
environment without crashes still held across restarts. That property was the foundation of D24
and of most of what followed it.

It matters only when important state lives in actor memory. Almost no application needs that.
A web application keeps its users, its orders and its payments in a database, and would keep
them there even with a journal, because operators, reports and other programs read the
database.

What the property cost:

- snapshots, and a data format for journal files that every later version must read (D29, D97);
- migrations that keep the old version's step functions frozen in the binary (D66);
- one writer per shard, a persistent disk, and a deploy unlike any other (D70);
- the hibernation of actors and the projection of a journal, still to come (D96);
- the contract work on delivery between journals: output ids, a handshake between peers, links
  that promise little (D30, D102, D105).

Each piece was sound, and most were proved. Together they were most of the work, for a property
few applications use. So the property goes, and its cost with it.

## Inside and outside the process

The line is the process.

- **Inside**, the runtime and the logic are Lean. Lanes binds only what touches physics (rule
  2.7, D46).
- **Outside**, every service is a model, checked against runs recorded from the real service,
  as S3 already is (D80, `oracles/`).

Postgres is not special. Trusting a modelled Postgres is the same kind of trust as trusting a
modelled S3. The journal was the one outside thing Lanes wrote itself, and it was trusted to meet
a disk model too (`Lanes/Durable/Disk.lean`).

## Durable state lives in outside services, each with a model

Postgres is the default store. S3 holds objects. There are queues, email and payments. Each is
a model in Lanes and a client that talks to the real service.

**A request handler is pure and does one transaction, at SERIALIZABLE.** The handler's type
enforces both. It cannot do IO; it returns the transaction to run and the answer to give.

- Because the handler is pure, the framework retries a serialization failure automatically and
  safely. Running it again repeats nothing outside the transaction, since the transaction is all
  it does.
- One transaction per request closes a class of bugs: one operation spread over several
  transactions, with a crash or a concurrent request between them.

**Invariants are proved per transaction.** If each transaction keeps the invariant, serializable
execution keeps it always, under the store's model. Serializable means the committed
transactions give the state some serial order gives, and an invariant kept by each step of a
serial order holds at its end. The model is `Lanes/Outside/Store/`, whose serializable level
already refuses write skew and lost updates (`Store.write_skew`, `Store.lost_update`).

**Effects and timers live in the database.**

- An outbox: an email, a payment or a call to make is a row written in the same transaction as
  the change that caused it. A worker performs it and marks it done.
- Jobs are rows of a table with the time they are due.
- Idempotency keys: a request that carries a key writes it in its transaction, so a retry finds
  it and gets the answer already given.

## Deterministic simulation and model checking are kept

They depend on pure steps, effects as data and models of the outside, not on the journal.

The checker now also explores the store's faults: a `COMMIT` whose answer is lost, a
serialization failure, and a crash between the commit and the reply. The store's model already
has the first two (`Store.lost_commit_either`, `Store.failed_never_committed`).

Replay of a production run can come back as an opt-in input recorder, off the commit path. It
records inputs for debugging and never delays an answer. It makes no state durable.

## What is lost

Said plainly:

- Actor memory across restarts.
- Proofs about data rest on a trusted, tested store model instead of on Lean values.
- Decisions at memory speed, without contention, on hot state. A counter every request touches
  is a row, and concurrent requests on it conflict and retry.
- Theorems that relied on the journal are restated or removed.

## Several instances behind a load balancer

This is the normal deploy. An actor's state is a cache of its process. Whatever must agree
across instances lives in the database. An instance can be replaced, scaled or restarted at any
moment, because it holds nothing that is not elsewhere.

## The runtime

The runtime has Tokio's scope: one process, with no durability of its own.

Its scheduler becomes free-running, proved to refine the interleaving semantics: every
execution is a run of `SysState.step`. It replaces waves, which committed parallel steps in the
order a journal would have (`Kernel.runWaves_eq`, D64, D88). Without a journal there is no order
to keep.

A paused measurement on the branch `claude/waves-default` compared the two on a prototype.
Free-running was 3 to 5 times lower at p50, with about twice the throughput, and similar at p99.

## The environment, in three layers

1. **Platform models, in core**: the clock, randomness, environment variables and
   configuration, the file system with crash semantics (unsynced writes lost, torn writes,
   atomic rename), network and DNS, signals and shutdown, standard input and output.
2. **Service shapes, in core**: a call whose answer may be unknown, idempotent requests,
   webhooks and events, things with a lifecycle, a transactional store (growing from key-value
   to SQL tables and queries), an object store, a queue, a cache, a throttle.
3. **Services, in one area of the same package**, `Lanes/Services/<Name>/`:
   - `Postgres`;
   - `S3`, for any S3-compatible store;
   - `Aws`: credentials, SES, SQS, CloudFront, folded in from `integrations/aws`;
   - `Oidc`, with Google and GitHub as presets, folded in from `integrations/google` and
     `integrations/github`;
   - later `Stripe` and `Sqlite`.

The bar for a service is a client, a model built from a core shape, and an oracle against the
real service or an emulator. A service without an oracle yet is marked experimental.

Services are bundled because Lake builds only the modules a program imports, so a service a
program does not use costs it nothing. A service becomes a Lake package of its own only when it
brings a heavy dependency or needs its own release cadence. The layering lint enforces the
direction: services import core, and core never imports services.

HTTP is a protocol, not a service, and stays in core.

## Serialization

`lanes_data` derives JSON and database rows. The binary codec and the former names
`(was …)`, built for journal files, go (D97, D103).

## What is removed from main

It is preserved on the branch `claude/archive-journal-runtime`.

- The journal and `Lanes/Durable/`, including the disk model, the framing, shipping to S3 and
  output ids.
- `Lanes/Net/` and shards in different processes.
- The data format's schema, body, matching and diff.
- `Quorum`.
- The Transcode models.
- `lanes journal` and the schema lint.
- The corpus of old journals.
- The examples raft-kv, election, migration, ledger and videos.
- The stateful deploy: `infra/app` and `docs/DEPLOY.md`.
- The per-definition inventory.
- The per-PR changelog machinery.
- Mathlib and CSLib, from the core library. The proof study recommended it
  (`docs/decisions/new-proof-libraries.md` on the branch `claude/cslib-mathlib-study`), and #130
  adds an example application that uses Mathlib for its own proofs.

## What changes in designs that assumed the journal

- **D101's step context.** `now` and `seed` come from the runtime, not from the journal.
  Quarantine becomes poison-message handling: a message that kills its step is set aside and
  reported, without the journal's careful starts.
- **Jobs, schedules and acting once** move to the database (D55, D79, D48, D54).
- **Sessions** use signed tokens or the database.
- **D106's gate stays**, as admission control. Its reasons of a journal and waves do not.
- **D105's output ids** are replaced by outbox row ids, used as idempotency keys.

## Decisions this supersedes

Wholly: D24, D29, D36 and D66 (the journal, snapshots, migrations); D70 (the deploy); D28, D30,
D37 and D102 (shards and peers); D94, D97, D103 and D105 (the journal's name, its format,
former names, output ids); D73 and D88 (waves); D79 (a scheduler whose jobs survive a restart);
D87 and D91 (the video site's jobs and pipeline); D35 and D54 (Raft); D47 (the inventory); D11
(the import root for Mathlib).

In part, each saying which part in its status line: D10, D18, D23, D32, D38, D44, D45, D48, D55,
D61, D64, D69, D72, D74, D93, D96, D99, D100, D101, D106, D107, D108 and D109.
