# Changelog

What changed in each release of Lanes. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/) as `docs/RELEASING.md` applies it to 0.x. A pull
request that changes the library, the C, the `lanes` command or the app template adds a line
under Unreleased (`CONTRIBUTING.md`).

## [Unreleased]

### Added

- Models of external services (`Lanes/Outside/`): `Rpc.outside`, a call answered at most once, `unknown` at its deadline with its effect left open, or never; `Idempotent.server`, idempotency keys, proved to give a request always sent under one key at most one effect in every run the model allows (`Idempotent.at_most_once`); `Events.bounded`, webhooks late, out of order and repeated up to a bound; `Effects`, services that hold things with a lifecycle, and its instances `Payments` (the statuses Stripe documents for a PaymentIntent) and `Email`. `Outside.see`, `Outside.after_induction`, `Outside.after_invariant` and `Outside.after_both` reason about runs a model allows; `System.Emits.outputs` lifts what actors emit to every output of every run.
- `examples/payments`: a shop that charges each order through the payment model, checked with the classic bug seeded (a retry without the key charges twice) and proved to charge each order at most once (`Shop.charged_at_most_once`).
- `ServerConfig.ioThreads`: connections owned by dedicated threads, so a connection never changes thread (21–30% more requests a second on the warm machine); and `Runtime.Config.workers`: a batch's actors' steps worked out in parallel, proved equal to the sequential run (`Kernel.runBatchAhead_eq`). Both are off by default.
- A PostgreSQL client in Lean (`Lanes/Lib/Postgres/`): the frontend/backend protocol 3.0 with trust, cleartext, MD5 and SCRAM-SHA-256 authentication, the extended query protocol with parameters in text, errors and transactions, over plain TCP; messages proved to read back as written, a connection as a pure `Postgres.Conn.step` proved to answer requests in order and never to report a failed transaction committed, and an IO file that only performs. MD5 and PBKDF2-HMAC-SHA-256 in Lean (`Lanes/Lib/Crypto/`).
- A transactional store model (`Lanes/Outside/Store/`) at read committed and serializable, with lost `COMMIT` answers, as an `Outside`, and an adapter that runs it on a PostgreSQL table (`Postgres.Store.handler`).
- `examples/todo-db`: a to-do list in PostgreSQL, where the checker finds the duplicate row that retrying a lost commit makes, and the fix is proved.

### Changed

- The HTTP server runs its connections on four threads of its own by default (`ServerConfig.ioThreads := 4`); `0` keeps the earlier behaviour.
- Module paths are reorganised by concern: `Lanes.Actors` is split into `Lanes/Core`, `Lanes/Proof`, `Lanes/Runtime`, `Lanes/Durable`, `Lanes/Net` and `Lanes/Outside`, HTTP, HTML and authentication are under `Lanes/Web`, the standard library under `Lanes/Lib`, and each area's IO in an `IO/` directory; `import Lanes` leaves out the framework's soundness theorems, which a proof imports with `import Lanes.Proofs` (or `Lanes.Semantics`); `Examples/` and `systems/` are one `examples/` directory of Lake packages, `examples/counter` being what `lanes new` writes.
- `Tests/Fixtures/` keeps the small applications' systems and the two bank theorems the tests carry to shards; the proofs of election, the key-value store and the watchdog are only in their examples.

### Removed

- `Actor.comapMsg`, which nothing used; the `Repr Empty` instance of `Lanes/Core/Inspect.lean`, which Lean has; helper lemmas of the soundness proofs that no proof used.

## [0.1.0] - unreleased

The first public release, a beta. It targets Lean `v4.37.0-rc1` and the CSLib commit pinned in
the Lake file.

### Added

- Actors with pure step functions, systems with an explicit boundary, and effects as data: send, emit, after, cancel, stop.
- One executable semantics of systems, stated as a CSLib labelled transition system, with refinement, specs, fairness and leads-to.
- A model checker with drivers, `always` and `sometimes` properties, refinement checks against a service spec, and seeded random runs with faults; a complete PASS is proved sound.
- A runtime: a proved kernel inside a thin shell, a bounded inbox read in batches, timers as data, and a thread per shard that parks when idle.
- Durability: a journal of what the kernel was asked, replayed at start, with snapshots that cut it; proved to recover the kernel from a file cut at any byte.
- Composition by `System.join`; a system on any number of shards proved to behave as the one system; a transport between processes with its decisions in a pure courier.
- Services as specs, the `Server`, `Once` and `Jobs` behaviours with their proofs, and the standard simulation for proving a service behind actors.
- Proof tools: per-actor invariants lifted to every fault model (`actor_invariant`), ghosts with erasure, monotone invariants, quorums, and where messages come from (`System.Sent`).
- HTTP: a gate joined in front of a system, typed routes proved to print and match alike, a strict request reader, the server's own connection loop on `Std.Net` as a pure `Http.Conn`, and an HTTP client.
- HTML values and a template macro, htmx attributes from routes, forms and cookies with proofs against their specs.
- Authentication: signed tokens, form tokens, sessions, failed-attempt limits and Argon2id password digests.
- Data: `lanes_data` with derived `Codable`, `Enum` and `LawfulBEq`; law-carrying codecs; JSON; Base64; IP addresses and prefixes; civil dates, RFC 3339 and HTTP dates; SHA-256 and HMAC references.
- Bindings to libsodium, `fsync` and a timed thread wait, each beside a Lean reference where one exists.
- Differential tests of the parsers against Go's standard library, with every difference decided.
- The `lanes` command: `new` (an app with a proved counter, a journal and a page), `lint`, `check` and `inventory`.
- A generated inventory giving every public definition its status and evidence, and an axiom gate per area.
- Reference examples: a bank, leader election, a key-value store with front ends, a watchdog.
- Applications built on Lanes: raft-kv (Raft, proved to implement its map, acting once per command), ledger (proved against its timed spec) and rookery (a message board with a JSON API).
- macOS support: libsodium found through pkg-config (Homebrew on Apple silicon included), and a macOS CI job.
- CI with one required check, a merge queue, a mutation gate for trusted code, and a benchmark workflow on a warm runner machine.

### Changed

- The HTTP server reads and writes HTTP itself; `Std.Http` is no longer imported.
- `serve` runs one gate joined in front of the system; the separate gated server is gone.
- The in-process router between shards is removed: shards in one process are one system.
- A spec names its inputs and outputs, and time passes in it as deadlines.
- A deadline may pass where a message is served.
- Actors at rest are released and started again by the kernel, with its theorems up to those starts.
- `Driver.deliver` takes the receiver and the message.
- A JSON object with a repeated key keeps the last value.

### Fixed

- Findings of five code reviews in the runtime, the shell, the HTTP adapter, routes, lint and the checker.
- The kernel's `fire` and the agenda of pending timers.
- The HTTP server and the shard no longer wake on every task, which burned a core while idle.
- Tests that could hang (the wire test's stop, raft-kv's process test) fail in bounded time.

### Security

- The request reader follows a strict profile: the shapes used for request smuggling are refused and every refusal closes the connection.
- URL attributes are rendered through `Html.safeUrl`, so a `javascript:` link cannot be written.
- A request is prepared before it is journalled, so a password or a cookie need never reach the disk.
- Secret comparisons, hashes and random bytes come from libsodium rather than Lean code whose timing is not controlled.
- A journal that is not the one expected, or is damaged other than by a cut, is refused and never repaired.
- CI runs pull requests from forks on GitHub's runners only, and the runner machine's role trusts this repository by its ids.

[Unreleased]: https://github.com/tacitresearch/lanes/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/tacitresearch/lanes/releases/tag/v0.1.0
