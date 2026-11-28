# Working on Lanes

Lanes is a framework for verified software in Lean 4: actors with pure step functions, one
semantics, a proved runtime kernel, a model checker, proofs, and adapters. This file is the rules,
for agents and for people. `README.md` is the front door, `docs/ARCHITECTURE.md` says how the
pieces fit and where each is proved, `docs/STATUS.md` what exists, `docs/ROADMAP.md` the direction
and what is being done now, `docs/decisions/` why, `TRUSTED.md` what is trusted.

Rules carry numbers (rule 2.6) because code, decisions and reviews cite them. Never renumber; a
new rule takes the next free number in its group. Cite a rule in a PR description when it shaped
a choice. Each rule says why, so a case it does not cover can be judged.

## Build and checks

```bash
lake exe cache get         # once, in a fresh clone: prebuilt Mathlib; never build Mathlib from source
lake build --wfail         # the library, warnings as errors (as CI builds it)
lake test                  # pure tests and live runtime tests, a few seconds
lake exe lanesCheck        # larger model checks, random runs and the scale benchmark, about 20 s: run once, never in a loop
lake exe lanes lint        # the checks below, and that generated files are up to date
lake exe lanes lint --fix  # rewrite the generated files: line counts, decisions' index, STATUS, INVENTORY
lake exe lanes stats       # the totals no file holds: trusted lines, decisions, the inventory by area
lake exe lanes changelog   # the Unreleased section, gathered from `docs/changes/`
lake exe lanes inventory --list none  # the definitions of Lanes/ without evidence
lake exe lanes docstrings  # how many public declarations of `import Lanes` have a docstring
```

- Run `lake build --wfail`, `lake test`, `lake exe lanesCheck` and `lake exe lanes lint` before
  calling a task done. CI runs them in that order, then `lint --fix` must change nothing, then a
  generated app is built and tested, the small examples are built and checked, and
  `examples/raft-kv`, `examples/ledger` and `examples/rookery` run as jobs of their own. A pull
  request that changes only documentation is built and linted, and the other jobs are skipped
  (the `changes` job of `.github/workflows/ci.yml` says which files count).
- `lanes lint` checks the text of a project: `no-sorry` (no `sorry` or `admit`), `trusted-listed`
  (`partial`, `unsafe`, `axiom`, `panic!`, `implemented_by`, `extern` and C only in files
  `TRUSTED.md` names), `trusted-size` (each trusted file has the line count `TRUSTED.md` gives),
  `layering` (rule 1.6), `decisions` and `status` (the generated files agree with their sources),
  `changelog` (each fragment in `docs/changes/` reads), `inventory` and `inventory-none` (below), `links` (every repository path in backquotes in
  `*.md` and `docs/*.md` exists) and `oracles` (`oracles/README.md` names an oracle, or why there
  is none, for every protocol module and model, and every path it names exists). It does not check `no-io-in-step`, `bounded`, `field-leak` or
  `fn-length`: those need the elaborator. The inventory's checks read the built modules: run
  `lake build lanesInventory` before `lake exe lanes lint --fix`.
- `docs/INVENTORY.md` gives every public definition a status, read from the built modules
  (`docs/decisions/D47-the-inventory-is-computed.md`). A theorem makes what it states proved when
  it has an axiom gate. A new definition of `Lanes/` with no theorem, test or row of `TRUSTED.md`
  fails `lanes lint` unless it is on `docs/inventory-none.md` under a heading that says why; when
  one there gets evidence, take it off.
- Templates are embedded with `include_str`, which Lake does not track: after editing
  `templates/`, delete `.lake/build/lib/lean/LanesCli/New.*` and `.lake/build/ir/LanesCli/New.*`,
  rebuild `lanes`, and write `examples/counter` again (move it aside, run `lake exe lanes new
  counter --dir examples/counter --lanes-path ../..`, put its `lake-manifest.json` back): `lake
  test` fails while the two differ. Then build and test it.
- Oracles (rule 5.9, `docs/decisions/D80-oracles.md`) are in `oracles/`, one folder per
  reference implementation with its pin, and `oracles/README.md` lists every protocol module and
  every model against its oracle or the reason it has none (lint `oracles`). *Pure oracles*: a
  reference's program (`oracles/go/<package>/main.go`, `oracles/<reference>/main.py`) answers the
  cases `Tests/Oracle/<Package>.lean` generates, and every difference is a `known` predicate
  there, with its reason, or a failure. `lake exe lanesOracle --cases 100000 [package…]` asks the
  references (it needs `go` and `python3`; Python's are set up in virtual environments under
  `LANES_ORACLE_CACHE`, or `.lake/oracles`); `lake test` replays the answers recorded in
  `oracles/<reference>/answers.jsonl`, which `--record` rewrites. CI runs them on every pull
  request. *Service oracles*: `oracles/moto/run.sh` and `oracles/postgres/run.sh` start moto or
  a PostgreSQL of their own, run our clients against it through their handlers, check the runs
  against the models with `Outside.allows`, and stop the service; `--record` rewrites the
  records under `oracles/`, which `lake test` checks against the models again. CI runs them
  nightly (`.github/workflows/services.yml`). The request reader's verdicts on
  `Tests/ReadRequest.corpus` are compared with Go's, Node's and h11's servers by
  `oracles/go/requests/requests.py`, run by hand.
- The toolchain is pinned in `lean-toolchain` and follows CSLib's. Dependencies are pinned in
  `lake-manifest.json`; upgrade them deliberately, CSLib first.
- A test of an application's front end drives it with `Http.Loopback` (pure, no socket: the
  connection, the gate and the system, as the server runs them), and a live test of a process
  with `Http.Client.fetch` (`examples/README.md`, "Testing a front end"). Do not write HTTP by
  hand.
- To work on a proof without rebuilding the file, `scripts/lean-goals` asks a language server it
  keeps open for a file's errors and the goals at some lines (`LINE` from 1, `COL` from 0):

  ```bash
  scripts/lean-goals --daemon Lanes/Web/Http/WireSound.lean 1710 1702:4   # start a server, ask it
  scripts/lean-goals Lanes/Web/Http/WireSound.lean 1710                   # later calls use it
  scripts/lean-goals --stop                                            # when done
  ```

  After an edit it elaborates again from the first changed command only. Each worktree has its
  own daemon, which stops after an hour unused; `--reopen` reloads a file whose imports changed.
  It does not replace `lake build` before a commit.

## Design

1.1 **Separate the essential from the accidental.** Specs and actor state hold only what the
problem needs; a cache or an index is a separate view with a theorem tying it to its source.
*Why:* most complexity is accidental state.

1.2 **Write the spec first**, even five lines, and model-check it before the implementation or a
proof. *Why:* an interface that cannot be specified is not ready, and the spec is what the code is
proved against.

1.3 **Deep modules, narrow interfaces.** Hide much behind a small surface: a few functions and an
opaque state, not record fields; one actor with three kinds of message over five that forward.

1.4 **Don't complect.** Keep values apart from identity, `step` from scheduling, policy from
mechanism. A function that decides and performs is two functions. *Why:* concerns that are
interleaved cannot be proved one at a time.

1.5 **End-to-end checks at the ends.** Duplicate suppression, ordering and recovery belong to the
endpoints (request ids, the spec's operation); transport retries are an optimisation, never the
argument.

1.6 **Layers run one way.** Runtime modules import `Std` only; Mathlib, CSLib and proof modules
(`Lanes.Semantics`, `…Proofs`) are imported only by proof files (lint `layering`). No cycles.
*Why:* executable code that imports the proof layer links all of Mathlib (over 150 MB).

1.7 **One concept, one name**, in code, specs and docs; names state units and bounds
(`timeout_ms`, `maxBatch`).

2.1 **Make illegal states unrepresentable.** A role is a sum type that carries its own data, not
flags in a record; bounds are subtypes and `Fin`. *Why:* a state the type rules out is an
invariant never proved.

2.2 **Parse, don't validate.** Adapters turn bytes into typed messages once, at the edge; `step`
never sees a raw string or an unchecked number.

2.3 **Data, calculations, actions.** Messages and effects are data, `step` and what it calls are
pure and total, and only the runtime and adapters act.

2.4 **`step` never runs IO.** It returns effects (`send`, `emit`, `after`, `cancel`, `stop`; D3).
Work outside the system is an output to an adapter whose handler performs it and whose answer
comes back as an input (D26). *Why:* the semantics stays a plain transition system, and the
checker and the proofs run the real code.

2.5 **Explicit options.** Configuration is one `structure Config` with every field named, passed
in at the start; no global settings and no environment lookups in logic.

2.6 **Bound everything.** Every queue, map, retry and batch has a maximum in its type or `Config`,
and the spec says what happens at the limit (refuse, shed, wait). *Why:* unbounded structures hide
liveness and memory bugs, and bounds keep the checker finite.

2.7 **Bind only what touches physics** (D46). Write in Lean, and prove, what decides; bind what
Lean cannot express (timing, the operating system), keep a Lean reference beside each binding,
and count the C in `TRUSTED.md`.

3.1 **Let it crash.** An actor in a state its spec does not cover emits `stop` rather than limping
on; it starts again, through `recover`, on its next message (D5, D18). No defensive fallbacks.
*Why:* defensive code hides the bugs the checker should find.

3.2 **The runtime is the error kernel.** Only the runtime shell, adapters' IO and bound C are
trusted, they stay small, and an actor's crash never corrupts another's state.

3.3 **Crash-only.** There is no clean-shutdown path: every start, the first included, runs
`recover`, and the semantics can crash any actor at any step. *Why:* the path that is proved is
the one that runs on every restart.

3.4 **Requests to the outside have an id and a deadline**, and one that may be retried is
idempotent or its spec says what a repeat does.

3.5 **Prefer a behaviour.** Before a bespoke actor, check `Lanes/Behaviours/`: each behaviour comes
with its spec and its proof (`Server.implements`).

3.6 **One message, one atomic transition.** What must touch two actors at once goes through a
protocol or a single owner, never shared state.

3.7 **Batch at the edges.** The shell batches inputs, journal writes and syncs; `step` still sees
one message at a time, and a theorem says the batch is unobservable (`Batch.run_kernel`).

3.8 **Back-pressure, not unbounded inboxes.** The inbox is bounded (`inboxCapacity`); when it is
full the sender is refused (`tryInput`, the server's `503`). The kernel's queue between actors
has no bound yet (`TRUSTED.md`).

3.9 **An adapter decides nothing in IO.** It is a pure function or a system that decides, a model
of the outside it talks to (`Outside`), and a handler that only performs (D26, D40). *Why:* every
defect four reviews found was a decision made in IO code.

## Code

4 **Inside `step` and the logic it calls:**

- State a pre- or postcondition as a type (subtype, `Fin`), a theorem beside the function or an
  invariant of the spec; `assert!` only where input is untrusted, at an adapter.
- Total by default: structural recursion or `termination_by`; no `partial`, `unsafe`,
  `implemented_by` or `extern` outside the files `TRUSTED.md` names (lint `trusted-listed`).
- Branch on the message once, at the top: one `match`, one handler per constructor, each short
  enough to be one proof goal; helpers are branch-free calculations over collections.
- Keep a function under about 70 lines.
- No `IO.Ref`, `ST` or `unsafe` in logic; no `do` with `mut` in `step` unless it is clearer.
- Errors are `Except` or a sum type in the result, never `panic!` or `default`; an unexpected
  state is `stop` (rule 3.1), never a silent skip.
- Names say units and bounds (rule 1.7); use namespaces, not prefixes.

Conventions:

- Library files use the module system: `module`, `public import`, then `@[expose] public section`
  (as CSLib does). A definition whose body uses private helpers is `@[no_expose]`.
- Write almost no comments. A comment or docstring is for a *why* that a name, a type or a theorem
  cannot carry; never restate the code or narrate a change. Each file keeps a short `/-! -/`
  header. A public declaration gets a docstring only when its name and type do not say what it
  is. Do not copy the docstring density of older files. `Lanes/Semantics/` documents every
  declaration, because CSLib's linter requires it.
- Define a concrete system with `abbrev`, so instance resolution can see its `State`.
- Template syntax is scoped: a view file starts with `open scoped Lanes.Html`; a tag follows `<`
  with no space (`<div>`), and `a < b` with a space is a comparison. Keep views and `main` on
  `import Lanes`: Mathlib's `<i` token breaks `<input>`.
- In `do` blocks, `(← action)` inside `a || b` or `a && b` runs whether or not the other side
  decides. Bind it first when it must be conditional.
- Lean never updates an object in place once another thread may see it, and state held across an
  `await` is handed to the task system. Hot state (a kernel, a table) lives on one thread, in an
  `IO.Ref` used through `modifyGet`.
- Take pairs apart by pattern (`let (a, b) := f x`), not with `.1` and `.2`, when the first part
  is large state that is then updated: a projection keeps the pair, and the state, alive.
- An instance over an abstract signature (`[σ.Inspect] : (joinSig σ τ).Inspect`) is not found for
  a concrete one, which is an `abbrev` that instance search unfolds. Write it as a named
  definition and give it in one line: `instance : (joinSig a b).Inspect := .join`.
- A family of instances by cases on an identity (`∀ i, DecidableEq (Msg i)`, the `Inspect` of a
  system whose actors differ) is `by instance_by_cases`.

Layout, and what each part may import. A module is in the directory of its concern; a file
that performs IO is in an `IO/` directory of its area and named in `TRUSTED.md`.

| Path | Contents | May import |
| --- | --- | --- |
| `Lanes/Core/` | `Actor`, `Signature`, `Effect`, `System`, the semantics' step (`World`), each event and run in closed form (`Step`, `Run`), joins, `Service`, `Inspect`, the deterministic and fair schedulers | `Std` only |
| `Lanes/Proof/` | The proof toolkit: lifting per-actor invariants, `Monotone`, ghosts and `Past`, `SysState.Equiv`, deeds, loss; what survives a join (`JoinSound`, `MapIOSound`); lemmas about lists (`List/`), strings (`Utf8`) and byte arrays (`ByteArray`) | `Std` only |
| `Lanes/Runtime/` | The kernel and its proofs, batches, the inbox, shards; the shell and the parker in `IO/` | `Std` only |
| `Lanes/Durable/` | The journal, snapshots, the disk model, the framing of a file; the journal's files in `IO/` | `Std` only |
| `Lanes/Net/` | The courier, every decision of the transport, and its proofs; the transport and a process with an HTTP front in `IO/` | `Std` only |
| `Lanes/Outside/` | What the outside may do (`Outside`), the home of models of external systems (calls, idempotency keys, webhooks, payments, email, an object store, and transactional stores in `Store/`); the clock in `IO/` | `Std` only |
| `Lanes/Web/` | HTTP as data, its grammar, the gate, routes, cookies, the wire format, the server's connections and Signature Version 4 (`Http/`); HTML values and templates (`Html/`); tokens, password digests, failed attempts, sessions (`Auth/`); the S3 client's calls and answers (`S3/`); the server, the client and the S3 client in `IO/` | `Std` only |
| `Lanes/Behaviours/` | Standard actors with their specs and proofs, by feature (`Server`, `Jobs/`, `Once/`, `Schedule/`) | `Std` only |
| `Lanes/Check/` | Model checker | `Std` only |
| `Lanes/Data/` | `Enum`, codecs and `lanes_data`, the queue, quorums | `Std` only |
| `Lanes/Lib/` | The standard library: encodings (Base64, JSON), addresses and URLs, time, SHA-256, HMAC, MD5, PBKDF2 and `Native`, the PostgreSQL protocol (`Postgres/`), media types, rate limits (`docs/STDLIB.md`) | `Std` only |
| `Lanes/Testing/` | The test kit, for tests and never in `import Lanes`: a fake S3 that checks signatures, a fake identity provider, a scripted browser, a server of a handler and readers of a response (`docs/decisions/D77-a-test-kit.md`) | `Std` only |
| `Lanes/Semantics/` | The semantics as a CSLib `LTS`, refinement, specs, fairness and leads-to, and the liveness of the gate, of jobs and of the scheduler | CSLib, Mathlib |
| `native/` | The C that binds OpenSSL's hashes, comparison and Argon2id, `fsync`, a timed wait, OpenSSL's TLS client, its signature check and its signing, all of it trusted | OpenSSL, libc |
| `LanesCli/` | The `lanes` command: `new`, `lint`, `check`, `changelog`, `stats`, `inventory`, `docstrings`, `journal` | `Std` only; `Lean` in `Inventory` and `Docstrings`, which only `lanesInventory` links |
| `templates/app/` | The application `lanes new` creates, which is `examples/counter` | |
| `examples/` | Applications to read, each its own Lake package (`examples/README.md`) | anything |
| `integrations/` | A vendor's preset or client, each its own Lake package (D61): `google` and `github` for sign-in, `aws` for a role's credentials, SES and SQS's calls, and CloudFront's signed URLs | Lanes |
| `Tests/` | Regression tests run by `lake test` and `lanesCheck`; the apps they use in `Fixtures/` | anything |
| `docs/api/` | The API reference, built with doc-gen4: a Lake package of its own (`docs/api/README.md`) | Lanes, doc-gen4 |
| `oracles/` | The references the oracles compare with, one folder each, with their pins, programs and records (`oracles/README.md`) | |
| `infra/` | The CI machine: its stack and its set-up script (`docs/RUNNERS.md`); in `app/`, the stack, set-up script and smoke check of an application on AWS (`docs/DEPLOY.md`) | |

`import Lanes` is the API, executable code and the proof toolkit; `import Lanes.Proofs` adds the
framework's soundness theorems (the `…Sound` modules), and `import Lanes.Semantics` the proof
layer, which imports both. Tests and the examples' proofs import what they cite. `import
Lanes.Testing` is the test kit, for tests only, so that no binary that serves links it.

Declare the messages, inputs, outputs and states of a system with `lanes_data`: the ordinary
declaration with a prefix, whose `deriving` also takes three classes Lean cannot derive without
linking `Lean` into the binary.

```lean
lanes_data structure Entry (N C : Type) where
  term : Nat
  /-- The node that took the command from its client. -/
  origin : N
  cmd : C
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Id (F : Type) where
  | front (f : F)
  | store
  deriving DecidableEq, Repr, Hashable, Enum
```

- `Codable` gives `Entry.codec : Codec N → Codec C → Codec (Entry N C)` and an instance;
  `Codec.of T` is the instance's codec, and its law holds by construction. A codec also carries
  its type's `Schema` (the names of its fields and constructors, their defaults and former
  names) and a map each way to `Value`, with the law `ofValue (toValue a) = some a`
  (`Lanes/Data/Schema.lean`); `lake exe lanes journal schema --type T` prints it. Every field's type
  needs `Codable`: `Nat`, `Int`, `String`, `Bool`, `Unit`, `ByteArray`, `Fin n`, `Option`,
  `List`, pairs, sums, sigma types, subtypes, `Std.ExtTreeMap`, and types declared this way.
- `Enum` lists every value. `LawfulBEq` compares a structure field by field, for one that holds a
  function on an `Enum` type and so has no `DecidableEq`.
- Arguments are `(x y : T)` or `(x : T := default)`, fields `x : T` or `x : T := default`,
  each with an optional docstring; a constructor may be a keyword (`| open`). A default names
  no other field. A renamed field, argument or constructor keeps its former names after its
  name, `height (was y) : Int`, `| path (was line)`, `(closed (was shut) : Bool)`, so that data
  written under them can be read by name (`docs/decisions/new-lanes-data-aliases.md`). A value with a property is a subtype,
  read back only if the property holds. A field whose type names an earlier field is refused.
  `extends`, indices and recursive types are not accepted: write those with `structure` or
  `inductive` and the codec with `Codec.struct%` or `Codec.sum%`.
- A line `from Old := f` after `deriving` says how a value of the type's previous version
  becomes one of this: it gives `T.migrate` and a `Migrate Old T` instance. A deploy that
  changes a persisted type keeps the old version's types, codecs and step functions in a module
  of their own, and reads its files through a `Journal.Upgrade` whose `Migration` proves that
  the migrated states satisfy the new actors' inductive invariants (`examples/migration`).

## Proofs

5.1 **Check before you prove.** Every invariant and refinement is model-checked on small bounds
before a proof is attempted. *Why:* a counterexample costs seconds, a failed proof hours.

5.2 **One invariant, one name, one sentence.** Each invariant is a named `def` with a docstring
saying it in English; split conjunctions of more than three clauses so a failure names its clause.

5.3 **A vacuity check for every invariant**: an `always` property is paired with a `sometimes`
showing its guarded state is reachable. *Why:* an invariant over unreachable states passes.

5.4 **Keep abstractions boring.** A refinement map is a short total projection, or a relation
(D34); history goes in ghosts with an erasure theorem (`System.Invariant.of_ghost`, D20).

5.5 **Trusted code is listed, not hidden.** Every `axiom`, `extern`, `implemented_by`, `unsafe`
and IO file has a row in `TRUSTED.md`: where, why it is trusted, how it is checked. Lint fails on
an unlisted one, and the axiom gate (`Tests/Axioms/`) stops compiling when a `sorry` or a new
axiom reaches a headline theorem.

5.6 **Specs say what happens at limits and on faults**: full queues, timeouts, crashes,
partitions, even if only "answers `unavailable`".

5.7 **Liveness is designed in.** A liveness property names its fairness assumption
(`System.Run.Fair`) and its measure before code is written.

5.8 **Everything is proved** (D45). Every definition Lanes ships, and every application in
`examples/`, is proved against a spec, or binds or performs something named in `TRUSTED.md`. A
complete PASS of the checker finds bugs; a theorem is the evidence.

5.9 **A parser has an oracle, and a model a recorded run.** Every parser or encoder (in
`Lanes/Lib/`, and the protocol code of `Lanes/Web/`: the wire format, Signature Version 4, XML,
JOSE) is compared with a reference implementation on generated inputs, and every model of an
outside service is checked against a run recorded from a real or reference implementation; or
`oracles/README.md` says why not. *Why:* a proof says the code meets its spec, not that the
spec reads the standard, or the service, as others do.

Conventions:

- Prove a per-actor invariant with `actor_invariant [myActor]`; it leaves the cases it cannot close
  as goals. It lifts to every system under every fault model (`System.invariant_of_actor`).
- A lemma that does not mention the system a proof is about does not stay in that proof's file.
  Lists: `Lanes/Proof/List/`, at the end of the file of its topic (`Erase`, `Prefix`, `Fold`, else
  `Basic`). Strings and byte arrays: `Lanes/Proof/Utf8.lean`, `Lanes/Proof/ByteArray.lean`.
  `update`, `SysState`, `run` and `Reachable`: `Lanes/Core/World.lean`; a step or a run in
  closed form: `Lanes/Core/Run.lean`; `NetEquiv` and `SysState.Equiv`:
  `Lanes/Proof/Equiv.lean`. Look there, and in core `List`, before proving a helper.
- A layer of a `Monotone` proof that reads states and messages in flight is added with
  `Monotone.and_net` (or `and_state`), not with `below` and `input` lemmas of its own; more than
  two layers get a structure through `Monotone.of_iff`.
- A proof that passes about 30 lines of tactics gets named lemmas. Proof pain is a signal about
  the design, not something to grind through.

## Parallel branches

Several agents work at once, each on a branch merged into the main branch. The layout gives
independent changes disjoint files; keep it that way.

- Commit after every step that builds. Before reporting, merge the main branch and run the checks
  again. Generated files (`docs/STATUS.md`, `docs/INVENTORY.md`, the decisions index) never need
  resolving: run `git config merge.generated.driver true` once (`.gitattributes` names them),
  and after a merge run `lake exe lanes lint --fix`, which writes them again.
- A new decision is a new file `docs/decisions/new-<slug>.md` whose first line is `# D?. Title`.
  Do not choose its number: whoever opens the pull request runs `lake exe lanes lint --fix --main`
  against the current main, which numbers it; CI on main refuses an unnumbered decision. If another
  open pull request took the same number, renumber the later one.
- A change of status goes in its fragment, `docs/status/areas/<area>.md` or
  `docs/status/apps/<app>.md`: its heading on the first line, then each item on one line, in
  sorted lists (`lanes lint --fix` sorts them).
- A change a user would notice gets a changelog fragment of its own,
  `docs/changes/<slug>.md`, never a line in `CHANGELOG.md` (`CONTRIBUTING.md`, "The changelog").
- An axiom gate goes in `Tests/Axioms/<Area>.lean`, under the line naming its module; a lemma
  about lists at the end of its topic's file in `Lanes/Proof/List/`.
- Never type a count: line counts in `TRUSTED.md`, the decisions' index, `docs/STATUS.md` and
  `docs/INVENTORY.md` are written by `lake exe lanes lint --fix`. Each generated line is about one
  item, and no committed file holds a total over the repository (`lake exe lanes stats` prints
  them), so two branches that change different items merge without a conflict. A conflict in a
  generated file is resolved by taking either side and running it.

## Docs

Agents do what the docs say, so a stale doc is worse than none. Keep each short and current.

- Change a doc in the same commit as the code it describes. A doc says what is, not how it came
  to be: history is in git, in `docs/decisions/` and in `docs/history/`.
- `docs/ROADMAP.md` holds the direction, the work in progress and why, the phases and the
  standing risks. When a step in progress is done, take it off.
- `docs/ARCHITECTURE.md` names the theorem behind each claim; a claim without one says it is
  checked, tested or trusted.
- Cite files by their repository path in backquotes; `lanes lint` fails on one that does not
  exist (`docs/history/` and `docs/decisions/` are exempt: they record the past). Name a module
  that is not written yet by its module name (`Lanes.Lib.Encoding.Base32`), not its path.
- `docs/decisions/` is the record of why: never rewrite a decision, write a new one that
  supersedes it.
- Write plainly: short sentences, one name per concept, no marketing.

The design rules adapt TigerStyle, Ousterhout's deep modules, Erlang/OTP, crash-only software,
Lampson's hints, *Out of the Tar Pit*, *Parse, don't validate* and *Grokking Simplicity*.
