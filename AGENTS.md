# Working on Lanes

Lanes is a runtime and library for building software in Lean 4: actors with pure step
functions, one semantics, a proved runtime kernel, a model checker, proofs, models of what a
program talks to, and the library applications need. This file is the rules,
for agents and for people. `README.md` is the front door; `docs/ARCHITECTURE.md` says how the
pieces fit and, area by area, what is claimed with its evidence and the limits of the design;
`docs/decisions/` says why, and `TRUSTED.md` what is trusted. The work, and what is known to be
missing, are GitHub issues (the direction is D110 and issue #239; fixable limits are labelled
`known-limit`).

Rules carry numbers (rule 2.6) because code, decisions and reviews cite them. Never renumber; a
new rule takes the next free number in its group. Cite a rule in a PR description when it shaped
a choice. Each rule says why, so a case it does not cover can be judged.

## Build and checks

```bash
lake build --wfail         # the library, warnings as errors (as CI builds it)
lake test                  # pure tests and live runtime tests, about two minutes
lake exe lanesCheck        # larger model checks, random runs and the scale benchmark, about 20 s: run once, never in a loop
lake exe lanes lint        # the checks below, and that generated files are up to date
lake exe lanes lint --fix  # rewrite the generated files: TRUSTED.md's line counts, the decisions' index
lake exe lanes stats       # the totals no file holds: trusted lines, decisions
```

- Run `lake build --wfail`, `lake test`, `lake exe lanesCheck` and `lake exe lanes lint` before
  calling a task done. CI runs them in that order, then `lint --fix` must change nothing, then a
  generated app is built and tested, the small examples are built and checked, and
  `examples/rookery` runs as a job of its own. A pull
  request that changes only documentation is built and linted, and the other jobs are skipped
  (the `changes` job of `.github/workflows/ci.yml` says which files count).
- A test that needs PostgreSQL runs when `LANES_POSTGRES=host:port` names one, and says it is
  skipped otherwise. `scripts/postgres-test-server` makes one; `scripts/with-postgres lake test`
  makes one for the run, runs the tests beside it, and removes it.
- Lake's artifact cache is on for Lanes, the examples and generated apps
  (`enableArtifactCache` and `restoreAllArtifacts` in each lakefile; D99, section 6). Lake keeps
  each build output once, named by a hash of its content, in the toolchain's cache,
  `$ELAN_HOME/toolchains/<toolchain>/lake/cache` (`ELAN_HOME` is `~/.elan` by default;
  `LAKE_CACHE_DIR` moves it), with a record of which outputs each module's inputs gave. A build
  whose inputs are recorded there makes hard links in `.lake/build` instead of building. So the
  worktrees and apps of a machine share one copy: a new worktree builds only what no checkout
  built before, and its `.lake/build` takes almost no disk of its own. Copying a warm
  `.lake/build` gains nothing. Never write into a file of `.lake/build` in place: it is also
  the cache's file (read-only, which does not stop root). Lake deletes an output before
  building it again, and several worktrees can build at once: an output is stored once under its
  hash and never rewritten, and two builds of a module give the same bytes. An entry is found
  only by the hash of everything a module's build reads, so it is as good as a build, provided
  each file read by `include_str` is declared (below), and except for warnings: Lake does not
  replay the warnings of a module it links from the cache, so `lake build --wfail` shows a
  module's warnings only when the module is built, or was last built, in this checkout. CI gives
  each job an empty cache of its own, so it sees them all. A checkout whose lakefile does not
  turn the cache on still reads it (Lake's default) and adds nothing to it. The cache only grows;
  delete the directory to reclaim it. To build from source, delete `.lake/build` and run
  `LAKE_CACHE_DIR= lake build`: set and empty, it gives the checkout an empty cache of its own,
  in `.lake/cache` (`LAKE_NO_CACHE` stops downloads only). Nothing is fetched from a remote cache
  yet (#98).
- **Small bounds on every pull request, large bounds on a schedule.** A pull request's checks
  are fast and exhaustive at small bounds: each example's `lake test` takes under a minute, and
  a pull request's CI under ten minutes. A model-checking scenario has a small version, in `lake
  test`, and its large version is run on a schedule. A small version still
  reaches every witness it names (rule 5.3), and fails if one is not reached, so it cannot pass
  by exploring nothing. Both are exact: the fingerprinted mode is not a pull request's check. A
  check over its budget is made smaller, never moved to the schedule alone. *Why:* iteration
  speed; a check that takes ten minutes is run less, and bugs wait for it.
- `lake test`, `lake exe lanesCheck` and the examples' check programs print through
  `Lanes.Testing.report` (`Lanes/Testing/Run.lean`): each result has a kind, build, proof, check
  or test, and the program exits 1 when one failed and 2 when a model check passed but hit a
  bound, which is not a pass. `--json` (`lake test -- --json`, `lanes check --json`, `lanes lint
  --json`) prints one JSON object instead. `Report.ok` is a complete pass; `Report.passed`, no
  failure in the part explored, is for a check bounded on purpose, which says so in its name.
- `lanes lint` checks the text of a project: `no-sorry` (no `sorry` or `admit`), `trusted-listed`
  (`partial`, `unsafe`, `axiom`, `panic!`, `implemented_by`, `extern` and C only in files
  `TRUSTED.md` names), `trusted-size` (each trusted file has the line count `TRUSTED.md` gives),
  `layering` (rule 1.6), `decisions` (the index agrees with the decisions, and each has its
  number and status line), `links` (every repository path in backquotes in
  `*.md` and `docs/*.md` exists) and `oracles` (`oracles/README.md` names an oracle, or why there
  is none, for every protocol module and model, and every path it names exists). It does not
  check `no-io-in-step`, `bounded`, `field-leak` or `fn-length`: those need the elaborator. Lint
  reads only text.
- Lake hashes a module's source and imports, not the files it reads with `include_str`. So each
  embedded file is an `input_dir` or `input_file` target that the module's library or executable
  `needs` (`templates/`, `lean-toolchain`, the test keys and Google's recorded documents in
  `lakefile.lean`), which puts the files' hashes in the trace of every module of
  that library: an edit rebuilds them, and neither `.lake/build` nor the artifact cache serves a
  copy built from the old files. A new `include_str` adds its file the same way. After editing
  `templates/`, run `lake build lanes` (`LanesCli.New` is built again, not restored; nothing is
  to be deleted) and write `examples/counter` again (move it aside, run `lake exe lanes new
  counter --dir examples/counter --lanes-path ../..`, put its `lake-manifest.json` back): `lake
  test` fails while the two differ, and rebuilds all of `Tests`, which needs the templates. Then
  build and test `examples/counter`.
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
- The toolchain is pinned in `lean-toolchain` and moved deliberately, in a pull request of its
  own. Lanes requires no other package: its `lake-manifest.json` lists none.
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

1.6 **Layers run one way.** Runtime modules import `Std` only; proof modules (`Lanes.Semantics`,
`…Proofs`) are imported only by proof files (lint `layering`). No cycles. The library uses no
Mathlib or CSLib; an application may use them for its own proofs (#130), from its proof files
only (lint `layering`).
Each module of `Lanes/` is in one package of `docs/decisions/D99-layered-packages.md`, and imports modules of Lanes only from its
package and those below it: the semantics and the checker; actors, and the standard library
beside them; the runtime; the web; the umbrella `Lanes`, which with all below it is the core; and
the services (`Lanes/Services/`), which may import the core, and which the core never imports
(`LanesCli/Layers.lean` gives each file's package, lint `layering`). A definition that a lower
layer needs moves down, or the lower layer takes it as a parameter. *Why:* executable code
that imports the proof layer links proofs it never runs (and all of Mathlib, over 150 MB, in an
application whose proofs use it), a layer that imports one above it cannot be used, or built,
without it, and a library that needs Mathlib ties every application to Mathlib's toolchain and
size.

1.7 **One concept, one name**, in code, specs and docs; names state units and bounds
(`timeout_ms`, `maxBatch`).

1.8 **Decide what belongs from first principles, not from our examples.** Lanes is a runtime and
library people use to build software in Lean, so a piece is judged by what it gives them, not by
whether our own examples happen to use it. For any piece, whether added, kept or removed, weigh
its reach against its total cost. Reach: would people building software in Lean want it, and what
could they build with it that they cannot today? Total cost: its own code, proofs, trusted lines
and concepts a newcomer must learn, plus what it costs people who never use it (a design choice it
forces on the core, imports, build time, rules everyone must follow). Coupling is part of the cost,
never a merit: a low cost to non-users is necessary for an optional piece, but never sufficient. A
general piece whose reach is worth its total cost stays even if no example uses it; a piece that
pulls its design into everything else goes even if it works. Say how you weighed these in the PR
when you add or remove something. *Why:* a library is used for things its authors did not build, and the
journal showed that a feature can be finished, proved and still not worth its cost (D110).

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

2.8 *Retired.* It pinned the schemas of what a journal and a snapshot held. Actor state is now
volatile, and the journal is kept on the branch `claude/archive-journal-runtime`; state that must
outlive the process lives in a service outside, whose model says what it keeps.

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

3.7 **Batch at the edges.** Adapters batch what they exchange with the outside (a connection's
writes, a pool's queries), and a worker steps one actor on several messages in a turn; `step`
still sees one message at a time, and each step is one event of the semantics
(`Sched.Step.sound`).

3.8 **Back-pressure, not unbounded inboxes.** The inbox is bounded (`inboxCapacity`); when it is
full the sender is refused (`tryInput`, the server's `503`). So is an input while
`mailHighWater` messages between actors wait; past `mailCapacity` the process restarts
(`docs/decisions/D123-runtime-limits.md`).

3.9 **An adapter decides nothing in IO.** It is a pure function or a system that decides, a model
of the outside it talks to (`Outside`), and a handler that only performs (D26, D40). *Why:* every
defect four reviews found was a decision made in IO code.

3.10 **An actor's state is a cache of its process.** Whatever must outlive the process, or that
several instances must agree on, lives in the database, and a request does what it does to it in
one pure transaction (`Handler`, D110, D111); an effect it causes is a row of an outbox written in
that transaction (D114). An application refuses to start on tables other than the ones it
declares (`Postgres.Typed.prepare`). *Why:* a restart resets every actor, and instances behind a
load balancer share nothing else; `docs/DEPLOY.md`.

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

- Library files use the module system: `module`, `public import`, then `@[expose] public section`. A definition whose body uses private helpers is `@[no_expose]`.
- Write almost no comments. A comment or docstring is for a *why* that a name, a type or a theorem
  cannot carry; never restate the code or narrate a change. Each file keeps a short `/-! -/`
  header. A public declaration gets a docstring only when its name and type do not say what it
  is. Do not copy the docstring density of older files.
- Define a concrete system with `abbrev`, so instance resolution can see its `State`.
- Template syntax is scoped: a view file starts with `open scoped Lanes.Html`; a tag follows `<`
  with no space (`<div>`), and `a < b` with a space is a comparison. Keep views and `main` on
  `import Lanes`: another library's tokens, such as Mathlib's `<i`, can break `<input>`.
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

A module is in the directory of its concern (D62): `docs/ARCHITECTURE.md` names the directory of
each area. A file that performs IO is in an `IO/` directory of its area and named in
`TRUSTED.md`. What is a vendor's (a client, a model of its service, its fake, a preset) is a
service, in `Lanes/Services/<Name>/`, whose README names its client, its model, its oracle and
whether it is checked (model plus oracle) or a client only (`Lanes/Services/README.md`,
`docs/decisions/D113-service-models.md`); a protocol (HTTP, Signature Version 4, OAuth) and the
shape of a service (`Lanes/Outside/`) are core. Code under `Lanes/` imports `Std` only, but for
the proof layer (rule 1.6).

`import Lanes` is the API, executable code and the proof toolkit; `import Lanes.Proofs` adds the
framework's soundness theorems (the `…Sound` modules), and `import Lanes.Semantics` the proof
layer, which imports both. `import Lanes` leaves out the services: a program imports those it
calls (`import Lanes.Services.Postgres`), and `import Lanes.Services` imports them all with their
soundness theorems. Tests and the examples' proofs import what they cite. `import
Lanes.Testing` is the test kit, for tests only, so that no binary that serves links it; a
service's fake is beside it (`Lanes.Services.S3.Testing`).

Declare the messages, inputs, outputs and states of a system, and the types of its JSON and its
tables, with `lanes_data`: the ordinary declaration with a prefix, whose `deriving` also takes
classes Lean cannot derive without linking `Lean` into the binary, and, for a structure, a
`table` line.

```lean
lanes_data structure Todo where
  id : Int64
  owner : Int64
  title : String
  /-- When it was done, if it was. -/
  doneAt : Option Int64 := none
  deriving DecidableEq, Repr, ToJson, FromJson
  table todos key id
    index byOwner on owner, title
    unique index byTitle "todo_titles" on title

lanes_data inductive Id (F : Type) where
  | front (f : F)
  | store
  deriving DecidableEq, Repr, Hashable, Enum
```

- `ToJson, FromJson`, always together, give the instances and `LawfulJson` (what is written
  reads back) and `NonNullJson`, by construction (`Lanes/Lib/Encoding/Json/Derive.lean`). A
  structure is an object of its fields, named as in Lean, a field encoded as `null` left out; a
  constructor is its name, or an object of one field, its name, holding the object of its
  arguments. Every field's type needs the three classes, and `Option α` needs `NonNullJson α`; a
  type parameter is given them.
- `ToCbor, FromCbor`, always together, give CBOR's instances and laws in the same way and the
  same shape, a structure a map with a text key per field
  (`Lanes/Lib/Encoding/Cbor/Derive.lean`). `import Lanes` does not import CBOR: a file that
  derives it imports `Lanes.Lib.Encoding.Cbor`.
- A `table` line declares a `TableOf` (`todos`) with its laws, and each index as
  `todos.byOwner`. The columns are the key's fields, then the others in order. Every field's type
  is a column (`Db.ColumnOf`, `Lanes/Db/Columns.lean`): `Int64`, `ByteArray`, `String`, `Bool`,
  or `Option` of one, nullable. PostgreSQL names are the Lean names in `snake_case`, an index's
  prefixed by its table's (`todos_by_owner`), unless a string gives one.
- `Enum` lists every value. `LawfulBEq` compares a structure field by field, for one that holds a
  function on an `Enum` type and so has no `DecidableEq`.
- Arguments are `(x y : T)` or `(x : T := default)`, fields `x : T` or `x : T := default`,
  each with an optional docstring; a constructor may be a keyword (`| open`). A value with a
  property is a subtype, read back only if the property holds. A field whose type names an
  earlier field is refused. `extends` and indices are not accepted: write those with `structure`
  or `inductive`, and the instances with `Json.Codec` and `Db.Columns`. A recursive type has no
  derived JSON: a codec is a value, and the command cannot define one that refers to itself.

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
`Lanes/Lib/`, and the protocol code of `Lanes/Web/` and `Lanes/Services/`: the wire format,
Signature Version 4, JOSE, S3's XML, PostgreSQL's messages) is compared with a reference
implementation on generated inputs, and every model of an outside service is checked against a
run recorded from a real or reference implementation; or
`oracles/README.md` says why not. *Why:* a proof says the code meets its spec, not that the
spec reads the standard, or the service, as others do.

Conventions:

- Prove a per-actor invariant with `actor_invariant [myActor]`; it leaves the cases it cannot close
  as goals. It lifts to every system under every fault model (`System.invariant_of_actor`). The
  goals quantify over the step's context (`ctx`, the moment `t` of a recovery): an actor that
  ignores it reduces `stepAt ctx` to its `step` by unfolding.
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
  again. The decisions' index, which is generated, never needs resolving: run `git config
  merge.generated.driver true` once (`.gitattributes` names it), and after a merge run `lake exe
  lanes lint --fix`, which writes it again.
- A new decision is a new file `docs/decisions/new-<slug>.md` whose first line is `# D?. Title`.
  Do not choose its number: whoever opens the pull request runs `lake exe lanes lint --fix --main`
  against the current main, which numbers it; CI on main refuses an unnumbered decision. If another
  open pull request took the same number, renumber the later one.
- A new claim goes in its area's table in `docs/ARCHITECTURE.md`, with its evidence, premises and
  status. A limit that can be fixed is an issue labelled `known-limit`; one the design accepts
  goes in its area's Limits there.
- No changelog entry: the changelog is written when a release is cut (`CONTRIBUTING.md`).
- Decide what is small or reversible yourself, and say what you chose in the pull request.
  Escalate to the owner only what changes direction, costs money, needs the owner's accounts, or
  cannot be undone, each with the choice you would make. A question already answered is a
  decision: record it, never ask it again.
- An axiom gate goes in `Tests/Axioms/<Area>.lean`, under the line naming its module; a lemma
  about lists at the end of its topic's file in `Lanes/Proof/List/`.
- Never type a count: the line counts in `TRUSTED.md` and the decisions' index are written by
  `lake exe lanes lint --fix`. Each generated line is about one
  item, and no committed file holds a total over the repository (`lake exe lanes stats` prints
  them), so two branches that change different items merge without a conflict. A conflict in a
  generated file is resolved by taking either side and running it.

## Docs

Agents do what the docs say, so a stale doc is worse than none. The rule is that each doc has
one job no other doc does:

- Each fact lives in one place. Elsewhere, point to it.
- A doc states rules and reasons, or it is generated or tested. `lanes lint` checks what it can
  (the decisions' index, the trusted sizes, every cited path, the oracles' list).
- Write so it will not go stale: name files and theorems, and avoid counts, dates and
  "currently" unless the number is the point.
- Work and status live in GitHub issues, not in docs: the direction is issue #93, a fixable
  limit is an issue labelled `known-limit`, and `docs/ROADMAP.md` only points there.

So:

- Change a doc in the same commit as the code it describes. A doc says what is, not how it came
  to be: history is in git and in `docs/decisions/`.
- `docs/ARCHITECTURE.md` has a section per area and per application: what it does, its claims
  with the theorem behind each (a claim without one says it is checked, tested or trusted), and
  the limits the design accepts.
- Cite files by their repository path in backquotes; `lanes lint` fails on one that does not
  exist (`docs/decisions/` is exempt: it records the past). Name a module that is not written
  yet by its module name (`Lanes.Lib.Encoding.Base32`), not its path.
- `docs/decisions/` is the record of why. Never rewrite a decision but for its status line: a
  new decision supersedes it, and changes the old one's line to `Status: Superseded by Dn` or
  `Status: Partly superseded by Dn (the part)`.
- Write plainly: short sentences, one name per concept, no marketing.

The design rules adapt TigerStyle, Ousterhout's deep modules, Erlang/OTP, crash-only software,
Lampson's hints, *Out of the Tar Pit*, *Parse, don't validate* and *Grokking Simplicity*.
