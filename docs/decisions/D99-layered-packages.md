# D99. Layered packages in one repository, one version, prebuilt builds (proposal)

Status: Accepted

This is the proposal of issue #101, item E of the design direction (#93). It is a proposal for
the owner to accept or edit, part by part. No file moves in this change. It adds
`scripts/layers.py`, which computes the import graph that sections 2 and 9 cite. The numbers
are measured on `origin/main` at `cb53031`.

The owner's framing: Lanes is the platform, the one dependency for building software in Lean,
as OTP and BEAM are for Erlang. Batteries are included. One `lanes` package installs
everything. Inside it are layers, and each works without the ones above it:

1. the semantics and the checker, for any state machine;
2. actors;
3. a runtime;
4. durability;
5. web, PostgreSQL and AWS.

The owner also decided that Mathlib and CSLib are removed from Lanes. They are used in only 5
files, all in `Lanes/Semantics/`. Lanes will own small replacements, and an application can still
`require mathlib` for its own proofs. No package of Lanes requires either of them (section 3).

This replaces the file moves of the closed #83 (its D90 proposal, on the branch
`claude/structure-proposal`). Those moves are folded into this split, so that each file moves
once (section 7).

## 1. The packages

All of them are in one repository and carry one version. The tag `vX.Y.Z` is the version of
every package. Each package is a directory `packages/<name>/` with its own `lakefile`. The
umbrella `lanes` stays at the root, so `require lanes` keeps meaning everything. Module names
keep the prefix `Lanes.`: a package owns its modules by its library's `globs`, not by a root
(section 4, experiment 4). So `import Lanes` and every `import Lanes.X` in an application stay
as they are.

| Package | Layer | Contents (paths inside the package) | Requires | Today: files, lines |
| --- | --- | --- | --- | ---: |
| `lanes-model` | 1 | `Lanes/Data/` (`Codec`, `Declare`, `Enum`, `Fifo`, `Quorum`, and `Frame` from `Lanes/Durable/`); the lemma library `Lanes/Proof/List/`, `Utf8`, `ByteArray`, `HashMap`; the checker's engine `Lanes/Check/Search`, `SearchSound`, `Fingerprint`; specs and refinement `Lanes/Semantics/Refinement`; the replacements of section 3 | nothing | 18, 4,285 |
| `lanes-actors` | 2 | `Lanes/Core/`; the rest of `Lanes/Proof/` (lifting, `Monotone`, ghosts, deeds, `JoinSound`, `MapIOSound`); the rest of `Lanes/Check/` (systems, monitors, reductions, fuzzing); `Lanes/Behaviours/`; the models of `Lanes/Outside/`; `Lanes/Semantics/` but for the three files that go elsewhere | `lanes-model` | 73, 22,834 |
| `lanes-runtime` | 3 | `Lanes/Runtime/`, with the kernel's log split from the journal (`Lanes/Runtime/Log.lean`); the courier as `Lanes/Peers/`; the clock's and the job pool's performers in `Lanes/Runtime/IO/`; `Lanes/Semantics/FairRuns`; the C of the parker | `lanes-actors` | 20, 10,711 |
| `lanes-durable` | 4 | `Lanes/Durable/` (journal files, snapshots, the disk model, migrations, upgrades); the C of `fsync` | `lanes-runtime` | 7, 2,172 |
| `lanes-std` | beside 2 | `Lanes/Lib/` (encodings and JSON, crypto, time, metrics, rate limits); `Lanes/Net/` (addresses, URLs, percent-encoding, TLS); the C of hashes, Argon2id, TLS, signatures | `lanes-model` | 30, 8,605 |
| `lanes-web` | 5 | `Lanes/Http/`, `Lanes/Html/`, `Lanes/Auth/`, `Lanes/S3/` (today all under `Lanes/Web/`); media types; a node with an HTTP front; `Lanes/Semantics/Front`; the test kit `Lanes/Testing/` as a second library | `lanes-durable`, `lanes-std` | 59, 18,327 |
| `lanes-postgres` | 5 | `Lanes/Postgres/` (today `Lanes/Lib/Postgres/`) | `lanes-runtime`, `lanes-std` | 11, 3,952 |
| `lanes-aws` | 5 | `integrations/aws`, moved | `lanes-web` | (its own) |
| `lanes-google`, `lanes-github` | 5 | `integrations/google`, `integrations/github`, moved | `lanes-web` | (their own) |
| `lanes` | all | the umbrella modules `Lanes.lean`, `Lanes/Proofs.lean`, `Lanes/Semantics.lean`; `LanesCli/` (the `lanes` command); `Tests/`, `examples/`, `templates/`, `docs/`, `oracles/`, `bench/`, `infra/` | every package above | 3, 228 |

`python3 scripts/layers.py --packages` prints the counts and the imports between packages.
`--moves` prints the old and new path of every file.

Choices made here, each open to the owner (section 11):

- **The standard library is a package of its own, beside the actors.** It needs only the lemma
  library. A user of layer 1 then gets no C and no OpenSSL. The web, PostgreSQL and, later,
  durability (the data format's checksums, #91) require it.
- **The web requires durability.** `Http.Front` takes snapshots (`Lanes/Web/Http/Front.lean`
  imports `Lanes.Durable.Snapshot`), the journal's name is the application's
  (`Lanes/Web/Http/JournalName.lean`), and the server opens the journal
  (`Lanes/Web/IO/Server.lean`). A front over a runtime with no journal is later work.
- **PostgreSQL does not require the web or durability.** Its handler runs on the runtime
  (`Postgres.Store.handler` takes a `Runtime sys`), and it needs TLS, which moves to `lanes-std`.
- **No separate proof package.** Rule 1.6 kept proofs apart because they linked Mathlib (D11:
  157 MB against 8 MB). Without Mathlib there is no such reason, so each package holds its own
  proofs, as the `…Sound` modules already sit beside their code.

## 2. The import graph today

`scripts/layers.py` reads the `import` lines of `Lanes/` and `Lanes.lean`, as `lanes lint`
does, so it needs no build. It reads each directory of today as the layer its concern belongs
to (`AREA`), and reports each import whose target is in a package that the importer's package
does not require, directly or below. With `HOME`, the place of each file after the moves of
this proposal, it reports what is left; `FIXES` gives the fix of each edge, and the script fails
on an edge with none.

Today there are 12 upward edges:

| Edge | Why it breaks | Fix |
| --- | --- | --- |
| `Lanes.Runtime.Batch` → `Lanes.Durable.Journal` | The runtime needs durability: a batch's acts are journal entries | Split `Lanes/Durable/Journal.lean`. Its pure log of the kernel (`Entry`, `ops`, `replay`, `recover`, `resume`, `Turn`, `turn`, `turnAll`: lines 28 to 40 and 253 to 594) moves to `Lanes/Runtime/Log.lean`, names kept. The bytes and files (`Entry.codec`, `write`, `read`, `open?`) stay. The shell already takes its storage as a parameter, `journal : Option (Journal.Log sys)` in `Lanes/Runtime/IO/Shell.lean`, and with `none` it runs with no journal |
| `Lanes.Runtime.Shard` → `Lanes.Durable.Frame` | The framing of shards' links is the journal file's | Move `Frame` to `Lanes/Data/Frame.lean`: it frames a file and a link, and imports `Std` only |
| `Lanes.Behaviours.Jobs.IO.Pool` → `Lanes.Runtime.IO.Shell` | An IO file of a behaviour performs on the runtime | Move the handler (`Port`, `handler`, `compute`) to `Lanes/Runtime/IO/Jobs.lean` |
| `Lanes.Behaviours.Jobs.IO.Pool` → `Lanes.Web.IO.Client` | The same file calls the HTTP client | Split: `withHeader` and `call` move to `Lanes/Http/IO/Jobs.lean` |
| `Lanes.Outside.IO.Clock` → `Lanes.Runtime.IO.Shell` | The clock's performer is under the models | Move to `Lanes/Runtime/IO/Clock.lean` |
| `Lanes.Semantics.FairRuns` → `Lanes.Runtime.KernelSound` | A proof about the kernel is among the actors' | Move to `lanes-runtime`, path kept |
| `Lanes.Semantics.Front` → `Lanes.Web.Http.FrontSound` | The gate's liveness is among the actors' | Move to `lanes-web`, path kept |
| `Lanes.Lib.Net.Url` → `Lanes.Web.Http.Basic` | URLs take percent-encoding from HTTP (D62 left it) | Move percent-encoding (`Http.percentDecode`, `Http.percentEncodeByte`, `Http.hexValue?`) to `Lanes/Net/Percent.lean`, names kept |
| `Lanes.Lib.Mime.MediaType` → `Lanes.Web.Http.Grammar` | Media types are RFC 9110's, written with HTTP's grammar | Move to `Lanes/Http/MediaType.lean` (#83's choice) |
| `Lanes.Lib.Postgres.IO.Client` → `Lanes.Web.IO.Tls` | PostgreSQL takes TLS from the web | Move TLS to `Lanes/Net/IO/Tls.lean`, in `lanes-std` |
| `Lanes.Net.IO.Node` → `Lanes.Web.IO.Server` | A node with an HTTP front is under the courier | Move to `Lanes/Http/IO/Node.lean` |
| `Lanes.Testing.Http` → `Lanes` | The test kit imports the umbrella | Import the modules of `lanes-web` it uses |

After the moves, 4 are left, each fixed by a split or by editing an import: the journal, the job
pool, percent-encoding and the test kit. Then the script reports none. The imports that are
downward stay as they are: the durable journal on the kernel (`Lanes.Durable.Journal` imports
`Lanes.Runtime.KernelSound` and `Lanes.Runtime.Wave`), PostgreSQL's handler on the shell, the
web on snapshots.

Two edges inside one package are worth fixing in the same work, as #83 found: the pure
`Lanes/Web/S3/Basic.lean` imports the IO module `Lanes/Web/IO/Client.lean` for the client's
data (`Client.Call`, `Scheme`, `Port`, `Config`), which would move out of its IO file; and
`S3.Endpoint.aws` and `S3.credentialsFromEnv` move to `lanes-aws` (the vendor rule, section 7).

There are 9 import lines of Mathlib or CSLib, in 5 files. Section 3 replaces them.

## 3. Mathlib and CSLib, removed

### What they are used for

A Lean script read every declaration of `Lanes/Semantics/` from the built modules, with its
proof, and listed the constants of Mathlib, CSLib, Batteries or Aesop that it uses: 265 of them,
in 13 of the 17 modules. The other 4 (`Front`, `History`, `Jobs`, `Schedule`) were not built in
the checkout the script read, and a search of their text found `Multiset` and
`Nat.le_induction`. The uses fall into eight groups:

| Use | Where | From | Replacement in `lanes-model` | Estimate |
| --- | --- | --- | --- | --- |
| Transition systems: `LTS`, `Tr`, `MTr`, `CanReach`, internal steps `HasTau` and its `Option` instance, `DecidableEqTau`, saturated steps `τSTr`, `STr`, `SMTr`, and `sTr_τSTr_iff`, `sMTr_τSTr_iff` | `Refinement`, `System`, `Simulation`, `Service`, `Monitor`, `MonitorSound`, `Once`, `Account`, `Liveness`, `Projection`, `FairRuns` | CSLib | `Lanes.Semantics.Lts`: the definitions, written again (CSLib is Apache-2.0, as Lanes is, so they can be ported with credit), with the 20 lemmas used | 300 lines |
| `Relation.ReflTransGen` | `Refinement`, `Monitor`, `Service`, `Once`, `Account` | Mathlib | An inductive and its 6 lemmas (`single`, `head`, `tail`, `trans`, `head_induction_on`, `refl`) | 60 lines |
| Infinite runs: `ωSequence`, `take`, `const`, `LeadsTo`, `leadsTo_trans`, `OmegaExecution` | `Liveness`, `Projection`, `FairJoin`, `FairRuns` | CSLib | Plain functions `Nat → α`, `take` as a list, leads-to and its transitivity. The statements of the liveness theorems then name no CSLib type, which #93 asked for | 100 lines |
| `Nat.segment` and `StrictMono` | `Projection`, `FairJoin` | CSLib, Mathlib | `StrictMono` on `Nat` with the 6 lemmas used, and the segment of a strictly increasing sequence with its 3 bounds | 120 lines |
| `Multiset`: `ofList`, `cons`, `+`, `erase`, `count`, `≤`, membership, and about 35 lemmas | `Service`, `Monitor`, `MonitorSound`, `Account`, `History`; and `examples/raft-kv`, `examples/ledger`, `examples/rookery`, `examples/kv-cache`, `Tests/BatchProofs.lean` (about 25 more lemmas) | Mathlib | `Lanes.Bag`: lists up to `List.Perm` (core Lean has the relation and 90 lemmas about it), with the same operations, `≤` read by counts, and the lemmas used. The largest piece | 500 lines |
| `Set`: insert, singleton, union, `⊆`, `ext` | `Liveness`, `MonitorSound`, `Once`, `FairRuns`; `examples/raft-kv/RaftKVProofs/Once.lean` | Mathlib | Predicates `α → Prop` and the few lemmas used | 60 lines |
| Sums: `Fintype`, `Finset.univ`, `∑`, `Finset.sum_congr`, `add_sum_erase`, `Function.update`, `List.sum_map_erase` | `Sums`; `examples/bank/Bank/Proofs.lean`, `Tests/Fixtures/BankProofs.lean`, `examples/raft-kv/RaftKVProofs/Refines.lean` | Mathlib | Sums over `Enum` (which lists every value): `Enum.sum`, and `sum_update` and `sum_map_erase` over `Int` | 100 lines |
| Algebra and order: `abel` (and `convert … <;> abel`), `norm_num`'s lemmas behind it, the instances of `Nat` as an ordered monoid, `LE.le.trans`, `le_rfl`, `add_comm`, `Nat.le_induction`, `Nat.strong_induction_on`, `List.reverseRecOn`, `List.Subperm` | `Sums`, `Account`, `Projection`, `FairJoin`, `Once`, `FairRuns`, `Front`, `Jobs`, `Schedule`; `examples/ledger` | Mathlib, Batteries | Core's `omega` and `grind` on `Int` and `Nat`, core's `Nat` lemmas, and 3 small inductions | 60 new lines, and edits of proofs |

In all, about 1,300 new lines in `lanes-model`. The edits: about 280 lines of `Lanes/Semantics/`
name one of these (of 6,721), about 120 lines of five examples, and about 20 of `Tests/`. Some
`simp` calls may have closed their goals with Mathlib's simp lemmas, and that shows only when
the files compile without it. That is the risk in the estimate. No executable code changes:
none of it imports Mathlib or CSLib today (lint `layering`).

What leaves the build: CSLib and the nine packages it brings (Mathlib, Batteries, Aesop, Qq,
ProofWidgets, Plausible, LeanSearchClient, import-graph and lean4-cli). The manifest becomes
empty. Each checkout no longer needs `lake exe cache get` or Mathlib's 7.2 GB in
`.lake/packages/mathlib` (measured in this container's main checkout). Rule 1.6's first half
goes, D10 and D11 are superseded, and the CSLib convention of a docstring on every declaration
of `Lanes/Semantics/` is no longer imposed.

An application that wants Mathlib requires it itself, at a version built for Lanes' toolchain
(below). A bridge package that relates `Lanes.Bag` to `Multiset`, `Enum.sum` to `Finset.sum`,
and `Lanes.Semantics.Lts` to CSLib's `LTS` can be written when an application asks for it.

### The toolchain

Today `lean-toolchain` is `leanprover/lean4:v4.37.0-rc1`, a release candidate, because CSLib's
pinned commit is built with it, and `AGENTS.md` says the toolchain follows CSLib's (D10). Once
neither is required, Lanes chooses its toolchain:

- **Pin stable releases only** (`v4.X.0`), and move to a new one deliberately, when CI passes on
  it. Release candidates are no longer forced on applications.
- **Wait until Mathlib has tagged the release.** Lake builds a workspace with one Lean, so an
  application that requires both Lanes and Mathlib needs a Mathlib built for Lanes' toolchain.
  Mathlib tags each stable release. With that rule, every Lanes version has a Mathlib to pair
  with, and the changelog names it.
- **What remains of the upgrade cost is Lean's own `Std`.** Lanes' proofs use its internals
  (`Lanes/Proof/HashMap.lean` imports `Std.Data.DHashMap.Internal.*`), and the HTTP server and
  the runtime use `Std.Async`.

## 4. Several packages in one repository: what Lake does

Lake supports this by `path` requirements inside the repository and, from outside it, a `git`
requirement with `subDir`. I checked each case with throwaway packages in `/tmp/pkgexp` on this
toolchain (Lake of `v4.37.0-rc1`). An application there required the repository from git by a
`file://` URL, which Lake treats like any other git URL.

| # | Experiment | Result |
| ---: | --- | --- |
| 1 | An umbrella at the root requires `core/` and `web/` by path; an application requires the umbrella from git | Works. The clone is `.lake/packages/lanes`, and the path packages are found inside it (`.lake/packages/lanes/web`) |
| 2 | An application requires `web` alone, from git with `subDir = "web"`; `web` requires `../core` by path | Works. `../core` is found in the same clone |
| 3 | An application requires `core` and `web` separately from git | Works, with two clones. **At different revisions, Lake builds `web` against the `core` the application names, and says nothing**: `web` of one commit ran with `core` of another |
| 4 | Two packages each own modules under `Lanes.` (`Lanes.Core.A`, `Lanes.Web.B`); the umbrella owns `Lanes` | Works if no library takes `Lanes` as a root. A root claims every module under it, so the umbrella's default library took `Lanes.Core.A`, looked for it in its own directory and failed. The umbrella's library has `roots = []` and `globs = ["Lanes"]`, and each package's library has `globs` such as `["Lanes.Core.+"]` |
| 5 | Packages whose sources stay in one tree: `packages/core/lakefile.toml` with `srcDir = "../.."` and disjoint `globs` | Works, with `lake build` and `lake setup-file`. Packages can then be declared before any file moves (section 10, step 9) |
| 6 | A module of `core` imports one of `web` | **The umbrella's build accepts it**, because Lake finds a module in any package of the workspace. Building `core` alone, as the root, fails. So CI builds each package alone, and `lanes lint` checks the table of packages |
| 7 | A package requires the umbrella by `path = "../.."` while the umbrella requires it | Lake accepts it and takes the root for `../..`. It works, and it makes the package depend on everything |
| 8 | `subDir = "packages/core"`, two levels down | Works. An application that requires only `core` cannot import a module of `web`: Lake reports that the `.olean` does not exist |

What this means for Lanes:

- **An application requires one package of Lanes**: the umbrella, or the one package it needs.
  Experiment 3 is the hazard of two. `lanes lint`, run in an application, can check that every
  package of Lanes in `lake-manifest.json` has the same URL and revision.
- **One version.** Each `lakefile` states `version`, and `lanes lint` checks that they are
  equal. A tag is a commit of the whole repository, so it pins every package at once.
- **Layering is checked twice**: by `lanes lint layering`, from the import lines and the table
  of packages, which is fast; and by a CI job that builds each package as its own root, which
  is what the user of one package sees (experiment 6).
- **Packages with C** (`lanes-std`, `lanes-runtime`, `lanes-durable`) keep a `lakefile.lean`,
  as the root has today, because TOML cannot build C. The others can be TOML. `native/lanes.c`
  splits in three: hashes, the comparison and Argon2id go to `lanes-std`, `lanes_park` and
  `lanes_unpark` to `lanes-runtime`, and `lanes_fsync` to `lanes-durable`. `native/tls.c`,
  `native/verify.c` and `native/sign.c` go to `lanes-std`.

## 5. Where the integrations go

Today `integrations/aws`, `integrations/google` and `integrations/github` each require `lanes`
by `path = "../.."` (`integrations/aws/lakefile.toml`). From outside the repository, an
application can require one from git with `subDir = "integrations/aws"`: `../..` is the root of
the same clone (experiment 2). But each then depends on the whole umbrella. And once the
umbrella requires them, so that `require lanes` installs AWS too, they require it back
(experiment 7).

Proposal:

- Move them to `packages/aws`, `packages/google` and `packages/github`, as `lanes-aws`,
  `lanes-google` and `lanes-github`.
- Each requires `lanes-web` by `path = "../web"`, never the umbrella. Their module names (`Aws`,
  `Google`, `GitHub`) stay as they are.
- The umbrella requires all three, so `require lanes` installs them, and `import Lanes` still
  imports none of them: an application imports `Aws` when it uses AWS.
- The vendor rule that #83 proposed (rule 1.8: protocols in Lanes, vendors in their packages)
  holds by package: `lanes-web` speaks S3 and Signature Version 4, and `lanes-aws` holds AWS's
  endpoints, credentials, SES, SQS and CloudFront. `S3.Endpoint.aws`
  (`Lanes/Web/S3/Basic.lean`) and `S3.credentialsFromEnv` (`Lanes/Web/IO/S3.lean`) move there.
- Their checks, oracles and fakes move with them. They run as now: `lake test` in each package,
  and its oracles against `oracles/`.

## 6. Prebuilt builds

### The cost today

A cold `lake build` of the repository took 18 min 44 s wall (14 min 1 s user), with Mathlib
from its cache (`build0.time` in the session's scratchpad; the machine is this container). That
build includes the tests and the tools. Of the module times Lake printed, Lanes' own modules
are 34 of 61 job-minutes, and its proofs (`…Sound` and `Lanes/Semantics/`) 13 of those. An
application builds all of Lanes: the template's proofs (`templates/app/Proofs.lean.tmpl`) import `Lanes.Semantics`, which
imports every soundness module. I did not time an application alone. Agents work in fresh
containers, so they pay this cost often.

### What Lake offers, from its source

The names below are from this toolchain's Lake (`src/lean/lake/` in the toolchain), not from
memory.

- **GitHub release archives.** Package options `releaseRepo`, `buildArchive` (by default
  `<name>-<target triple>.tar.gz`) and `preferReleaseBuild` (`Lake/Config/PackageConfig.lean`).
  `lake pack` and `lake unpack` make and open the archive of a package's build directory, and
  `lake upload <tag>` uploads it to an existing release with `gh`. A dependency with
  `preferReleaseBuild` is fetched from `<repo>/releases/download/<tag>/<buildArchive>`, where
  the tag is found by `git describe --tags --exact-match` (`Lake/Build/Package.lean`, lines 214
  to 223; `Lake/Util/Git.lean`). **It needs a tag at the exact commit.**
- **Remote artifact caches, by revision.** `lake build -o <file>` writes the mappings from
  inputs to outputs, and `lake cache put <file>` uploads them with the artifacts to an
  S3-compatible service, signed with SigV4 by `curl`, with the key from `LAKE_CACHE_KEY` as
  `id:secret`. `lake cache get` downloads them. A package names its service with
  `downloadCacheService` and declares it with `cache_service` (`[[cache_service]]` in TOML:
  `kind = "s3"`, `artifactEndpoint`, `revisionEndpoint`, `hasPackageScopes = false`), and turns
  on Lake's artifact cache with `enableArtifactCache`. A dependency so configured has its
  outputs fetched before it is built (`Package.maybeFetchBuildCache`). Lake looks the mappings up
  by the commit and, if none are there, by up to 100 earlier commits (`--max-revs`). The URL of
  a commit's mappings names the platform and the toolchain:
  `<revisionEndpoint>/pt/<target>/tc/<toolchain>/<commit>.jsonl`. **It needs no tag.**
- **Reservoir.** Builds are fetched from Reservoir without configuration only for packages of
  the scopes `leanprover` and `leanprover-community` (`Lake/Build/Package.lean`, lines 97 to
  100). Not for Lanes.
- **The local artifact cache.** With `enableArtifactCache`, outputs are stored once per
  toolchain in Lake's cache directory (`LAKE_CACHE_DIR`), and shared by every checkout on the
  machine. `restoreAllArtifacts` copies them back into `.lake/build` for tools that read them
  there. `LAKE_NO_CACHE=1` turns all of this off, and the build is from source.
- **CI artifacts and caches.** The Actions cache (which `.github/actions/lean/action.yml`
  already uses for `.lake/packages` and `.lake/build`) and workflow artifacts serve CI's own
  jobs. Downloading an artifact takes a GitHub token, so an application's build cannot use them.

### Checked by experiment

In `/tmp/pkgexp`, with a local HTTP server standing in for the service:

| # | Experiment | Result |
| ---: | --- | --- |
| 9 | A tagged commit with `preferReleaseBuild` and a `releaseRepo` whose release holds the archive made by `lake pack` | Downloaded and unpacked; the module was `Replayed`, not built |
| 10 | The same package at a commit with no tag | Built from source, with the warning "building from source; failed to fetch GitHub release". **`lake build --wfail` then fails**, and CI builds the examples with `--wfail` (`.github/workflows/ci.yml`) |
| 11 | `enableArtifactCache`, `downloadCacheService` and a `cache_service`; outputs uploaded with `lake build -o` and `lake cache put`; an application requires that untagged commit from git | `Fetched Core`: nothing built. The same through the umbrella, with the package as its path dependency |
| 12 | The application at a later commit whose outputs were not uploaded | Lake found the previous commit's mappings, built what had changed, warned of nothing, and `--wfail` passed |
| 13 | `LAKE_NO_CACHE=1` | Built from source; nothing was requested |
| 14 | A second application on the same machine, at a commit never uploaded, with the same Lake cache directory | `Reused Core`, with no network |

Not checked: the C targets of `lakefile.lean` (`buildO` and `moreLinkObjs`) with the artifact
cache, which may simply rebuild (seconds); a real S3 or R2 bucket (Lake signs for the region
`auto`, `Lake/Config/Cache.lean`, line 639, which R2 accepts; whether AWS S3 accepts it is not
checked); macOS; a `cache_service` written in a Lean `lakefile`.

### What works before the first tag

Only the owner tags, and `lanes new` pins the commit it was made from when there is no tag
(`New.pinned` in `LanesCli/New.lean`). Release archives give nothing to such an application, and
`preferReleaseBuild` would break its `--wfail` build (experiment 10). The artifact cache works for
every commit CI uploads (experiment 11):

1. **Now, with no service.** Set `enableArtifactCache` on Lanes' packages. Every checkout and
   application on one machine then shares one build of each module (experiment 14). This is
   most of the cost for agents: many worktrees in one container. Check first that
   `lanesInventory`, `docs/api`, `lanes lint` and CI's cache of `.lake/build` still find the
   outputs, or set `restoreAllArtifacts`.
2. **Then a public cache.** A bucket readable by anyone. CI, on each push to main, runs
   `lake build -o outputs.jsonl` for each package and `lake cache put`, for each platform it
   builds on. Each package of Lanes declares the service and names it in
   `downloadCacheService`. An application pinned to any commit of main then fetches Lanes. Each
   package needs its own pair of endpoints, because a `downloadCacheService` must have
   `hasPackageScopes = false`. If Lake's signing does not suit the bucket, `lake cache stage`
   writes the files to a directory, and any tool uploads them in the layout of experiment 11.
3. **After the first tag**, nothing more is needed: a tag is a commit, and its outputs are
   already uploaded. Release archives (`lake upload <tag>`) can be added for users who cannot
   reach the bucket, without `preferReleaseBuild`.

Trust: an application that fetches outputs trusts CI's build of Lanes' proofs. To check them,
`LAKE_NO_CACHE=1 lake build` builds from source, and `lake check` (in this toolchain) replays
the exported declarations through the kernel in a sandbox. `docs/RELEASING.md` should say both.

## 7. The moves of #83, folded in

#83 proposed moving files within `Lanes/`. Each of those moves now happens in the same pull
request that moves the files into their package, so that no file moves twice. The module renames
come with the moves; the namespaces do not follow paths (D62), so no public name changes.

| Today | After | #83 | Package |
| --- | --- | --- | --- |
| `Lanes/Web/Http/` (24 files) | `Lanes/Http/` | yes | `lanes-web` |
| `Lanes/Web/Http/SigV4.lean`, `SigV4Sound.lean` | `Lanes/S3/` | yes | `lanes-web` |
| `Lanes/Web/Html/` | `Lanes/Html/` | yes | `lanes-web` |
| `Lanes/Web/Auth/`, `Lanes/Web/IO/SignIn.lean` | `Lanes/Auth/`, `Lanes/Auth/IO/SignIn.lean` | yes | `lanes-web` |
| `Lanes/Web/S3/`, `Lanes/Web/IO/S3.lean` | `Lanes/S3/`, `Lanes/S3/IO/Client.lean` | yes | `lanes-web` |
| `Lanes/Web/IO/Server.lean`, `Client.lean`, `Ops.lean` | `Lanes/Http/IO/` | yes | `lanes-web` |
| `Lanes/Web/Transcode.lean` | `Lanes/Http/Transcode.lean` | (new since) | `lanes-web` |
| `Lanes/Lib/Mime/` | `Lanes/Http/` | yes | `lanes-web` |
| `Lanes/Lib/Net/`, `Lanes/Web/IO/Tls.lean` | `Lanes/Net/`, `Lanes/Net/IO/Tls.lean` | yes | `lanes-std` |
| Percent-encoding in `Lanes/Web/Http/Basic.lean` | `Lanes/Net/Percent.lean` | yes | `lanes-std` |
| `Lanes/Net/` (the courier) | `Lanes/Peers/`, after its namespace `Lanes.Peers` | its alternative | `lanes-runtime` |
| `Lanes/Net/IO/Node.lean` | `Lanes/Http/IO/Node.lean` | no | `lanes-web` |
| `Lanes/Lib/Postgres/` | `Lanes/Postgres/` | optional there | `lanes-postgres` |
| `S3.Endpoint.aws`, `S3.credentialsFromEnv` | `lanes-aws` | yes | `lanes-aws` |
| `Tests/Axioms/Web.lean` | one file per package's areas | yes | `lanes` |

The rest of #83 is done or decided: the generated documents and changelog fragments (#92), no
re-exporting modules at old paths, and deleting `examples/sign-in`, which is not a move and goes
on its own. #83's choice to keep the shared cache's model in `Lanes/Http/`, not `Lanes/Outside/`,
stands.

## 8. Perspectives

How other platforms that include their batteries are packaged, and what each suggests here.
Only what they publish about themselves is used; there are no quotes.

- **Go: the standard library, and `golang.org/x/`.** One distribution carries the language and a
  large library: HTTP, TLS, crypto, JSON, `database/sql` (an interface; drivers live outside),
  all released with the toolchain under the Go 1 compatibility promise. The `x/` repositories
  (`x/net`, `x/crypto`, `x/sync`) are by the same team but are separate modules with versions of
  their own and a looser promise. They hold what moves faster or is not yet ready for the
  standard library. For Lanes: one version for the core, and the option, later, to give the
  vendor packages (`lanes-aws`, `lanes-google`, `lanes-github`) a pace of their own if vendors
  change faster than Lanes releases. Unlike Go, Lanes ships its PostgreSQL client itself.
- **Rust, workspaces (tokio).** The tokio repository is a Cargo workspace of several crates
  (`tokio`, `tokio-util`, `tokio-stream`, `tokio-macros`, `tokio-test`), each published and
  versioned on its own. `tokio` also selects its parts with Cargo features (`rt`, `net`, `time`,
  `full`). For Lanes: Lake has no features, so the parts have to be packages, or libraries in one
  package; and separate versions bring a matrix of what works with what, which Lanes avoids with
  one version.
- **Rails.** One repository holds the gems: Active Support, Active Record, Action Pack, Action
  View, Active Job and the others, with `rails` a gem that depends on all of them. They are
  released together, under one version number. Several can be used alone, Active Record and
  Active Support most of all. This is the closest model to the owner's: an umbrella, parts usable
  alone, one version.
- **Phoenix.** The pieces are packages in separate repositories with versions of their own:
  `phoenix`, `phoenix_html`, `phoenix_live_view`, `phoenix_pubsub`, on Plug, and Ecto as a project
  of its own. The generator `mix phx.new` writes versions that work together. For Lanes: what one
  repository and one version save, a generator (`lanes new`) and documentation must otherwise do.
- **Erlang/OTP.** One release (OTP 27, for instance) holds the runtime system (ERTS) and the
  applications: `kernel` and `stdlib` at the bottom, then `ssl`, `crypto`, `public_key`, `inets`
  (an HTTP client and server), `mnesia` (a database), `sasl` and others. Each application has
  its own version and declares the applications it needs, and the release is tested and shipped
  as one. For Lanes: the layers map onto it (model and actors as kernel and stdlib, the runtime
  as ERTS and its scheduler, durability as Mnesia's logs, web and PostgreSQL as `inets` and
  `ssl`), and Lanes is simpler still, with one version for all.

## 9. Costs

From `python3 scripts/layers.py --cost`, counting the hand-written files that would change
(`docs/decisions/` and `docs/history/` keep the old paths; the generated files are rewritten by
`lanes lint --fix`):

- **218 files move** into `packages/`, and 73 of them get a new module name (section 7). Three
  files split in two (the journal, the job pool, HTTP's `Basic`). The umbrella's 3 modules stay.
- **173 import lines** name a renamed module, all in `Lanes/` and `Tests/`. No example,
  integration, template, benchmark or `docs/api` imports one: they import `Lanes`,
  `Lanes.Semantics`, `Lanes.Testing` or three JSON proof modules, which keep their names.
- **614 references to an old path and 69 to an old module name**, outside import lines, in 133
  files with the moved ones: `docs/` (236 lines: `docs/ARCHITECTURE.md`, `docs/CLAIMS.md`,
  `docs/STDLIB.md`, `docs/inventory-none.md`, the status fragments), `Lanes/` (163, comments and
  docstrings), `scripts/mutants.py` (93), `oracles/README.md` (80), `Tests/` (73), `Lanes.lean`
  (53), `TRUSTED.md` (40), `examples/` (16), `AGENTS.md` (6), `bench/` (4). All are mechanical:
  one table of old and new paths, applied by a script.
- **New files**: about 10 `lakefile`s, the `native/` split, CI jobs that build each package
  alone. The lint's `layering` and `oracles` checks read paths (`LanesCli/Lint.lean`, the
  protocol directories `Lanes/Lib` and `Lanes/Web`), and `AGENTS.md`'s layout table becomes
  one table per package.
- **Mathlib and CSLib**: about 1,300 new lines and 400 edited (section 3).

What a merge costs: a pull request that edits a moved file still merges, because git follows a
rename. One that adds a file in a moved directory has to move it.

## 10. The order of work

Each step is one pull request of one kind, small, with the build green at each. A move is
opened when no open pull request adds files to what it moves.

| Step | Pull request | Size | After |
| ---: | --- | --- | --- |
| 1 | `enableArtifactCache` in `lakefile.lean`, with `restoreAllArtifacts` if a tool needs the outputs in place | a few lines; check the tools and CI's cache | nothing |
| 2 | Replace CSLib's transition systems and `ReflTransGen` (`Lanes.Semantics.Lts`) | about 360 lines, 10 files edited | nothing |
| 3 | Replace ω-sequences, segments and `StrictMono`; drop `require cslib` | about 220 lines, 4 files edited | 2 |
| 4 | `Lanes.Bag` for `Multiset`, predicates for `Set`, in Lanes, the examples and the tests | about 560 lines, 12 files edited | 3 |
| 5 | Sums over `Enum`, `abel` to `omega` and `grind`; drop Mathlib; the manifest is empty; rule 1.6, D10, D11, `AGENTS.md`, `README.md`, the tutorials and CI's action lose `lake exe cache get` | about 160 lines and docs | 4 |
| 6 | The toolchain moves to a stable release that Mathlib has tagged | one line, and what breaks | 5 |
| 7 | Splits with no move of a whole file: `Lanes/Runtime/Log.lean` from the journal, `Frame` to `Lanes/Data/`, percent-encoding to its own file, the job pool in two, the test kit's imports. `scripts/layers.py` then reports no edge left | moves of definitions, names kept | the data-format work (#91), if it rewrites the journal first |
| 8 | `lanes lint layering` reads a table of packages, and CI runs `scripts/layers.py` until it does | about 100 lines in `LanesCli/` | 7 |
| 9 | The packages declared, with no file moved: `packages/<name>/lakefile` with `srcDir = "../.."` and the globs of `HOME` (experiment 5); the umbrella requires them; CI builds each alone | about 10 small files | 8 |
| 10 | Moves, one package per pull request, from the bottom: `lanes-model`, `lanes-actors`, `lanes-runtime`, `lanes-durable`, `lanes-std`, `lanes-postgres`, then `lanes-web` (HTTP last, since it is where most branches work). Each sets its `srcDir` back to its own directory, applies section 7's renames, splits its share of `native/lanes.c`, and rewrites the references | moves | 9 |
| 11 | The integrations to `packages/`, each on `lanes-web`; the vendor rule, and `S3.Endpoint.aws` and `S3.credentialsFromEnv` to `lanes-aws` | moves and about 40 lines | 10 |
| 12 | `lanes lint` checks one version across the packages, and, in an application, one URL and revision for every package of Lanes | about 60 lines | 10 |
| 13 | The public cache: a bucket, CI uploads on each push to main, each package names the service | CI and a few lines per package | 10, and the owner's bucket |
| 14 | CI makes an application from git, as a user does (`lanes new` without `--lanes-path`), and times its build with the cache | one job | 13 |

Steps 2 to 6 and step 7 touch different files and can go in parallel. Step 10's pull requests
are queued one after another, each built on the last.

## 11. Details settled

Each detail below is settled at the default it states (the owner's rule: small and reversible choices are taken at their default, and changed later if needed).

Each with the default this proposal takes.

1. **Names**: `lanes-model`, `lanes-actors`, `lanes-runtime`, `lanes-durable`, `lanes-std`,
   `lanes-web`, `lanes-postgres`, `lanes-aws`, `lanes-google`, `lanes-github`, and `lanes` for
   the umbrella? *Default: these.*
2. **Layer 1's contents**: the data types and codecs, the lemma library, the checker's engine
   over any transition system (`Check.Search`, which knows nothing of actors), and specs with
   refinement and temporal logic? *Default: yes. The checks of actor systems are layer 2.*
3. **The standard library** as its own package beside the actors, needing only layer 1?
   *Default: yes.*
4. **The web on durability**, as today? *Default: yes; a front with no journal is later work.*
5. **Where packages live**: each in `packages/<name>/` with its own `Lanes/…` subtree (218 moves),
   or every package's sources in the one `Lanes/` tree (`srcDir = "../.."`, no moves)?
   *Default: their own directories, with the shared tree only as the step between.*
6. **#83's renames in the same moves**, `Lanes/Web/` into `Http`, `Html`, `Auth` and `S3`, the
   courier to `Lanes/Peers/`, and `Lanes/Lib/Postgres/` to `Lanes/Postgres/`? *Default: yes.*
7. **The test kit**: a second library of `lanes-web`, or a package of its own? *Default: a
   library of `lanes-web`, outside `import Lanes`, as D77 has it.*
8. **Google and GitHub**: packages of their own, or presets inside `lanes-web`? *Default:
   packages of their own, so vendors stay out of the web package.*
9. **Proofs beside their code** in each package, with no proof package, and rule 1.6 rewritten
   as "a package imports only the packages it requires"? *Default: yes. Measure a binary's size
   after Mathlib leaves, to confirm.*
10. **The toolchain**: stable releases only, moved when Mathlib has tagged them? *Default: yes.*
11. **A bridge to Mathlib and CSLib**, as an optional package? *Default: no, until an
    application asks.*
12. **The public cache**: where (a bucket in the AWS account CI runs in, or Cloudflare R2), and
    a write key for CI as a secret? *Default: a bucket in the existing AWS account, if Lake's
    signing works with it; otherwise R2.*
13. **Platforms to prebuild**: Linux x86-64, and macOS on ARM if CI builds there? *Default:
    both.*
14. **Release archives** at tags, with `preferReleaseBuild` off? *Default: none at first; the
    cache serves tags too.*
15. **One package per application**: should `lanes lint` refuse an application that requires
    two packages of Lanes at different revisions? *Default: yes.*
