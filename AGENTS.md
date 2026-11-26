# Working on Lanes

Lanes is a framework for building verified software in Lean 4: actors with pure step functions, one
semantics, a model checker, proofs, and adapters. Read `docs/DESIGN.md` for the plan,
`docs/STATUS.md` for what exists, `docs/ROADMAP.md` for the phases ahead, `docs/PLAN.md` for what
is being done next and why, and
`LANES_STYLE.md` for the rules. `docs/decisions/` records where the implementation settled or
departed from the design document, with reasons, one file per decision.

## Lanes rules for agents

- Read LANES_STYLE.md before writing code. Cite rule numbers in PR descriptions when a rule shaped a choice.
- Write or update the spec first; model-check it before writing the implementation or a proof.
- step is pure: no IO. New external work = new Effect constructor + response message.
- Encode invariants in types first, theorems second, runtime asserts only at adapters.
- Never add sorry, partial, unsafe or an axiom without listing it in TRUSTED.md.
- On an unexpected state, emit stop; do not add defensive fallbacks.
- Run `lake build && lake test && lake exe lanesCheck` before claiming a task is done.

## Build

```bash
lake exe cache get   # prebuilt Mathlib; never build Mathlib from source
lake build           # the library
lake test            # pure tests and live runtime tests, a few seconds
lake exe lanesCheck  # larger model checks, random runs and the scale benchmark, about 20 s: run once, never in a loop
lake exe lanes lint  # LANES_STYLE checks, and that generated files are up to date
lake exe lanes lint --fix  # rewrite the generated files: line counts, decisions' index, STATUS, INVENTORY
lake exe lanes inventory --list none  # the definitions of Lanes/ without evidence
```

`docs/INVENTORY.md` gives every public definition a status, read from the built modules
(`docs/decisions/D47-the-inventory-is-computed.md`). A theorem makes what it states proved when
it has an axiom gate. A new definition of `Lanes/` with no theorem, test or row of `TRUSTED.md`
fails `lanes lint` unless it is on `docs/inventory-none.md` under a heading that says why; when
one there gets evidence, take it off.

A parser or format is also tested against Go's standard library
(`docs/decisions/new-differential-tests-against-go.md`): `oracle/<package>/main.go` answers the
cases that `Tests/Oracle/<Package>.lean` generates, and every difference is either a `known`
predicate there, with its reason, or a failure. `lake exe lanesOracle --cases 100000` asks Go
(it needs `go`, at the version `oracle/go.mod` pins); `lake test` replays the answers recorded in
`Tests/Oracle/vectors/`, which `lake exe lanesOracle --cases 1000 --record` rewrites.

## Parallel branches

Several agents work at once, each on a branch that is merged into the main branch. The layout
gives independent changes disjoint files; keep it that way.

- Commit after every step that builds.
- Before reporting, merge the main branch and run the checks again. Generated files
  (`docs/STATUS.md`, `docs/INVENTORY.md`, the decisions index) never need resolving: run
  `git config merge.generated.driver true` once, and after a merge run
  `lake exe lanes lint --fix`, which writes them again.
- A new decision is a new file `docs/decisions/new-<slug>.md` whose first line is
  `# D?. Title`. Do not choose its number: `lake exe lanes lint --fix --main` numbers it on the
  main branch after the merge.
- A change of status goes in its area's fragment, `docs/status/areas/<area>.md` or
  `docs/status/apps/<app>.md` (the row on the first line, the area's known limits after it).
  `docs/STATUS.md` is generated; do not edit it.
- An axiom gate goes in `Tests/Axioms/<Area>.lean`, under the line naming its module; a lemma
  about lists at the end of its topic's file in `Lanes/Data/List/`.
- Never type a count: the line counts in `TRUSTED.md` and `README.md` are written by
  `lake exe lanes lint --fix`. A conflict in a generated file is resolved by taking either side
  and running `lake exe lanes lint --fix`.

The toolchain is pinned in `lean-toolchain` and follows CSLib's. Dependencies are pinned in
`lake-manifest.json`; upgrade them deliberately, CSLib first.

## Seeing a goal without a rebuild

`scripts/lean-goals` asks the Lean language server for a file's errors and the goals at some of
its lines, so a proof can be worked on without rebuilding the file each time:

```bash
scripts/lean-goals --daemon Lanes/Http/WireSound.lean 1710 1702:4   # start a server, ask it
scripts/lean-goals Lanes/Http/WireSound.lean 1710                   # later calls use it
scripts/lean-goals --stop                                            # when done
```

`LINE` counts from 1 and `COL` from 0, as in Lean's messages; without `COL` it prints the goals
before and after the line. The daemon keeps the file open: after an edit it elaborates again
only from the first changed command, so an edit near the end of `WireSound.lean` takes half a
second instead of the six of `lake env lean` (measured under load 9 here). The first call costs a
full elaboration. A daemon belongs to the package that holds the file (its socket is that
package's `.lake/lean-goals.sock`, so each worktree has its own), builds the file's imports when
they are out of date, and stops by itself after an hour unused. It reopens a file whose imports
Lean reports out of date; `--reopen` forces that. It does not replace `lake build` before a
commit.

## Layout

| Path | Contents | May import |
| --- | --- | --- |
| `Lanes/Actors/` | `Actor`, `Signature`, `Effect`, `System`, the world step function, scheduler, runtime | `Std` only |
| `Lanes/Data/` | Small data utilities (`Enum`; lemmas about lists in `List/`, strings in `Utf8` and byte arrays in `ByteArray`), codecs and `lanes_data` (`Codec`, `Declare`), the JSON library (`Json`), SHA-256 and HMAC in Lean (`Sha256`, `Hmac`), the references of what `Sodium` binds from libsodium | `Std` only |
| `Lanes/Auth/` | Signed tokens, form tokens, password digests, failed attempts, sessions | `Std` only |
| `native/` | The C that binds libsodium and `fsync` (`lanes.c`), every line of it trusted and counted in `TRUSTED.md` | libsodium, the C library |
| `Lanes/Check/` | Model checker | `Std` only |
| `Lanes/Http/`, `Lanes/Html/` | HTTP requests and responses as data; HTML values and template syntax | `Std` only |
| `Lanes/Env/` | Adapters to the outside world (HTTP server) | `Std` only |
| `Lanes/Semantics/` | The semantics as a CSLib `LTS`, refinement, fairness and leads-to | CSLib, Mathlib |
| `LanesCli/` | The `lanes` command: `new`, `lint`, `check`, `inventory` | `Std` only; `Lean` in `Inventory`, which only `lanesInventory` links |
| `templates/app/` | The application `lanes new` creates; embedded in the `lanes` binary | |
| `Examples/` | Reference apps, checked and proved | anything |
| `Tests/` | Regression tests run by `lake test` | anything |

Runtime modules never import Mathlib or CSLib (design decision 5). `import Lanes` is the runtime
layer and gives a binary of a few megabytes; `import Lanes.Semantics` is the proof layer.
Importing the proof layer from executable code links all of Mathlib into the binary (over 150 MB),
and Mathlib's `<i` token breaks `<input>` in templates, so keep views and `main` on `import Lanes`.

## Declaring a type for a system

Declare the messages, inputs, outputs and states of a system with `lanes_data`. It is the
ordinary declaration with a prefix, and its `deriving` clause also takes three classes Lean
cannot derive without linking `Lean` into the binary:

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

- `Codable` gives `Entry.codec : Codec N → Codec C → Codec (Entry N C)` and
  `instance [Codable N] [Codable C] : Codable (Entry N C)`; `Codec.of T` is the instance's codec.
  Every field's type needs a `Codable` instance: `Nat`, `Int`, `String`, `Bool`, `Unit`,
  `ByteArray`, `Fin n`, `Option`, `List`, pairs, sums, sigma types, subtypes, `Std.ExtTreeMap`,
  and types declared this way. The law holds by construction (`Codec.struct%`, `Codec.sum%`).
- `Enum` lists every value, from `Enum` instances of the constructors' arguments.
- `LawfulBEq` gives a structure a `BEq` that compares field by field, and its law, for a structure
  that holds a function on an `Enum` type and so has no `DecidableEq`. A type parameter that is a
  field's whole type is compared with its own `BEq`; any other needs `DecidableEq`.

Constructor arguments are written `(x y : T)`, fields `x : T` or `x : T := default`, each with
an optional docstring; a constructor may be named by a keyword (`| open`). A value with a
property is a subtype, `name : {s : String // valid s}`: it is written as the value and read back
only if the property holds. A field whose type names an earlier field, such as a proof about it,
is refused by the three classes above. `extends`, indices and recursive types are not accepted:
declare those with `structure` or `inductive` and write the codec with `Codec.struct%` or
`Codec.sum%`.

A family of instances defined by cases on an identity, such as `∀ i, DecidableEq (Msg i)` or the
`Inspect` of a system whose actors have different messages or states, is `by instance_by_cases`.

## Conventions

- Library files use the module system: `module`, `public import`, then `@[expose] public section`
  (as CSLib does). A definition whose body uses private helpers is marked `@[no_expose]`.
- Write almost no comments. A comment or docstring is for a *why* that a name, a type or a
  theorem cannot carry. Never restate what the code says, and never narrate a change. If code
  needs explaining, rename or restructure it. Each file keeps a short `/-! -/` header saying what
  it is for; a public declaration gets a docstring only when its name and type do not already
  say what it is. Do not copy the docstring density of older files: it is being removed.
  Exception: `Lanes/Semantics/` documents every declaration, because CSLib's linter requires it.
- One actor step handles one message. Branch on the message once, at the top (rule 4).
- Define a concrete system with `abbrev`, so instance resolution can see its `State`.
- Prove per-actor invariants with `actor_invariant [myActor]`; it leaves the cases it cannot
  close as goals.
- Template syntax is scoped: a view file starts with `open scoped Lanes.Html`. Inside it, a tag
  name follows `<` with no space (`<div>`); `a < b` with a space is a comparison.
- In `do` blocks, `(← action)` inside `a || b` or `a && b` runs whether or not the other side
  decides the result. Bind it first when it must be conditional.
- Lean never updates an object in place once another thread may see it, and state held across
  an `await` is handed to the task system. Hot state (a kernel, a table) lives on one thread, in
  an `IO.Ref` used through `modifyGet`; an `Async` loop would copy it on every update.
- Take pairs apart by pattern (`let (a, b) := f x`), not with `.1` and `.2`, where the first
  part is large state that is then updated: a projection keeps the pair, and so the state, alive.
- An instance stated over an abstract signature (`[σ.Inspect] : (joinSig σ τ).Inspect`) is not
  found for a concrete one: the concrete signature is an `abbrev`, instance search unfolds it,
  and `σ.Msg i` no longer matches. Write such instances as named definitions and give them in
  one line: `instance : (joinSig a b).Inspect := .join`.
- Templates are embedded with `include_str`, which Lake does not track: after editing
  `templates/`, touch `LanesCli/New.lean` and rebuild `lanes`. CI builds a generated app.
- Check before you prove: every invariant gets an `always` property and a `sometimes` vacuity
  check in a test before its proof is attempted (rules 5.1, 5.3).
- A lemma that does not mention the system a proof is about does not stay in that proof's file,
  private or not. Facts about lists go in `Lanes/Data/List/`, at the end of the file of their
  topic (`Erase`, `Prefix`, `Fold`, else `Basic`); about strings and byte arrays in
  `Lanes/Data/Utf8.lean` and `Lanes/Data/ByteArray.lean`; about `update`, `SysState`,
  `run` and `Reachable` beside their definitions in `Lanes/Actors/World.lean`; a step or a run
  in closed form in `Lanes/Actors/Run.lean`; `NetEquiv` and `SysState.Equiv` in
  `Lanes/Actors/Equiv.lean`. Look there, and in core `List`, before proving a helper.
- A layer of a `Monotone` proof that reads states and messages in flight is added with
  `Monotone.and_net` (or `and_state`), not with `below` and `input` lemmas of its own; a stack
  of more than two layers gets a structure through `Monotone.of_iff`.
