# Working on Lanes

Lanes is a framework for building verified software in Lean 4: actors with pure step functions, one
semantics, a model checker, proofs, and adapters. Read `docs/DESIGN.md` for the plan,
`docs/STATUS.md` for what exists, `docs/ROADMAP.md` for the phases ahead, `docs/PLAN.md` for what
is being done next and why, and
`LANES_STYLE.md` for the rules. `docs/DECISIONS.md` records where the implementation settled or
departed from the design document, with reasons.

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
lake exe lanes lint  # LANES_STYLE checks
```

The toolchain is pinned in `lean-toolchain` and follows CSLib's. Dependencies are pinned in
`lake-manifest.json`; upgrade them deliberately, CSLib first.

## Layout

| Path | Contents | May import |
| --- | --- | --- |
| `Lanes/Actors/` | `Actor`, `Signature`, `Effect`, `System`, the world step function, scheduler, runtime | `Std` only |
| `Lanes/Data/` | Small data utilities (`Enum`, list lemmas in `List`), codecs and `lanes_data` (`Codec`, `Declare`), the JSON library (`Json`), SHA-256, HMAC and PBKDF2 (`Sha256`, `Hmac`) | `Std` only |
| `Lanes/Auth/` | Signed tokens, form tokens, password digests, failed attempts, sessions | `Std` only |
| `Lanes/Check/` | Model checker | `Std` only |
| `Lanes/Http/`, `Lanes/Html/` | HTTP requests and responses as data; HTML values and template syntax | `Std` only |
| `Lanes/Env/` | Adapters to the outside world (HTTP server) | `Std` only |
| `Lanes/Semantics/` | The semantics as a CSLib `LTS`, refinement, fairness and leads-to | CSLib, Mathlib |
| `LanesCli/` | The `lanes` command: `new`, `lint`, `check` | `Std` only |
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
  private or not. Facts about lists go in `Lanes/Data/List.lean`; about `update`, `SysState`,
  `run` and `Reachable` beside their definitions in `Lanes/Actors/World.lean`; a step or a run
  in closed form in `Lanes/Actors/Run.lean`; `NetEquiv` and `SysState.Equiv` in
  `Lanes/Actors/Equiv.lean`. Look there, and in core `List`, before proving a helper.
- A layer of a `Monotone` proof that reads states and messages in flight is added with
  `Monotone.and_net` (or `and_state`), not with `below` and `input` lemmas of its own; a stack
  of more than two layers gets a structure through `Monotone.of_iff`.
