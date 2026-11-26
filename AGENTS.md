# Working on Lanes

Lanes is a framework for building verified software in Lean 4: actors with pure step functions, one
semantics, a model checker, proofs, and adapters. Read `docs/DESIGN.md` for the plan,
`docs/STATUS.md` for what exists and what is next, and `LANES_STYLE.md` for the rules. `docs/DECISIONS.md` records where the implementation settled or
departed from the design document, with reasons.

## Lanes rules for agents

- Read LANES_STYLE.md before writing code. Cite rule numbers in PR descriptions when a rule shaped a choice.
- Write or update the spec first; model-check it before writing the implementation or a proof.
- step is pure: no IO. New external work = new Effect constructor + response message.
- Encode invariants in types first, theorems second, runtime asserts only at adapters.
- Never add sorry, partial, unsafe or an axiom without listing it in TRUSTED.md.
- On an unexpected state, emit stop; do not add defensive fallbacks.
- Run `lake build && lake test` before claiming a task is done.

## Build

```bash
lake exe cache get   # prebuilt Mathlib; never build Mathlib from source
lake build           # the library
lake test            # checker, scheduler, runtime and example regression tests
lake exe lanes lint  # LANES_STYLE checks
```

The toolchain is pinned in `lean-toolchain` and follows CSLib's. Dependencies are pinned in
`lake-manifest.json`; upgrade them deliberately, CSLib first.

## Layout

| Path | Contents | May import |
| --- | --- | --- |
| `Lanes/Actors/` | `Actor`, `Signature`, `Effect`, `System`, the world step function, scheduler, runtime | `Std` only |
| `Lanes/Data/` | Small data utilities (`Enum`) and the JSON library (`Json`) | `Std` only |
| `Lanes/Check/` | Model checker | `Std` only |
| `Lanes/Http/`, `Lanes/Html/` | HTTP requests and responses as data; HTML values and template syntax | `Std` only |
| `Lanes/Env/` | Adapters to the outside world (HTTP server) | `Std` only |
| `Lanes/Semantics/` | The semantics as a CSLib `LTS`, refinement | CSLib, Mathlib |
| `LanesCli/` | The `lanes` command: `new`, `lint`, `check` | `Std` only |
| `templates/app/` | The application `lanes new` creates; embedded in the `lanes` binary | |
| `Examples/` | Reference apps, checked and proved | anything |
| `Tests/` | Regression tests run by `lake test` | anything |

Runtime modules never import Mathlib or CSLib (design decision 5). `import Lanes` is the runtime
layer and gives a binary of a few megabytes; `import Lanes.Semantics` is the proof layer.
Importing the proof layer from executable code links all of Mathlib into the binary (over 150 MB),
and Mathlib's `<i` token breaks `<input>` in templates, so keep views and `main` on `import Lanes`.

## Conventions

- Library files use the module system: `module`, `public import`, then `@[expose] public section`
  (as CSLib does). A definition whose body uses private helpers is marked `@[no_expose]`.
- Every declaration and structure field has a docstring. Each file opens with a `/-! -/` module
  docstring stating what it defines.
- One actor step handles one message. Branch on the message once, at the top (rule 4).
- Define a concrete system with `abbrev`, so instance resolution can see its `State`.
- Prove per-actor invariants with `actor_invariant [myActor]`; it leaves the cases it cannot
  close as goals.
- Template syntax is scoped: a view file starts with `open scoped Lanes.Html`. Inside it, a tag
  name follows `<` with no space (`<div>`); `a < b` with a space is a comparison.
- In `do` blocks, `(← action)` inside `a || b` or `a && b` runs whether or not the other side
  decides the result. Bind it first when it must be conditional.
- Templates are embedded with `include_str`, which Lake does not track: after editing
  `templates/`, touch `LanesCli/New.lean` and rebuild `lanes`. CI builds a generated app.
- Check before you prove: every invariant gets an `always` property and a `sometimes` vacuity
  check in a test before its proof is attempted (rules 5.1, 5.3).
