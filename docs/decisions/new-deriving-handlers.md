# D?. Lanes' derivations can be deriving handlers, once applications are modules

Status: Proposed

Issue #239 asks whether the word `lanes_data` can go: people would write a plain `structure Todo …
deriving ToJson, FromJson` and get the proved instances. D38 put the declaration inside a
command because a deriving handler needs `Lean.Elab`, and D15 recorded that `public meta import
Lean` still gives a 137 MB binary. A spike on Lean v4.37.0-rc1, in `scratch/deriving-spike/`,
finds that this holds only for an executable whose root file is not a `module`. When the root is
a module, a handler module imported with `meta import` adds none of `Lean` to the binary, and
Lanes' derivations work as handlers with the same output.

## What was measured

`scratch/deriving-spike/lakefile.lean` builds each program below with `lake build -v`. The sizes
are of the linked binaries; "`Lean.Elab`" counts the symbols `nm` lists that contain
`l_Lean_Elab`.

| Program | Root file | How it reaches `Lean` | Size | `Lean.Elab` |
| --- | --- | --- | --- | --- |
| `byHand` | module | not at all (toolchain only, instance by hand) | 4.1 MB | 0 |
| `withHandler` | module | `meta import Spike.Derive`, a handler for a toy class | 9.4 MB | 0 |
| `plainImport` | module | `import Spike.Derive` | 9.4 MB | 0 |
| `wholeLean` | module | imports a module that does `public meta import Lean` (D15's set-up) | 9.5 MB | 0 |
| `importLean` | module | `import Lean` | 136.6 MB | 28700 |
| `lanesData` | module | not at all: Lanes types declared with `lanes_data` | 10.40 MB | 0 |
| `lanesHandler` | module | the same types as plain declarations, `meta import Spike.Lanes` | 10.44 MB | 0 |
| `viaPrelude` | module | `import Spike.Prelude`, which does `public meta import Spike.Lanes` | 10.44 MB | 0 |
| `notModule` | not a module | `viaPrelude`'s file without its `module` line | 137.4 MB | 28700 |

- The handler runs. `deriving Spike.Describe` and, on Lanes, `deriving ToJson, FromJson, Enum`
  and a table elaborate, and `lanesHandler`, `viaPrelude` and `notModule` print exactly what
  `lanesData` prints (`diff` of their output is empty): the same JSON, round trips, `Enum`
  sizes and table and index names.
- Lake links the handler's object anyway: `withHandler.rsp` lists
  `.lake/build/ir/Spike/Derive.c.o.export`, and every executable's link line, `byHand`'s too,
  has `-lLean`. Nothing of it stays, because the linker keeps only what `main` reaches
  (`--gc-sections`), and in a module `main` calls `runtime_initialize_<root>`, which initializes
  the runtime imports only. `WithHandler.c` shows it: `Spike.Derive` appears in
  `meta_initialize_spike_WithHandler` and `initialize_spike_WithHandler`, never in
  `runtime_initialize_spike_WithHandler`.
- A file that is not a module has no such split: its `main` calls `initialize_<root>`, which
  initializes every import, meta ones included (`NotModule.c`: `initialize_spike_NotModule` calls
  `initialize_spike_Spike_Prelude`, which calls `initialize_spike_Spike_Lanes`). So all of
  `Lean` is linked. That is the 137 MB D15 measured.
- The 5 MB between `byHand` and `withHandler` is OpenSSL (`nm` lists 0 `ossl_` symbols in
  `byHand`, 2469 in `withHandler`), which the toolchain's archives bring once any of their
  members is linked. Every Lanes application links it already (2469 in `lanesData`).
- On Lanes the handlers cost 47 KB (`lanesHandler` over `lanesData`), and every symbol that
  differs is the application's own code (`lp_spike_…`), none of `Lean` or of the handler module.
- Elaborating `LanesHandler.lean` took 0.84 to 0.89 s against 0.70 to 0.79 s for
  `LanesData.lean` (three runs of `lean` each): the handler's imports are loaded, and its own
  code is interpreted.

Two rules of the module system bound this. A file that is not a module cannot write `meta
import` (`cannot use 'meta import' without 'module'`), and a module cannot import a file that is
not one (`cannot import non-'module' Mid from 'module'`). So an application that wants the
handlers without `Lean` in its binary has every file of the executable on the module system.

## How ours would be picked

A handler is registered for a class's full name (`registerDerivingHandler`,
`Lean/Elab/Deriving/Basic.lean`), and `deriving C` resolves `C` as a name
(`realizeGlobalConstNoOverloadWithInfo`). Our classes are `Lanes.ToJson`, `Lanes.FromJson` and
`Lanes.Enum`, other names than Lean's `ToJson`, so their handlers never meet Lean's: with `open
Lanes`, `deriving ToJson` is ours. With `open Lean` as well the name is ambiguous, an error
(`ambiguous identifier 'ToJson', possible interpretations: [Lanes.ToJson, Lean.ToJson]`,
`scratch/deriving-spike/Spike/Errors.lean`), and `deriving Lanes.ToJson` chooses. No attribute or
priority is needed. `LawfulBEq` is Lean's own class, with Lean's handler: a class may have several
handlers, the one registered last is tried first, and the first that returns `true` wins
(`applyDerivingHandlers`), so ours would run whenever its module is imported, and could return
`false` to leave a type to Lean's.

`ToJson` and `FromJson` are two handlers that build one codec, so whichever runs first makes the
codec and all four instances, and the other finds it (`jsonHandler`,
`scratch/deriving-spike/Spike/Lanes.lean`). A handler does not see the rest of the `deriving`
clause, so `deriving ToJson` alone gives `FromJson` too, where `lanes_data` refuses it.

A table is not a class: it needs a name, a key and indexes, so it is a command of its own, which
reads the structure from the environment:

```lean
structure Todo where
  id : Int64
  owner : Int64
  title : String
  /-- When it was done, if it was. -/
  doneAt : Option Int64 := none
  deriving DecidableEq, Repr, ToJson, FromJson

lanes_table todos : Todo key id
  index byOwner on owner, title
  unique index byTitle "todo_titles" on title
```

The word cannot be `table`. A command cannot begin with a word that is not a keyword (`unexpected
identifier; expected command`), and making `table` a keyword would break the field
`TableOf.table` and `{ table := … }`. A term, `def todos : TableOf Todo := table% key id`, would
avoid the word but cannot also declare `todos.byOwner`.

The spike's handlers are 152 lines (`scratch/deriving-spike/Spike/Lanes.lean`). They read each
field's type from the environment, turn it back into syntax with the delaborator, and call the
functions `lanes_data` already uses (`Lanes.Declare.json`, `structJson`, `sumJson`, `enum`,
`table`), so the codecs and their laws are the same terms. `LawfulBEq` was not ported.

## What changes for a user

Gained:

- Every form Lean's `structure` and `inductive` take: `extends` (fields flattened, as
  `{ x := …, colour := … }` takes them; tested), several fields on one line, attributes,
  `private`, universe parameters, and `deriving instance ToJson for T` for a type declared elsewhere.
- Docstrings on fields and default values are Lean's own, untouched, as with `lanes_data`.
- The check that a field's type names no earlier field reads the elaborated type
  (`Expr.containsFVar`) instead of the text, so a constant named like an earlier field is not
  mistaken for it.
- One concept less: `lanes_data` and its accepted forms (AGENTS.md's paragraph on them).

Lost or changed:

- Every file of an executable must be a module, or the binary is 137 MB. Lanes' own executables
  (`lanes`, `lanesTest`, `lanesCheck`, …), the template and every example are not modules today.
  Lake's `requiresModuleSystem` on the Lanes library makes Lake warn when a file that is not a
  module imports Lanes (`Lake/Config/LeanConfig.lean`; not tried here), which would close the
  trap.
- Errors are reported at the class's name in the `deriving` clause, as Lean's own handlers
  report them. `lanes_data` reports a field that names an earlier one at that field's type, and
  the rest on the command.
- Lanes depends, at compile time, on Lean's elaborator API (`Meta`, the delaborator, the deriving
  framework), which can change at each toolchain bump; `lanes_data` uses only macros. The core
  meta-imports `Lean`, an exception to rule 1.6 that `LanesCli/Layers.lean` would name.
- A type whose delaborated form does not elaborate back (a notation that is not open where the
  codec is elaborated) would fail. A production version builds the codec from the elaborated types instead
  of from syntax.
- Recursive types still have no derived JSON: a codec is a value, as before.
- Each file that imports the handlers elaborates about 0.15 s slower.

## Cost of migrating

From a scan of every `.lean` and template file outside `.lake/`:

- 116 `lanes_data` declarations: 35 in `Lanes/`, 38 in `Tests/`, 41 in `examples/`, 2 in
  `templates/`. 90 of them derive only Lean's classes (`DecidableEq`, `Repr`, `Hashable`): for
  those the command passes the declaration through unchanged, and the word can be dropped today.
  The other 26 derive ours: 12 `Enum` or `LawfulBEq` only, 11 JSON (10 in `Tests/`, 1 in
  `examples/`), 3 tables.
- Prose: `AGENTS.md` (3 mentions), `docs/ARCHITECTURE.md` (7), `docs/TUTORIAL.md` (1),
  `docs/TUTORIAL-WEB.md` (3), `examples/README.md` (1). Decisions record the past and stay.
- The module system: the template's 4 Lean files, the examples' 66 files, 136 of the 137 files
  of `Tests/` and the 4 of `LanesCli/` are not modules. Each gets `module`, `public import` and
  `@[expose] public section` (proofs need the bodies), and `main` becomes `public`. This is most
  of the cost, and a concept every newcomer then meets.

## Recommendation

Keep `lanes_data` for now; do not move to handlers on their own. Weighed by rule 1.8: the reach
is real but modest, nicer syntax and `extends` for the 26 declarations that derive our classes,
and `deriving instance` for types declared elsewhere. The total cost is dominated by what the
handlers require, not by the handlers: every application file, and every Lanes executable, on
the module system, plus a compile-time dependency on Lean's elaborator. If Lanes moves
applications to the module system for its own reasons (Lean's libraries are modules, and modules
rebuild less), the handlers become cheap, and should replace the wrapper then.

Two things are worth doing whatever is chosen:

- Correct the record: D15's 137 MB and D38's "even through `meta import`" hold for an executable
  whose root is not a module, and not otherwise. This decision is that correction.
- Drop `lanes_data` from the 90 declarations that derive only Lean's classes, and say in
  `AGENTS.md` that the word is for deriving Lanes' classes. The word then appears only where it
  does something.

## Migration plan, if applications move to the module system

1. Make the template, then the examples, `Tests/` and `LanesCli/` modules, one pull request
   each, and set `requiresModuleSystem := true` on the Lanes library.
2. Add `Lanes.Derive`: the handlers for `Lanes.ToJson`, `Lanes.FromJson`, `Lanes.Enum` and
   `LawfulBEq`, and `lanes_table`, building the codecs from elaborated types. `Lanes.lean` does
   `public meta import Lanes.Derive`, so `import Lanes` carries them and no file adds a line
   (`viaPrelude` measured this). Port `Tests/Derive.lean` to plain declarations, its error
   cases included, and keep a test that a module root importing Lanes has no `l_Lean_Elab`
   symbol.
3. Rewrite the 26 declarations that derive our classes and the 3 `table` lines, then the prose.
4. Remove `lanes_data` and `Lanes/Data/Declare.lean`'s macros, keeping the builders the handlers
   call.
