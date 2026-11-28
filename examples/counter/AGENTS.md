# counter

A [Lanes](https://github.com/tacitresearch/lanes) application. It needs elan and a C compiler to
build, and PostgreSQL to run.

```bash
lake build
lake test                                    # the model check, then the proofs
LANES_POSTGRES=127.0.0.1:5432 lake test      # and the application on that PostgreSQL
lake test -- --json                          # as JSON: each result with its kind
PGHOST=... PGUSER=... PGDATABASE=... lake exe counter 8080   # run
```

The process keeps nothing: the count is a row in PostgreSQL. A request is one pure transaction,
which the store runs at `SERIALIZABLE` and tries again on a conflict. At the start the
application runs the migrations of `migrations/` not yet run, and refuses to start when the
tables differ from the ones `Counter.schema` declares. An actor's state is a cache of its
process: whatever several instances must agree on lives in the database.

## Rules for agents

The rules are Lanes' own, numbered as the code cites them (rule 2.4): the `AGENTS.md` of the
Lanes package this application requires (in .lake/packages/lanes once Lake has fetched it, or
[on GitHub](https://github.com/tacitresearch/lanes/blob/main/AGENTS.md)), sections Design, Code
and Proofs. The ones every change here meets:

- Write or update the spec first, and model-check it before the implementation or a proof
  (rules 1.2, 5.1). Pair every `always` property with a `sometimes` (rule 5.3).
- `step` is pure: no IO. Work outside the system is an output to an adapter, and its answer comes
  back as an input (rule 2.4).
- What a request does to durable state is one pure transaction (`Handler`). What must outlive
  the process, or agree across instances, is in a table, never only in an actor's state.
- Encode invariants in types first, theorems second, runtime checks only at adapters (rule 2.1).
- Bound every queue, map and retry in its type or `Config` (rule 2.6).
- Never add `sorry`, `partial`, `unsafe` or an axiom without listing it in `TRUSTED.md`
  (rule 5.5).
- On an unexpected state, emit `stop`; do not add defensive fallbacks (rule 3.1).
- Write almost no comments. A comment is for a *why* that a name, a type or a theorem cannot
  carry. If code needs explaining, rename or restructure it.
- Run `lake build && lake test && lake exe lanes lint` before claiming a task is done.
  `lake test` exits 0 only when every check explored its whole instance and the proofs build
  with no warning (a `sorry` is one); it exits 2 when a check passed but hit a bound, which is
  not a pass of the instance.

## Layout

- `Counter/Counter.lean`: logic. The table (`lanes_data … table …`), the transactions, and the
  front, an actor that keeps nothing. Pure: no IO, and no theorems.
- `Counter/Proofs.lean`: the theorems: each transaction keeps the count within its limit, so
  every database the store's model allows does.
- `Counter/Web.lean`: the edge. HTTP, HTML views, and the store on PostgreSQL.
- `migrations/`: plain SQL, run once each, in the order of their names. A change to a table is
  a new file here and the same change to its `lanes_data` declaration.
- `Check.lean`: the model check on a small instance, run by `lake test`, which then builds the
  proofs, and runs the application on PostgreSQL when `LANES_POSTGRES` names one. It does not
  import the proofs, so a broken proof does not stop the checks.
- `Main.lean`: `main`, configured from the environment.

Executable code imports `Lanes`, and `Lanes.Services.Postgres` for the database. Proof files
import `Lanes.Semantics`; keep that import, and every theorem, out of anything `Main.lean` and
`Check.lean` depend on: the binary would link the proofs, and a broken proof would stop the
checks.
