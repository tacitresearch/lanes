# counter

A [Lanes](https://github.com/tacitresearch/lanes) application. Lanes links libsodium: install
`libsodium-dev` and `pkg-config` first.

```bash
lake exe cache get      # once: prebuilt Mathlib
lake build
lake test               # model checks
lake exe counter 8080  # run
lake exe counter 8080 app.journal  # run, and keep state across restarts
```

## Rules for agents

The rules are Lanes' own, numbered as the code cites them (rule 2.4): the `AGENTS.md` of the
Lanes package this application requires (in .lake/packages/lanes once Lake has fetched it, or
[on GitHub](https://github.com/tacitresearch/lanes/blob/main/AGENTS.md)), sections Design, Code
and Proofs. The ones every change here meets:

- Write or update the spec first, and model-check it before the implementation or a proof
  (rules 1.2, 5.1). Pair every `always` property with a `sometimes` (rule 5.3).
- `step` is pure: no IO. Work outside the system is an output to an adapter, and its answer comes
  back as an input (rule 2.4).
- Encode invariants in types first, theorems second, runtime checks only at adapters (rule 2.1).
- Bound every queue, map and retry in its type or `Config` (rule 2.6).
- Never add `sorry`, `partial`, `unsafe` or an axiom without listing it in `TRUSTED.md`
  (rule 5.5).
- On an unexpected state, emit `stop`; do not add defensive fallbacks (rule 3.1).
- Write almost no comments. A comment is for a *why* that a name, a type or a theorem cannot
  carry. If code needs explaining, rename or restructure it.
- Run `lake build && lake test && lake exe lanes lint` before claiming a task is done.

## Layout

- `Counter/Counter.lean`: logic. The spec, the actor and its invariant. Pure: no IO.
- `Counter/Proofs.lean`: proofs that need `Lanes.Semantics`, such as refinement to the spec.
- `Check.lean`: model checks on small instances, run by `lake test`.
- `Main.lean`: the edge. HTTP, HTML views, `main`.

Executable code imports `Lanes`. Proof files that need refinement or Mathlib import
`Lanes.Semantics`; keep that import out of anything `Main.lean` depends on, or the binary grows
by over 100 MB.
