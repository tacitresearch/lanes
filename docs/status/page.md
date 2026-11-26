# Status

Where the implementation stands against `DESIGN.md`. Each row of the two tables, with the known
limits of its area, is a file in `docs/status/` (`areas/<area>.md`, `apps/<app>.md`: the row on
the first line, the limits after it), and the rest of this page is `docs/status/page.md`.
Update them in the same change that moves an item; `lake exe lanes lint --fix` writes this page.

## Working

| Area | What exists | Where |
| --- | --- | --- |
<!-- rows: areas -->

## Reference apps

| App | Checked | Proved |
| --- | --- | --- |
<!-- rows: apps -->

## Against the DESIGN exit criteria

- **Phase 1** (runtime and actor API): met, except that the gateway app does not exist. The runtime's logic is proved, which Phase 1 did
  not ask for.
- **Phase 2** (semantics, specs, refinement): semantics, lifting theorem and refinement theory
  are in. Trace checking runs in the test suite. Not done: the scheduler simulation proof, the
  Raft KV store.
- **Phase 3** (model checking and system proofs): checker finds the seeded split-brain bug;
  money conservation is proved for all instances. At most one leader per term is proved. Not done:
  counterexample-to-induction finder, `lanes prove`, symmetry reduction, parallel search.
- **Phase 4** (liveness): fair runs, leads-to and its proof rule are in, with one theorem, the
  gate's, and fair runs are proved to exist. Not done: ranking functions, the lasso search,
  "eventually a leader".
- **Phases 5 to 8**: only the HTTP server adapter, the HTML layer and JSON exist.

## Next, in order

1. Make the monotone proof rule cheaper to use, from what the election proof showed: a variant
   that takes per-state, per-message and per-timer predicates and discharges `below` itself, a
   frame lemma for the actors that did not move, and projections for ghost state.
2. Counterexample-to-induction finder and `inv_split`, then `lanes prove`.
3. Releasing idle actors.
4. What `systems/ledger` asks of the framework (its README's friction log): requests prepared
   before the journal, specs with time, `Service` without the system's signature.

## Known limits

<!-- limits -->
