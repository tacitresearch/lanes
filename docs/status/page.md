# Status

What exists, area by area, and its known limits. Each row of the two tables, with the known
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

1. Make proving an application cheap: a library for the usual simulation relations (what the
   key-value store's refinement proof repeated), the cheaper monotone rule the election proof
   asked for, then a counterexample-to-induction finder and `lanes prove`. The measure: the
   ledger's refinement of its spec, proved.
2. A generated proof inventory: every public definition proved, checked, tested, trusted or
   none, kept current by CI, with none left in library code.
3. The standard library: what Go's has that applications need, triaged into what Lean already
   has, what is pure (built and proved, and tested against Go), what is bound, and what is not
   needed.
4. Shrink what is trusted and assumed: the server's request reader, `fsync` and the bound
   cryptography, exactly-once requests, idle actors released.
5. A place for slow work that is not a function of one request, as the ledger's friction log
   asks.

The standard library, triaged from Go's, with its P0 set in build order: `docs/STDLIB.md`.

## Known limits

<!-- limits -->
