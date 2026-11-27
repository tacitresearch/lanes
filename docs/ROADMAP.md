# Roadmap

The direction, the phases and the risks. `docs/PLAN.md` holds the step being worked on;
`docs/STATUS.md` what exists. Review this file whenever a phase ends: is this still the right
direction, and is there a better design than the one written here? The reviews held so far are
in `docs/history/roadmap-reviews.md`.

## Direction

Decided 2026-11-26 (`docs/decisions/D45-everything-is-proved.md`). Lanes is for software an agent
writes and nobody reads line by line, so its claim has to rest on proofs, not on checks, tests or
review. The order of work:

1. **Proving an application becomes cheap enough to be routine.** A simulation-relation library
   from what the key-value store's proof repeated, a cheaper invariant rule, then a
   counterexample-to-induction finder. The ledger's refinement, proved, is the measure; the
   flagship application is proved, not checked.
2. **A generated proof inventory** gives every public definition a status, and library code has
   none without one. Built (`docs/INVENTORY.md`, D47); `docs/inventory-none.md` lists what still
   has none, and only shrinks.
3. **A standard library on the scale applications need**, triaged from Go's (`docs/STDLIB.md`):
   what Lean already has; what is pure, built here and proved, and tested against Go's
   implementation on generated inputs; what touches the operating system or cryptography and is
   bound (D46); what is not needed.
4. **Trusted and assumed things keep shrinking**: our own HTTP/1.1 request reader in place of
   `Std.Http`'s, exactly-once requests in place of the premise that links from clients do not
   duplicate, idle actors saved to storage when they rest. `fsync` and cryptography bound to
   libsodium are done (D46); exactly-once requests are in for the key-value store (D48); actors
   back where a start puts them are released (`docs/decisions/D51-release-actors-at-rest.md`).
5. **Specs are what a person reviews.** Each system's spec and its premises sit in one place, and
   a person reads them before any public claim.

Launch work (the flagship application, deployment, the write-up) follows 1 to 4, because a launch
claim is what a critic tests first.

## Phases

| Phase | What | Done when | State |
| --- | --- | --- | --- |
| A. Settle the contracts | Durability; a composition operator with its theorem; adapters with a model of the outside; fairness, so liveness can be stated; codecs for inputs | The bank survives `kill -9` with recovery covered by a theorem; the gate is rebuilt with the general operator; one real adapter passes conformance against its model | Done: the journal (D24) and its crash theorems, `System.join` (D25) with the gate joined in front (D31, D43), `Outside` and conformance tests for the server, the clock and the client (D26), fair runs and leads-to (D27), `lanes_data` (D38) |
| B. Scale | Several shards; node-to-node transport; checker v2; snapshots | A Raft-sized model check finishes in minutes; a shard restarts from a snapshot in time that does not grow with its history | Shards proved for any number (D28), the transport with its courier proved (D30), snapshots (D29), the checker 3.5 times faster (D33): Raft's largest check, 7.8 million states, takes minutes. Open: checker v2 (states as flat data, symmetry, parallel search, a lasso search), and a proof that the running processes implement `System.shards` |
| C. Acceptance test | `examples/raft-kv` | Linearizability proved against the map spec; runs on three machines; survives fault injection | Met but for three machines: proved to implement the map it replicates (`RaftKV.implementsMachine`), run as three processes on one machine through `kill -9` and pauses. Frozen as a regression suite. Not done: liveness, membership change, log compaction |
| D. Batteries | Database, HTTP client, sessions and auth, server push, jobs, observability | `examples/ledger` is a full web application using all of them | HTTP client (no TLS), sessions and authentication, `fsync`, libsodium. `examples/ledger` runs with sessions and a journal, checked and not yet proved. Not built: a database, server push, jobs, observability, TLS. Now ordered by the standard library's P0 (`docs/STDLIB.md`) |
| E. Developer experience | A macro that hides signature boilerplate; `lanes prove`; counterexample-to-induction; a cheaper proof API; tutorial; trace viewer | A new user ships a checked application in a day | `lanes_data` and `instance_by_cases`; `lanes new` with a proved counter. In progress: the cheaper proof API (direction 1). Not built: `lanes prove`, counterexample-to-induction, a tutorial, a trace viewer |

A came first because B to D build on its contracts; C came before D because Raft found the
mistakes in A and B while they were cheap to fix. Since D45 the direction above sets the order
inside D and E.

## Serious applications

`examples/` holds small pieces, one idea each, that run in seconds, and the serious
applications, each its own Lake package that requires Lanes as a user would; the serious ones
have a CI job each.
They stay in this repository while the API they use is changing, so that a framework change that
breaks one cannot merge. One moves to its own repository when that API has settled or the
application needs its own releases.

`examples/raft-kv` is frozen as a regression suite: its checks, proofs and process tests stay in
CI, and no Raft feature is added unless the framework needs it. `examples/ledger` is the stress
test of phase D and the measure of direction 1.

## Assumptions made without an answer

- **The Lean runtime is the production target for now.** If it becomes a reference
  implementation instead, the kernel is run from another host and the investment moves to
  proofs.

## Standing risks

- **Lean as a production runtime.** A thread crossing costs tens of microseconds; Std has no TLS
  and no database client; `Std.Async` and `Std.Http` are young. There is no preemption, so one
  slow `step` stalls its shard.
- **Proof cost.** The key-value store's refinement took about 300 lines, Raft's safety about a
  thousand and its refinement some 800 more; how much a relation library and automation close
  the gap is unmeasured, and every kernel change re-proves hundreds of lines.
- **Trusted code grows with features.** The shell is flat; file IO, the transport and the
  adapters are what grew. `lanes lint` pins each file's size and `scripts/mutants.py` holds the
  known ways of breaking it, each of which has to fail a test.
- **A spec can say the wrong thing.** A theorem says the code meets its spec, not that the spec
  says what was meant; a property can also be too strong on states never reached. Specs are
  short and reviewed by a person (direction 5), proved code is tested against a reference where
  one exists, and checks seed bugs and widen bounds one at a time.
- **Model-checker state explosion.** Raft on three nodes with a crash is millions of states;
  larger instances wait for checker v2.
- **Lean, Mathlib and CSLib churn.** The toolchain follows CSLib's and is upgraded deliberately.
