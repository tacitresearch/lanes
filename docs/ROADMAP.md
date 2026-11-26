# Roadmap

The larger map, agreed 2026-11-27. `PLAN.md` holds the step being worked on; `STATUS.md` holds
what exists. Review this file whenever a phase ends: is this still the right direction, and is
there a better design than the one written here?

## Where the design stands

The core has held up: pure step functions, one semantics, a proved kernel inside a thin shell,
check before you prove. In two independent reviews and one night of proofs, every defect found
was in code no theorem covered, and each fix moved logic into a pure function with a proof.

Four contracts in the core are not settled. Each could change the `Actor` or kernel API, so they
come before anything is built on top.

1. **Durability.** What survives the process, and what may leave the system before it is safe.
2. **Composition.** Joining verified systems, with a theorem that refinement is kept.
3. **The outside world.** An adapter as an actor with a model the checker explores, plus an IO
   implementation tested against that model.
4. **Time and liveness.** Fairness in the semantics, so "eventually" can be stated.

## Phases

| Phase | What | Done when |
| --- | --- | --- |
| A. Settle the contracts | Durability; a composition operator with its theorem; adapters with a model of the outside; fairness, so liveness can be stated; codecs for inputs | The bank survives `kill -9` with recovery covered by a theorem; the gate is rebuilt with the general operator; one real adapter passes conformance against its model |
| B. Scale | Several shards; node-to-node transport; checker v2; snapshots | A Raft-sized model check finishes in minutes; a shard restarts from a snapshot in time that does not grow with its history |
| C. Acceptance test | `systems/raft-kv` | Linearizability proved against the map spec; runs on three machines; survives fault injection |
| D. Batteries | Database, HTTP client, sessions and auth, server push, jobs, observability | `systems/ledger` is a full web application using all of them |
| E. Developer experience | A macro that hides signature boilerplate; `lanes prove`; counterexample-to-induction; a cheaper proof API; tutorial; trace viewer | A new user ships a checked application in a day |

A comes first because B to D build on its contracts. C comes before D because Raft will find
the mistakes in A and B while they are cheap to fix.

## Assumptions made without an answer

- **The Lean runtime is the production target for now.** If it becomes a reference
  implementation instead, the kernel is run from another host and the investment moves to
  proofs. Nothing in phase A depends on the answer.
- **Library and protocol code is proved; application code is model-checked and proves its key
  invariants.**

## Standing risks

- Lean as a production runtime: a thread crossing costs about 90 µs, and Std has no TLS, HTTP
  client or database.
- Proof cost: election safety took 240 lines with the new tools; full Raft is perhaps ten times
  that. How much automation closes the gap is unmeasured.

## Serious applications

`Examples/` holds small pieces, one idea each, that run in seconds. Serious applications live
in `systems/`, each its own Lake package that requires Lanes as a user would, with its own CI
job. They stay in this repository while the API they use is changing, so that a framework
change that breaks one cannot merge. One moves to its own repository when that API has settled
or the application needs its own releases.
