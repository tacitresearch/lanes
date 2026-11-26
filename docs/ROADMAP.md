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

## Review at the end of phase A (2026-11-27)

Asked at each phase end: is this still the right direction, and is there a better design?

**What changed from the plan, and why it was better.**

- Durability became a journal of what the kernel was asked, not stored actor states (D24). It
  fell out of the kernel being pure: replay is the same run continued, so a restart is not a
  fault any proof has to account for, and only inputs need a codec.
- An adapter became a model of the outside plus a handler (D26), not an actor. The outside
  makes choices and actors do not; the semantics already puts choices in events.
- Composition is proved by projection (what holds of one side holds in any join), not yet as a
  precongruence for refinement. Projection is what the semantics gives for free, because a
  system's theorems already quantify over everything its environment may send.
- Sugar for applications will be macros, not deriving handlers: anything that imports `Lean`
  costs 137 MB in the binary, even through `meta import`.

**What held.** Every defect found by four reviews and by the proofs themselves was in code no
theorem covered, or in a statement weaker than its name. Each fix moved logic into a pure
function. Twice a proof found a bug in code written the same night (`Kernel.fire`, the name of
a `sometimes` property), and once the checker rejected a property its author believed.

**What to watch.**

- *Trusted code is growing with features*: about 590 lines, from 430. The shell itself is flat;
  the growth is file IO and adapters, each with a conformance test. The lint pins the sizes.
- *Timers and liveness do not quite agree.* In the semantics, arming a pending timer again
  changes nothing, so a fair run still fires it; in the runtime it restarts the delay, which is
  what a keep-alive wants. A liveness proof that leans on a timer firing is about the model.
  The honest fix is to give a timer an identity that re-arming changes, in the semantics as in
  the kernel. This should be settled before Raft, whose election timer is reset by heartbeats.
- *The net is one list.* A state records the order of messages on different links, which
  nothing can observe, and reachability is stated up to equality. The projection proof for
  joins paid for this twice: the left side needed a hidden relation to get an exact statement,
  and the right side is true only up to that unobservable order (`SysState.Equiv`), because a
  join boots one side first. The shard theorem is up to the same relation
  (`System.SplitReachable.merged`). Decided:
  the relation is in the core now (`Lanes/Actors/Equiv.lean`) and theorems about systems put
  together are stated up to it. A queue per link would make states canonical, but it would
  touch every proof in the core for no new guarantee.
- *Proof volume.* The kernel's timer invariants are 700 lines, the search's soundness 800. They
  were re-proved after each change without trouble, but every kernel change now has that cost.
- *Throughput.* One shard, and about 90 µs to wake it. Nothing in phase A depended on it;
  phase B does.

**Verdict.** The direction holds. Phase B starts with the timer identity question, because it
changes the semantics, then shards.

## Serious applications

`Examples/` holds small pieces, one idea each, that run in seconds. Serious applications live
in `systems/`, each its own Lake package that requires Lanes as a user would, with its own CI
job. They stay in this repository while the API they use is changing, so that a framework
change that breaks one cannot merge. One moves to its own repository when that API has settled
or the application needs its own releases.
