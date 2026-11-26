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
- The gate was rebuilt with the join after the phase ended (D31): `Http.fronted`. It needed two
  things the join did not have: runs, not only states, seen from one side
  (`SysState.run_left`), and a way to hide what a join wires (`System.filterMapIO`). The
  hand-built `gated` stays until fair runs project, since its liveness theorem is about them.
- Sugar for applications will be macros, not deriving handlers: anything that imports `Lean`
  costs 137 MB in the binary, even through `meta import`.

**What held.** Every defect found by four reviews and by the proofs themselves was in code no
theorem covered, or in a statement weaker than its name. Each fix moved logic into a pure
function. Twice a proof found a bug in code written the same night (`Kernel.fire`, the name of
a `sometimes` property), and once the checker rejected a property its author believed.

**What to watch.**

- *Trusted code is growing with features*: about 590 lines, from 430 (and far more since: see
  the next review). The shell itself is flat;
  the growth is file IO and adapters, each with a conformance test. The lint pins the sizes.
- *Timers and liveness now agree* (settled after this review, D27). In the semantics, arming
  a pending timer again changes nothing; in the runtime it restarts the delay, which is what a
  keep-alive wants. Fairness used to oblige every timer that stays pending to fire, so a
  liveness proof that leaned on a timer was about the model only, and a Raft follower would
  have timed out under heartbeats in every fair run. Fairness now obliges a timer to fire only
  if it stays pending and no step arms it again. The semantics did not change; the leads-to
  rule got one more premise for timers; the gate's theorem was re-proved with it; and a
  watchdog whose keeper pings forever never barks in a fair run
  (`Examples/WatchdogProofs.lean`). A timer identity in the semantics was not needed.
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

**Verdict.** The direction holds. The timer question came first and is settled in the
definition of a fair run, with the semantics as it was. Phase B starts with shards.

## Review after the first night of phase B (2026-11-26)

**What was built.** A fourth review and its fixes; snapshots; the order of a save as a proved
function; the theorem that two shards are the one system; a transport between processes;
`systems/raft-kv`, model-checked and running as three nodes over TCP through a leader's death.

**What the night taught.**

- *An adapter's handler may not decide.* The fourth review could not break anything proved.
  It found a journal deleted by opening it with the wrong codec, a second process starting on
  a journal in use, callers left hanging when a write failed. Raft, started on real sockets,
  worked the first time, and the transport under it did not: a stopped shard kept its
  connections open. Every one of these was a decision made in IO code. Three adapters now
  have the right shape. The HTTP server's logic is an actor, the gate. The journal's is a pure
  function over a model of its two files, with a crash-consistency theorem, and the IO runs
  the writes it is given. The HTTP client's reading is a pure function. The transport did not
  have it: its queues, its reconnecting and what `stop` ends were IO. **Rule from here on: an
  adapter is an actor or a pure function that decides, a model of the outside it talks to, and
  a handler that only performs.** The transport was rebuilt that way the same night (the
  courier, D30), and the model checker run against a failing network found a property of mine
  that was false.
- *A snapshot is a restart without the crash.* The plan asked for a theorem that kernels alike
  in everything observable behave alike, because a restored hash map is not the saved one.
  Making the running shard go on with the restored kernel removed the need: both sides compute
  equal values. The general lesson is to make the recovery path the normal path, so that
  equality replaces equivalence.
- *Mutants pass.* The review ran mutants of trusted code and three passed the whole suite.
  Each now fails a test, and every fix since has been checked against its own mutant. A
  standing mutation run over the trusted files is cheap and is the right gate for them.
- *The checker is the bottleneck of phase C*, as expected: one crash on three Raft nodes is
  six million states and ten minutes (three, after the checker was made faster). A seeded Raft bug that needs four terms took 4.7 million
  states to find.
- *A property can be wrong too.* The first leader-completeness property was stronger than
  Raft's and held on every instance that fitted; a seeded bug in a larger one showed it.
  Vacuity witnesses do not catch a property that is too strong on states never reached.
  Seeding bugs and widening one bound at a time is what did.

**What to watch.**

- *Trusted and unproved code is about 1,500 lines*, three times what it was at the end of
  phase A: the transport's handler (168), the HTTP wire format (411, part proved), the journal and
  snapshot IO. The pure cores behind them are proved, but the count is the wrong way round
  for a framework whose point is the opposite, and the rule above is how it comes down.
- *Proof volume.* The join, the split and the disk model are 1,700, 1,050 and 650 lines.
  The lemmas agents reported missing each time (updates of functions, erasing under a map,
  a step in closed form, permutations of the net, reachability up to `Equiv` closed under
  steps) are in the core now: `Lanes/Data/List.lean` and `Lanes/Actors/{World,Run,Equiv}.lean`.
  What is left is the size of the arguments themselves, the join's above all.
- *Boot order is observable* when a boot actor stops as it starts, which is why the shard
  theorem carries a condition. Nothing depends on it yet.
- *Throughput* was fifteen thousand inputs a second on one shard, and nobody had measured
  it. It is 1.8 million now (D32). The kernel was never the cost: the channel between threads
  was, and a promise made for every input. Finding the second took measuring each piece alone,
  after two confident explanations were wrong. The benchmark prints the number on every run.
- *Two gates* until the hand-built one is retired in favour of the gate joined by the general
  operator; a process with both an HTTP front and peers needs the joined one.

**Since this review** (the same day): the lemma library was consolidated, the checker made
3.5 times faster, the inbox rebuilt as a batch (1.8 million inputs a second on a shard, from
fifteen thousand), the gate rebuilt as a system joined by the general operator, and Raft proved
linearizable and run as three processes through two leaders killed. Phase C's criterion is met
but for running on three machines.

**Verdict.** The direction holds and the order changes a little: the lemma library comes
before more batteries, because Raft's proofs stand on it, and no adapter is added from here
on without its deciding function and its model.

## Serious applications

`Examples/` holds small pieces, one idea each, that run in seconds. Serious applications live
in `systems/`, each its own Lake package that requires Lanes as a user would, with its own CI
job. They stay in this repository while the API they use is changing, so that a framework
change that breaks one cannot merge. One moves to its own repository when that API has settled
or the application needs its own releases.
