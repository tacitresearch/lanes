# Examples

Applications built on Lanes, each a Lake package of its own that depends on the framework in
this repository by path, as an application of yours would depend on it by git. They are written
to be read: copy one to start. The tests do not use them (they use copies in `Tests/Fixtures/`),
so an example can change for its reader alone. The large ones are also here to find out what the
framework is missing: anything one of them has to work around is a defect of Lanes, and is fixed
there.

## In what order to read them

`docs/TUTORIAL.md` comes first: it changes the counter, checks it and proves it.

1. `counter`: exactly what `lake exe lanes new counter` writes. A spec as a `Service`, run as an
   actor by the `Server` behaviour, an invariant, refinement to the spec, model checks, and a
   web page with htmx. `lake test` fails if it and the template differ.
2. `bank`: accounts as actors that send each other credits. An invariant of every actor
   (`balance_nonneg`), one of the whole system (`money_conserved`), and the checker finding the
   credit a lossy link drops.
3. `bank-web`: the bank behind a server-rendered page: typed routes, a bridge from requests to
   inputs, templates, and a journal with snapshots that survives `kill -9`.
4. `kv-cache`: a key-value store with front ends, checked against a five-line spec with no
   refinement mapping. A read cache breaks it, and the checker and the proof both show the stale
   read; behind the `Once` memo it takes each request once under every fault.
5. `election`: leader election with timers, crashes and restarts, at most one leader per term,
   proved with a ghost history and `Monotone`; random runs for five nodes.
6. `watchdog`: what fairness says about a keep-alive: a fair run in which the dog never barks.
7. `migration`: a deploy that changes the state type. Version 1 of a quota service runs on a
   journal; version 2 adds a quota to each user, reads version 1's files through an upgrade,
   and carries its invariant across with the migration's proof.
8. `raft-kv`, `ledger`, `rookery`: the serious systems below.

| Feature | Where to see it |
| --- | --- |
| A spec as a `Service`, run by `Server` | `counter` |
| A spec as a `Service`, implemented by actors | `kv-cache`, `ledger`, `raft-kv`, `rookery` |
| `lanes_data` and codecs | `counter`, `bank`, `ledger`, `raft-kv`, `rookery` |
| Per-actor invariants (`actor_invariant`, `System.invariant_of_actor`) | `counter`, `bank`, `ledger`, `raft-kv`, `rookery` |
| Invariants under every fault (`Monotone`), ghosts | `election`, `ledger`, `raft-kv` |
| Refinement to a spec (`System.Implements`, `System.Refines`) | `counter`, `kv-cache`, `ledger`, `raft-kv`, `rookery` |
| A request takes effect once (`Once.actor`, `Service.once`) | `kv-cache`, `raft-kv` |
| Fairness and liveness | `watchdog` |
| Model checks, a bug found, random runs | `bank`, `kv-cache`, `election` |
| HTTP, routes, htmx, templates | `counter`, `bank-web`, `ledger`, `rookery` |
| A journal and snapshots across `kill -9` | `bank-web`, `ledger`, `raft-kv`, `rookery` |
| A changed state type: an upgrade, a migration and its proof (`Migration`, `Journal.Upgrade`) | `migration` |
| Sessions, log-in, cookies, tokens | `ledger`, `rookery` |
| A JSON API and rate limits | `rookery` |
| Shards in several processes, joined by TCP | `raft-kv` |

## The serious systems

| System | What it is | State |
| --- | --- | --- |
| `raft-kv` | A replicated key-value store: Raft, generic over the machine it replicates | Protocol written and model-checked against its spec and its invariants; the invariants of Raft's safety argument, leader completeness among them, and refinement to the spec, proved for every cluster and fault, given that no request is handed to a node twice, and, with the machine behind a memo, with no premise (the processes run the plain map); runs as three processes with an HTTP front each, joined by TCP, that save their state and cut their journals, through every node killed with SIGKILL and started again, and through a minute of nodes killed and paused at random with every acknowledged write kept (`raftChaos`); a node is not started without its journal unless it is new |
| `ledger` | A multi-user double-entry ledger as a web application: sign-up, log-in, sessions, transfers between users, an audit | Spec and safety properties first; users as actors, the book as one actor; refinement and every property model-checked on two users with two accounts each, with crashes and timers; conservation, no overdraft, paired entries, visibility and the bounds on sessions and failed log-ins proved for every run and fault; refinement to its spec proved where the links from the users to the book are ordered and do not duplicate, and with timers where they also lose nothing and the book does not crash; served over HTTP with a journal and snapshots, tested through SIGKILL and a restart. Its friction log (`ledger/README.md`) is what it is for |
| `rookery` | A small social network for bots and their owners: sign-up, sessions, API tokens, posts, follows, timelines, deletes, rate limits, as a web application with a JSON API | The flagship. Spec first and checked alone; one actor that runs it; every claim proved of the spec for every configuration (posts never lost and deleted only by their author, a deleted post in no read, timelines exactly the newest posts followed, the rate limit, API changes acted on once per `seq`, no other account's secrets, the bounds) and the system proved to implement its spec with deadlines, under lost and reordered requests and crashes, where the link from outside does not duplicate; the two are not yet joined into statements about the running system, and the gate in front is not covered; served over HTTP with a journal and snapshots, tested through SIGKILL and a restart. Its README lists each claim with its theorem, what remains, and its friction log |

## Building one

```bash
cd examples/raft-kv
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build
lake test
lake exe raftLive     # three nodes in one process
lake exe raftProcs    # three processes, killed and started again
lake exe raftChaos    # a minute of random faults; not part of the tests
```

and in the same way, in `examples/ledger`, `lake build`, `lake test` and `lake exe ledgerLive`;
in `examples/rookery`, `lake build`, `lake test` and `lake exe rookeryLive`; and in each small
one, `lake build` and `lake test` (`bank-web` needs `bank` beside it, which it requires by path).
