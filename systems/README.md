# Systems

Serious applications built on Lanes, each a Lake package of its own that depends on the
framework in this repository by path. They are here to find out what the framework is missing:
anything one of them has to work around is a defect of Lanes, and is fixed there.

| System | What it is | State |
| --- | --- | --- |
| `raft-kv` | A replicated key-value store: Raft, generic over the machine it replicates | Protocol written and model-checked against its spec and its invariants; the invariants of Raft's safety argument, leader completeness among them, and refinement to the spec, proved for every cluster and fault, given that no request is handed to a node twice; runs as three processes with an HTTP front each, joined by TCP, that save their state and cut their journals, through every node killed with SIGKILL and started again, and through a minute of nodes killed and paused at random with every acknowledged write kept (`raftChaos`); a node is not started without its journal unless it is new |
| `ledger` | A multi-user double-entry ledger as a web application: sign-up, log-in, sessions, transfers between users, an audit | Spec and safety properties first; users as actors, the book as one actor; refinement and every property model-checked on two users with two accounts each, with crashes and timers; conservation, no overdraft, paired entries, visibility and the bounds on sessions and failed log-ins proved for every run and fault; served over HTTP with a journal and snapshots, tested through SIGKILL and a restart. Its friction log (`ledger/README.md`) is what it is for |
| `rookery` | A small social network for bots and their owners: sign-up, sessions, API tokens, posts, follows, timelines, deletes, rate limits, as a web application with a JSON API | The flagship. Spec first and checked alone; one actor that runs it; every claim proved for every configuration (posts never lost and deleted only by their author, a deleted post in no read, timelines exactly the newest posts followed, the rate limit, exactly-once API changes, no other account's secrets, the bounds) and the system proved to implement its spec with deadlines, under lost and reordered requests and crashes; served over HTTP with a journal and snapshots, tested through SIGKILL and a restart. Its README lists each claim with its theorem, what remains, and its friction log |

To build one:

```bash
cd systems/raft-kv
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build
lake test
lake exe raftLive     # three nodes in one process
lake exe raftProcs    # three processes, killed and started again
lake exe raftChaos    # a minute of random faults; not part of the tests
```

and in the same way, in `systems/ledger`, `lake build`, `lake test` and `lake exe ledgerLive`, and
in `systems/rookery`, `lake build`, `lake test` and `lake exe rookeryLive`.
