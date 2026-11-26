# Systems

Serious applications built on Lanes, each a Lake package of its own that depends on the
framework in this repository by path. They are here to find out what the framework is missing:
anything one of them has to work around is a defect of Lanes, and is fixed there.

| System | What it is | State |
| --- | --- | --- |
| `raft-kv` | A replicated key-value store: Raft, generic over the machine it replicates | Protocol written and model-checked against its spec and its invariants; the invariants of Raft's safety argument, leader completeness among them, and refinement to the spec, proved for every cluster and fault, given that no request is handed to a node twice; runs as three processes with an HTTP front each, joined by TCP, that save their state and cut their journals, through every node killed with SIGKILL and started again, and through a minute of nodes killed and paused at random with every acknowledged write kept (`raftChaos`); a node is not started without its journal unless it is new |

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
