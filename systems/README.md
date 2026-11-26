# Systems

Serious applications built on Lanes, each a Lake package of its own that depends on the
framework in this repository by path. They are here to find out what the framework is missing:
anything one of them has to work around is a defect of Lanes, and is fixed there.

| System | What it is | State |
| --- | --- | --- |
| `raft-kv` | A replicated key-value store: Raft, generic over the machine it replicates | Protocol written and model-checked against its spec and its invariants; no proofs yet; one process only |

To build one:

```bash
cd systems/raft-kv
mkdir -p .lake && ln -s ../../../.lake/packages .lake/packages   # share the fetched dependencies
lake build
lake test
```
