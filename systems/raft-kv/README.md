# raft-kv

A replicated key-value store. The protocol is Raft (`RaftKV/Protocol.lean`), written once as
the step function of a node and generic over the machine it replicates; the key-value map is
one instance (`RaftKV/Store.lean`).

## What it must do

To its clients the cluster is one machine: every answer is one the machine would give if it
handled the commands one at a time in some order consistent with when they were sent and
answered. That is `spec`, six lines, and it is checked as refinement by a monitor, with no
refinement mapping written.

The invariants of Raft's safety argument are checked in every state as well
(`RaftKV/Properties.lean`): at most one leader per term, log matching, agreement on committed
entries, leader completeness.

## What has been checked

Three nodes, one key, two values, a write and a read, with terms, log lengths and messages in
flight bounded. `lake test` runs the quick checks; `lake exe raftCheck deep` the others.

| Instance | States | Result |
| --- | --- | --- |
| Reliable links, one term, three messages in flight | 6,616 | passes |
| Reliable links, two terms | 695,272 | passes |
| Unordered links, one term | 845,974 | passes |
| Unordered links, one crash and restart, one term | 6,012,807 | passes |
| Seeded bug: a node votes for a candidate whose log is behind | 27,412 | found: a leader lacks a committed entry, in 15 steps |
| Seeded bug: a leader commits an entry of an earlier term by counting (four terms, two writes) | 4,651,808 | found: a later leader lacks the entry, in 28 steps |

Each passing check also reaches its witnesses: a leader is elected, a write is answered, a read
sees the written value, a follower commits.

## What is not here yet

- Proofs. The invariants are checked on small instances, not proved for all.
- More than one process. The nodes are actors of one system; a cluster of machines needs the
  node-to-node transport (`docs/ROADMAP.md`, phase B).
- Change of membership, and compaction of the log.
- Sending a new follower less than the whole log on first contact.
- An answer for a client that reaches a node which is not the leader. The request is dropped
  and the client's deadline passes.
