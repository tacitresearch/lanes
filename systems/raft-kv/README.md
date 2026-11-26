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

Each passing check also reaches its witnesses: a leader is elected, a write is answered, a read
sees the written value, a follower commits.

## What is proved

In `RaftKV/Proofs/`, for every finite set of nodes, every machine, every `Config` (the two
bug-seeding switches on or off) and every environment model (loss, duplication, reordering,
crashes and restarts), in every reachable state:

| Theorem | Says |
| --- | --- |
| `election_safety`, `electionSafety_invariant` | No two nodes lead the same term. The second is `electionSafety c = true`, the function the checker evaluates. |
| `applied_le_commit` | A node has applied no more than it has committed. |
| `entry_term_le` | No entry is of a later term than the node that holds it. |
| `leader_append_only`, `leader_log_grows` | A node that leads a term before and after a step has kept every entry it had. |
| `log_matching`, `logMatching_invariant` | Two logs that agree on the term of an entry agree on everything up to it. The second is `logMatching c = true`. |

The proofs give each node a ghost history of the states it has left and use the monotone proof
rule, so one argument covers every fault. `Proofs/Axioms.lean` holds them to Lean's three
standard axioms. `lake build` builds them; `raftCheck` does not link them.

## What is not here yet

- The rest of the proofs: agreement on committed entries, leader completeness and refinement to
  `spec`, which are checked on small instances only and hold only with both switches on. So is
  `commit ≤ log.length`, the last part of `wellFormed`: a follower's log gets shorter when a
  leader's entries replace its own, and that this never reaches a committed entry is leader
  completeness. With `votesForUpToDateOnly` off it is false: a leader elected without two
  committed entries replaces them, in a follower that has committed both, with its one.
- More than one process. The nodes are actors of one system; a cluster of machines needs the
  node-to-node transport (`docs/ROADMAP.md`, phase B).
- Change of membership, and compaction of the log.
- Sending a new follower less than the whole log on first contact.
- An answer for a client that reaches a node which is not the leader. The request is dropped
  and the client's deadline passes.
