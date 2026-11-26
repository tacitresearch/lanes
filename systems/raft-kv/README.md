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

## What has been run

`lake exe raftLive` starts three nodes on the runtime in one process, joined by TCP, each with
a journal and with real timers. A leader is elected, a write and a read are answered, the
leader is stopped, the other two elect one of themselves and go on answering, and the stopped
node comes back from its journal and catches up. `RaftKV/Deploy.lean` has what a node needs as
a process: the codecs for its messages and `startNode`.

`raftNode` is one node as a process, with an HTTP front:

```bash
lake exe raftNode 0 8800 node0.journal 7810 7811 7812 &
lake exe raftNode 1 8801 node1.journal 7810 7811 7812 &
lake exe raftNode 2 8802 node2.journal 7810 7811 7812 &
curl -X PUT -d 1 http://127.0.0.1:8800/kv/a      # 200 from the leader, 504 from the others
curl http://127.0.0.1:8800/kv/a                   # 1
kill -9 %1                                        # the leader
curl http://127.0.0.1:8801/kv/a                   # 1, from whichever of the two now leads
```

`lake exe raftProcs` does this as a test: three processes, the leader killed with SIGKILL, the
killed node brought back from its journal, then the second leader killed too, so that what is
left is a majority only because the first came back with what it had.

## What is proved

In `RaftKV/Proofs/`, for every finite set of nodes, every machine and every environment model
(loss, duplication, reordering, crashes and restarts), in every reachable state. The first five
rows hold for every `Config`, the two bug-seeding switches on or off:

| Theorem | Says |
| --- | --- |
| `election_safety`, `electionSafety_invariant` | No two nodes lead the same term. |
| `applied_le_commit`, `appliedWithinCommit_invariant` | A node has applied no more than it has committed. |
| `entry_term_le`, `entryTermsWithinTerm_invariant` | No entry is of a later term than the node that holds it. |
| `leader_append_only`, `leader_log_grows` | A node that leads a term before and after a step has kept every entry it had. |
| `log_matching`, `logMatching_invariant` | Two logs that agree on the term of an entry agree on everything up to it. |

The rest need both switches on. With either off the checker finds a leader without a committed
entry (the seeded checks above):

| Theorem | Says |
| --- | --- |
| `commit_le_length`, `commitWithinLog_invariant` | A node has committed no more than it has in its log. |
| `committed_agree`, `committedAgree_invariant` | What two nodes have both committed is the same. |
| `leader_complete`, `leaderComplete_invariant` | A leader has what every node no further on in terms has committed. |
| `leader_completeness` | Leader completeness as Raft states it, over the history: what a majority held in a term (`Chosen`) is in the log of every leader of a later term, at every time. |
| `committed_chosen` | What a node has committed is a start of something a majority held, in a term up to the node's. |

Each `…_invariant` is the function the checker evaluates, equal to `true`: what is checked and
what is proved are the same definition.

The proofs give each node a ghost history of the states it has left (`Lanes/Actors/Past.lean`)
and build one invariant in layers with the monotone proof rule, so one argument covers every
fault: `Votes`, `Terms`, `Logs`, `Standing`, `Safe`, `Commits`. What the layers say of a state
without its history is checked first, as properties of their own (`raftCheck "what the proofs
use, one term"`, and two deep ones). `Safe`, which is about what a majority may yet come to
hold, has no such form; it is checked only through the three properties it proves.
`Proofs/Axioms.lean` holds every theorem to Lean's three standard axioms. `lake build` builds
them; `raftCheck` does not link them.

## What is not here yet

- The top theorem: that the cluster refines `spec`. It is stated (`RaftKVProofs.lean`,
  `ImplementsMachine`) and checked on small instances, not proved. What is proved gives the
  list of commands that have taken effect: what a majority has held is never lost. What is
  missing is the account of clients: that each request becomes at most one entry, and that the
  node that took it answers with what the machine said.
- Liveness: that a request is ever answered.
- More than one machine. The nodes are processes joined by TCP, on one machine in every test;
  the transport has no authentication or encryption.
- An answer from a node that is not the leader. It lets the request run into its deadline,
  `504`, and the client asks the next node.
- Election timeouts that differ by themselves. Each node is given its own in its configuration.
- Change of membership, and compaction of the log.
- Sending a new follower less than the whole log on first contact.
