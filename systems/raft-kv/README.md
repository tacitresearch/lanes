# raft-kv

A replicated key-value store. The protocol is Raft (`RaftKV/Protocol.lean`), written once as
the step function of a node and generic over the machine it replicates; the key-value map is
one instance (`RaftKV/Store.lean`).

## What it must do

To its clients the cluster is one machine: every answer is one the machine would give if it
handled the commands one at a time in some order consistent with when they were sent and
answered. That is `spec`, six lines. It is checked as refinement by a monitor, with no
refinement mapping written, and proved for every cluster (`RaftKVProofs.lean`).

The invariants of Raft's safety argument are checked in every state as well
(`RaftKV/Properties.lean`): at most one leader per term, log matching, agreement on committed
entries, leader completeness, and that each node's machine is the map run over the entries
the node has applied.

## What has been checked

Three nodes, one key, two values, a write and a read, with terms, log lengths and messages in
flight bounded. `lake test` runs the quick checks; `lake exe raftCheck deep` the others.

| Instance | States | Result |
| --- | --- | --- |
| Reliable links, one term, three messages in flight | 6,616 | passes |
| Reliable links, two terms | 695,272 | passes |
| Unordered links, one term | 845,974 | passes |
| Unordered links, one crash and restart, one term | 6,012,807 | passes |
| Links between nodes lose messages, one term, three messages in flight | 550,410 | passes |
| Links between nodes lose, reorder and repeat messages (`Link.network`), one term, three in flight | 2,790,036 | passes |
| Requests lost and reordered on their way to a node, one term, three in flight | 34,325 | passes |
| Outside the assumption of the top theorem: a request may be handed to a node twice | 3,021 | found: the request is answered twice, in 18 steps |
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

On those, also with both switches on, state machine safety and the top theorem:

| Theorem | Says |
| --- | --- |
| `step_serves`, `recover_serves` | What one step of a node does for its clients (`Serves`): an entry is added only by the node that handles a `propose`, and is that request; a node applies exactly the entries between what it had applied and what it has now committed; it answers exactly those it took from a client, each with what the machine says after the entries before it. For every `Config`. |
| `requests_from_clients`, `requestsFromClients_invariant` | No node sends a request: those in flight came from clients. For every `Config`. |
| `applied_eq_commit`, `appliedAllCommitted_invariant` | A node has applied all it has committed. |
| `machine_eq_run`, `machinesRun_invariant` | A node's machine is the replicated machine run from `init` over the entries the node has applied. |
| `applied_agree` | Of two nodes, the one that has applied less has applied a start of what the other has. |
| `implementsMachine` (`RaftKVProofs.lean`), `cluster_implements` | The cluster refines `spec`: for every finite set of nodes, every machine and every environment model whose links from clients do not repeat a request. Links between nodes may lose, repeat and reorder, links from clients may lose and reorder, and any node may crash and restart at any time. |

The top theorem is `System.Implements`, a weak simulation, so every finite run of the cluster
has the inputs and outputs of a run of the service in which each command takes effect at one
instant (`Refines.traces`). The one hypothesis is needed: the check "outside the assumption" in
the table above is the run without it, where a request the link hands to the leader twice
becomes two entries and is answered twice. A client that sends a request twice is inside the theorem:
those are two inputs.

The simulation (`RaftKVProofs/Refines.lean`) is on the cluster with its history and is carried
to the cluster by `System.Refines.of_ghost`. It names the list the cluster has committed to
(`Logged`, in `RaftKV/Proofs/Applied.lean`): a committed list that every node's committed
entries are a start of. The service's value is the machine run over that list; its outbox is
the cluster's and the answers nodes still owe for entries of the list; its pending requests
include those in flight and those of every entry, in a log or an `append`, past the end of the
list. A command takes effect when the list grows over its entry, so one step of a node can be
several steps of the service. The pending requests are bounded from below and not computed
from the cluster's state: a request that was lost, or whose entry was replaced, stays pending
for ever, which the service allows. So no ghost counts requests, and the relation is not a
refinement mapping.

The proofs give each node a ghost history of the states it has left (`Lanes/Actors/Past.lean`)
and build one invariant in layers with the monotone proof rule, so one argument covers every
fault: `Votes`, `Terms`, `Logs`, `Standing`, `Safe`, `Commits`. What the layers say of a state
without its history is checked first, as properties of their own (`raftCheck "what the proofs
use, one term"`, and two deep ones). `Safe`, which is about what a majority may yet come to
hold, has no such form; it is checked only through the three properties it proves.
`Proofs/Axioms.lean` and `RaftKVProofs.lean` hold every theorem to Lean's three standard
axioms. `lake build` builds them; `raftCheck` does not link them.

## What is not here yet

- Liveness: that a request is ever answered. The top theorem is safety: a cluster that answers
  nothing refines `spec` too.
- Requests a link may repeat. The theorem assumes it does not, and the node has no way to tell:
  suppressing duplicates needs an id the client keeps (rule 1.5), which is not in the protocol.
- More than one machine. The nodes are processes joined by TCP, on one machine in every test;
  the transport has no authentication or encryption.
- An answer from a node that is not the leader. It lets the request run into its deadline,
  `504`, and the client asks the next node.
- Election timeouts that differ by themselves. Each node is given its own in its configuration.
- Change of membership, and compaction of the log.
- Sending a new follower less than the whole log on first contact.
