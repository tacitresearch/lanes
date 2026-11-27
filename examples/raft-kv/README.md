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
flight bounded. `lake test` runs the quick checks; `lake exe raftCheck deep` the others, in 19
minutes on one core.

An `append` carries at most `maxAppend` entries. Logs here hold two, so with the default of 8 a
batch is all there is to send, and the rows marked *batches of one* run with `maxAppend := 1`:
a follower two entries behind is brought on in two messages, with elections in between.

| Instance | States | Result |
| --- | --- | --- |
| Reliable links, one term, three messages in flight | 6,278 | passes |
| Reliable links, two terms | 708,116 | passes |
| Unordered links, one term | 704,502 | passes |
| Unordered links, one crash and restart, one term | 5,431,921 | passes |
| Links between nodes lose messages, one term, three messages in flight | 612,692 | passes |
| Links between nodes lose, reorder and repeat messages (`Link.network`), one term, three in flight | 3,042,012 | passes |
| Requests lost and reordered on their way to a node, one term, three in flight | 32,467 | passes |
| Reliable links, one crash and restart, two terms | 7,848,541 | passes |
| Reliable links, two crashes and restarts, one term | 4,309,502 | passes |
| A write through one node and a read through another, reliable links, two terms | 376,864 | passes |
| Two writes through two nodes, reliable links, two terms | 429,066 | passes |
| Batches of one: reliable links, one term, three in flight | 6,692 | passes |
| Batches of one: reliable links, two terms | 712,576 | passes |
| Batches of one: unordered links, one term | 648,562 | passes |
| Batches of one: unordered links, one crash and restart, one term | 4,713,803 | passes |
| Batches of one: links between nodes lose, reorder and repeat messages, one term, three in flight | 1,982,474 | passes |
| Outside the assumption of the top theorem: a request may be handed to a node twice | 3,037 | found: the request is answered twice, in 18 steps |
| Behind the memo: commands named by one client, handed to a node twice and reordered on the way in, one term, three in flight | 11,683 | refines `once` of the map |
| Behind the memo: a write sent again through another node, one term, three in flight | 16,692 | refines `once` of the map |
| Behind the memo: links from clients lose, reorder and repeat, one crash and restart, one term | 189,686 | refines `once` of the map |
| Behind the memo, against the map without `once`: commands handed to a node twice | 3,030 | found: an answer handed over twice, in 18 steps |
| Seeded bug: a node votes for a candidate whose log is behind | 26,798 | found: a leader lacks a committed entry, in 15 steps |
| Seeded bug: a leader commits an entry of an earlier term by counting (four terms, two writes) | 4,055,184 | found: a later leader lacks the entry, in 28 steps |

The rows *behind the memo* run the cluster with `Machine.once` (`RaftKV/Once.lean`): a command
names its client and the client's number for it, and the machine remembers, per client, the
last number it acted on and its answer. They are checked against `once` of the map
(`Service.onceMonitored`), under which a command takes effect at most once and an answer may be
handed over again; the first also reaches an answer waiting twice and a command overtaken by a
later one of its client. The last row is why `once` is the spec: the memo answers a repeat
again, so the map spec, which allows one answer per request, is broken.

Each passing check also reaches its witnesses: a leader is elected, a write is answered, a read
sees the written value where there is a read, a follower commits. With batches of one, an
`append` carries less than its leader has to send, and in two terms one starts past the end of
the log it is sent to. Unordered links with two crashes in one term is more than the ten
million states the checker stores, and is not in the list.

What a PASS means is a theorem (`RaftKVProofs/Checked.lean`): after a complete PASS every
`always` property that was checked holds in every state the instance reaches within its bounds
(`always_of_pass`), and the inputs and outputs of every run of it are a trace of the map
(`traces_of_pass`). The kernel does not run the search, so the PASS is their hypothesis.

## What has been run

`lake exe raftLive` starts three nodes on the runtime in one process, joined by TCP, each with
a journal and with real timers. A leader is elected, a write and a read are answered, the
leader is stopped, the other two elect one of themselves and go on answering, and the stopped
node comes back from its snapshot and its journal and catches up. `RaftKV/Deploy.lean` has what
a node needs as a process: the codecs for its messages and its state, the name of its journal,
and `startNode`.

`raftNode` is one node as a process, with an HTTP front. Its first start is `new`; no later
one is:

```bash
lake exe raftNode new 0 8800 node0.journal 7810 7811 7812 &
lake exe raftNode new 1 8801 node1.journal 7810 7811 7812 &
lake exe raftNode new 2 8802 node2.journal 7810 7811 7812 &
curl -X PUT -d 1 http://127.0.0.1:8800/kv/a      # 200 from the leader, 504 from the others
curl http://127.0.0.1:8800/kv/a                   # 1
kill -9 %1                                        # the leader
curl http://127.0.0.1:8801/kv/a                   # 1, from whichever of the two now leads
lake exe raftNode 0 8800 node0.journal 7810 7811 7812 &   # back with what it had
```

A node keeps its journal, and beside it its state as last saved (`.snapshot`) and a lock. It
saves every 65,536 journal entries (`--snapshot-every <entries>` changes that) and cuts the
journal there, so a start reads the snapshot and replays what came after it.

`lake exe raftProcs` is the test of this: three processes that save every 64 entries. 300
writes are answered while each node cuts its journal some tens of times. All three are killed
with SIGKILL and started from their snapshots and cut journals, two at a time: each pair
answers with every write, which is so only if two of the three nodes each have all of them.
Then the leader is killed, the killed node brought back, and the second leader killed too, so
that what is left is a majority only because the first came back with what it had. Last, a node
is not started on a path with no journal, nor as `new` on its own.

`lake exe raftChaos [seconds] [seed]` is the longer run, a minute unless told otherwise, and
not part of the tests. Four clients write and read through whichever node answers while nodes
are killed, one or two at a time, started again, and paused with SIGSTOP, at random; the nodes
save every 128 entries, so they are killed during saves as well. Every operation is recorded
with the times it was sent and answered. At the end every key is read, and every read, during
the run or after it, must be of a value that was written, and of none older than a write
acknowledged before the read was sent. One minute with seed 7: 39 kills and 13 pauses, 2,343
writes acknowledged, 2,422 reads answered over 1,939 keys, no violation, and journals cut to
between 256 bytes and 14 kB at the end.

## What is proved

In `RaftKV/Proofs/`, for every finite set of nodes, every machine and every environment model
(loss, duplication, reordering, crashes and restarts), in every reachable state. The rows of
the first table hold for every `Config`: the two bug-seeding switches on or off, and whatever
`maxAppend` is:

| Theorem | Says |
| --- | --- |
| `election_safety`, `electionSafety_invariant` | No two nodes lead the same term. |
| `one_leader_per_term` | The same over time: the nodes that lead one term at two points of a run are one node. Stated of the cluster and a run of it, with no history. |
| `append_bounded`, `appendsBounded_invariant` | No `append` in flight carries more than `maxAppend` entries, or more than one where that is zero. |
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
| `applied_agree_over_time`, `applied_same_entry` | State machine safety over time: what a node has applied at one point of a run and what a node, the same or another, has applied at a later point are one a start of the other. So no two nodes ever apply different entries at one index. Stated of the cluster and a run of it, with no history. |
| `implementsMachine` (`RaftKVProofs.lean`), `cluster_implements` | The cluster refines `spec`: for every finite set of nodes, every machine and every environment model whose links from clients do not repeat a request. Links between nodes may lose, repeat and reorder, links from clients may lose and reorder, and any node may crash and restart at any time. |
| `implementsMachine_once` (`RaftKVProofs.lean`), `onceCluster_implements` | With the machine behind its memo (`Machine.once`) and the answers it no longer keeps hidden (`onceCluster`), the cluster implements `once` of the named machine: for every finite set of nodes, every machine, every set of clients and every environment model, with no hypothesis. Every link, those from clients included, may lose, repeat and reorder, and any node may crash and restart at any time. |

The top theorem is `System.Implements`, a weak simulation, so every finite run of the cluster
has the inputs and outputs of a run of the service in which each command takes effect at one
instant (`Refines.traces`). The one hypothesis is needed: the check "outside the assumption" in
the table above is the run without it, where a request the link hands to the leader twice
becomes two entries and is answered twice. A client that sends a request twice is inside the theorem:
those are two inputs.

`implementsMachine_once` removes the hypothesis. A command names its client and the client's
number for it, and the memo is in the machine, so it is replicated with the state: two entries
of one command take effect once and are each answered with what the first was. The spec is
`once` of the machine (`Lanes/Semantics/Once.lean`): each command takes effect at most once, at
one instant between its arrival and an answer, and an answer given may be handed over again,
named as its command. A command overtaken by a later one of its client is answered with
nothing, since the memo keeps one answer per client, and that empty answer is not handed over
(`System.Refines.filterMapIO`). The simulation (`RaftKVProofs/Once.lean`) reads the same
committed list, by membership instead of counting: every request in flight or in an entry has
arrived, every answer along the list or waiting is empty or given, and the memo after the list
agrees with the keys taken. So a copy of a message changes nothing it says, and the duplicate
case is the delivery case.

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

The proofs give each node a ghost history of the states it has left (`Lanes/Proof/Past.lean`)
and build one invariant in layers with the monotone proof rule, so one argument covers every
fault: `Votes`, `Terms`, `Logs`, `Standing`, `Safe`, `Commits`. An `append` carries a batch, so
what a follower takes from a leader is a start of that leader's log (`Within`), and the layers
speak of that. What the layers say of a state
without its history is checked first, as properties of their own (`raftCheck "what the proofs
use, one term"`, and two deep ones). `Safe`, which is about what a majority may yet come to
hold, has no such form; it is checked only through the three properties it proves.
`Proofs/Axioms.lean` and `RaftKVProofs.lean` hold every theorem to Lean's three standard
axioms. `lake build` builds them; `raftCheck` does not link them.

## Before you run it

It is safe, and it is not yet something to leave running. An independent review killed and
paused its processes 392 times and found every acknowledged write linearizable, and found
these:

- **A node must come back with its journal.** The journal and the snapshot are a node's
  memory of the votes it gave and the entries it acknowledged. `raftNode` now refuses to start
  when its journal is not there, unless it is started as `new`, and refuses `new` on a journal
  that is there: a mistyped path or a disk that was not mounted is an error, where it was a
  node that remembered nothing. What is left is the journal that is really lost. The node
  cannot be given back what it knew, and started as `new` under its old id it votes again:
  with one other node behind, the two elect a leader that lacks a write the cluster has
  answered, and it stays lost when the third returns. This is outside what is proved, since
  the model's crash keeps what a node had, and replacing such a node safely needs a change of
  membership, which is not here. Nothing is synced to disk, so loss of power is such a loss.
- **The journal is cut now, and the log is not.** A node journals every message it is sent,
  heartbeats too: idle, a follower writes 5 kB a second and the leader 11, which was 470 and
  930 MB a day. A node now saves its state every 65,536 entries and cuts the journal: idle,
  that is every 7 to 18 minutes, and the journal stays under 6 MB. After 10,000 writes a
  node's process is back in a few tenths of a second, from its snapshot and what it journaled
  since. (The cluster took longer to answer again, 16 to 20 seconds with that log, saved or
  not, before appends were bounded: see below.) What is left: Raft's log is never compacted, so a node's
  state grows with every command, in memory and in the snapshot, by 60 to 90 bytes for a
  small write, and a save writes all of it while the node does nothing else. Saving the state
  of 10,000 small writes, 0.6 MB, delayed no write by a tenth of a second.
- **A node's configuration is part of its journal's name.** A start runs the step functions
  over the journal again, and they read the timeouts: a timer is due at the clock's reading
  plus the configured delay. Replayed under another timeout a node would have voted otherwise
  than it did. So the name a journal is kept under holds the node's id, the size of the
  cluster and every field of `Config` and of the HTTP gate's, and a node started with another
  is refused. There is no way yet to change a timeout of a node that has run.
- **A client that tries again after a `504` may have its write applied twice.** Requests are
  not told apart.

It also found that a leader sent a follower everything it had not acknowledged in one message.
A log over 16 MB could not be sent at all, so after a change of leader nothing committed
again; a follower that stopped reading made the leader hold many copies of what it had not
acknowledged; with a node down, each write cost more than the last. An `append` now carries at
most `maxAppend` entries (8). With 20 MB of 1 MB values and the leader killed, another node
answered a write three seconds later, where none did in six minutes; with a node down a write
sends that node nothing. What is left of the finding:

- **A follower more than a batch behind a new leader is walked through the whole log.** A new
  leader sends each follower the last `maxAppend` entries of its log. A follower that was up
  to date takes them. One that is not ignores them, and from the first heartbeat on is sent
  the log from its first entry, a batch for each acknowledgement: nothing tells the leader
  where a follower's log ends. At any time a follower is sent at most `maxAppend` entries per
  round trip.
- **A node that stops reading is still sent a batch on every heartbeat.** The heartbeat
  repeats the batch the node has not acknowledged, and the transport holds up to 1,024 of
  them: with a follower stopped, thirty writes of 100 kB and ten seconds, the leader grew to
  384 MB, where it grew to 1.3 GB before.
- **`maxAppend` counts entries and does not measure them.** That many of the largest must fit
  in the 16 MiB the transport takes as one message. The defaults do: 8 entries, each a value
  of at most 1 MiB (the limit on a request's body), its key and about 60 bytes.

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
- A way for a leader to learn where a follower's log ends (a refusal that says so, or a
  `nextIndex` that steps back), and to know what it has sent and not heard of. Without the
  first a follower far behind a new leader starts again from entry 1; without the second a
  heartbeat repeats a batch that may only be slow.
