# D?. The checker at scale: a hash that sees order, a fingerprinted mode, reductions

Status: Accepted

`Lanes/Check/{System,SystemSound,Fingerprint,FingerprintSound,Reduce,ReduceSound}.lean`. The
videos example reached the 3,000,000 states its checks allow, and its scenarios were cut down: a
quiet worker where the worker's faults were not the point, only the site crashing where the
scheduler could too. D8 kept full states compared exactly and left fingerprints and parallel
search to a second engine, with the exact one kept. The owner asked for a checker that scales
further and runs faster, still proved. This is what was measured, what changed, and what did
not.

## What was measured

The scenarios of `examples/videos/Videos/Check.lean`, each alone, on four cores shared with
other work, with `perf` (sampled stacks) and the peak resident memory. Before any change:

| Scenario | States | Transitions | Time | Memory |
| --- | --- | --- | --- | --- |
| A video's life | 1,838,171 | 8,869,423 | 88 s | 1,522 MB |
| A video deleted while its check may be out | 1,648,323 | 7,593,908 | 53 s | 1,368 MB |
| A second check while the first may be out | 1,414,585 | 5,884,160 | 39 s | 1,166 MB |
| An upload never confirmed | 359,757 | 1,555,580 | 14 s | 317 MB |
| The pipeline | 2,852,633 | 13,264,488 | 286 s | 2,669 MB |

About 830 bytes a state, and 20,000 states a second. Where the time of a video's life goes:

- 49% finding duplicates. Four transitions in five lead to a state already stored, and each
  is confirmed by comparing the whole state: the driver (the browsers and the store's model,
  25 to 30%), the messages in flight (12%), the actors (7%). Lean's derived equality walks
  both values even where they share memory.
- 25% computing successors: the semantics, and the example's own model of the outside
  (its HMAC of every report, 5 to 10%).
- 9% hashing, and most of the rest allocating and freeing successors that are duplicates.

And 13% of the states stored in the scenario of a delete tried twice, 13% in the upload never
confirmed and 20% in the forged reports had a 64-bit hash another state had. Every one differed
from it only in the order of the messages on an ordered link: `SysState.trafficHash` sums over
the messages in flight, so it cannot see order, and on an ordered link order is part of the
state.

## What changed

**A hash that sees the order a link keeps** (`Check.Node.trafficHash`). Each message is hashed
with the number of messages before it on its link if the link is ordered, and with `0` if it is
not. Equivalent states keep the same hash (`Check.Node.trafficHash_eq`, so `Node` stays
`LawfulHashable` and counts stay exact), and the collisions are gone: none in any videos
scenario. In the exact search this changes little (14.5 s against 13.8 s for the upload never
confirmed, within the noise): a collision cost a comparison that failed early. It matters for
the fingerprinted mode, where a collision hides a state.

**A fingerprinted mode, off by default** (`Check.fingerprint`, `Check.systemFingerprinted`).
It keeps of each state seen only its hash, and of each state stored its parent's record and
which of the parent's transitions led to it (two numbers); states are held only while their
level waits to be expanded. A duplicate is found by comparing hashes, and nothing else. A trace is
rebuilt by replaying the recorded choices through `Model.next`, and what it shows is checked
again on the state it reaches. So what it reports is real whatever the hash
(`Check.fingerprint_violated`, `Check.fingerprint_deadlock`, `Check.fingerprint_witness`,
`Check.systemFingerprinted_violated`), and that is all that is proved: a state whose hash
collides with one seen is never explored, so a pass is not exhaustive. The report says so
(`Report.fingerprinted`, "PASS (fingerprinted)").

| Scenario | Exact, with the new hash | Fingerprinted |
| --- | --- | --- |
| A video's life, 1,838,171 states | 79 s, 1,518 MB | 48 s, 530 MB |
| An upload never confirmed, 359,757 states | 13.5 s, 316 MB | 9.2 s, 100 MB |
| A delete tried twice, 61,578 states | 1.3 s, 61 MB | 0.8 s, 38 MB |

The same states and transitions in each: with the new hash there was no collision.

**Parallel exploration, level by level** (`Fingerprint.Search.runParallel`, with
`Options.tasks`). The fingerprinted search is level-synchronous: it computes the successors of
a level, 4,096 states at a time, in tasks of 64, and stores them in order. It is the same
function as the sequential search (`Fingerprint.Search.runParallel_eq`, `Check.fingerprint_tasks`):
the same states stored in the same order with the same records, so the same verdict, counts and
traces. It does not help here: 9.1 s of wall time and 29 s of processor time for the upload
never confirmed, against 9.2 s on one core. The exact search's tasks (D33, `Search.runBatches`)
lose too: 16.7 s and 39 s against 13.5 s. D33's reasons hold. Lean counts references to an
object another thread has seen atomically and never updates it in place, so the table of seen
states must stay on one thread, and every state a worker made is shared: the search in tasks
takes about three times the processor time. On this machine the main thread and four workers share four cores.
Whether more idle cores win was not measured.

**Reductions with proofs** (`Model.reduce`, `Check.systemReduced`). A reduction replaces every
state the search reaches by a representative, `canon` of it. `Model.Reduction` is what `canon`
must satisfy: each state is related to its representative by `rel`, an equivalence that the
constraint and the properties respect and that is a simulation of the model. Then a complete
pass of the reduced search is a pass of the model, for `always` properties and so for a
refinement check (`Check.search_reduce_sound`, `Check.systemReduced_sound`), for deadlocks
(`Check.search_reduce_deadlock_free`) and for `sometimes` properties reported unreached
(`Check.search_reduce_unreached`); and what it reports is true of a reachable state of the
model, related to the one reported (`Check.search_reduce_violated`, `Check.search_reduce_deadlock`,
`Check.search_reduce_witness`). The one instance proved in general is the driver's state put in
a canonical form, under a relation the driver cannot see (`Driver.Simulation`,
`Check.World.Reduction.ofDriver`): a list the driver only reads as a set, kept sorted, which
`Tests/Reduce.lean` checks (600 states, 457 reduced) and `Tests/ReduceProofs.lean` proves.

## What did not change, and why

- **Symmetry over actor ids.** `Model.Reduction` takes any simulation, so a permutation of
  interchangeable actors is one, but no theorem yet says that `SysState.step` commutes with
  renaming actors: a renaming has to carry each actor's state, timers and messages, whose types
  depend on its id, and the system's `step`, `recover` and `accept` must commute with it. That
  is its own piece of work. The videos system has two actors that are not interchangeable, so it
  would gain nothing.
- **Partial-order reduction.** Sound forms need every transition left out to be invisible to the
  properties, and a proviso against ignoring one forever. In the videos checks nearly every
  transition changes what a property reads (the browsers' state, the site's), so the simple
  form would reduce little, and its proof was not started.
- **A compact encoding compared exactly.** It would replace the comparisons that take half the
  time with one pass over bytes. It needs an encoder for every state, message and driver type
  and a proof that it is injective up to `World.Equiv`, with the messages in flight in a
  canonical order. `Codec` is proved but writes a list of byte strings, numbers in decimal,
  and the videos driver and the outside models it uses have no codec. Not started.
- **A pointer comparison before the structural one.** `withPtrEq` cannot be used at a type
  variable, and an `implemented_by` that compares pointers is sound only for a reflexive `==`:
  it would be trusted code where the checker has none. Not done.
- **A smaller node.** A stored `Node` keeps both the world, with its functions read from the
  slots, and the slots: some 200 of its 830 bytes. Keeping only the slots would cut memory by a
  quarter, but every lemma of `SystemSound` reads `Node.world`. Not done.

## The old sizes

The cut-down videos scenarios, at the sizes they had before they were cut, in the fingerprinted
mode, with no bound reached. Each passed, with every witness reached. `examples/videos` still
checks the cut-down ones, exactly; whether to check these too, and how, is the owner's call.

| Scenario | States | Transitions | Time | Memory |
| --- | --- | --- | --- | --- |
| A video deleted while its check may be out, either actor crashing | 2,059,057 | 9,767,745 | 39 s | 472 MB |
| A second check while the first may be out, either actor crashing | 1,699,880 | 7,261,846 | 31 s | 378 MB |
| A video's life with the worker's faults | 7,371,678 | 38,775,151 | 409 s | 2,362 MB |
| The pipeline with either actor crashing and a job's start not answered, refused or `unknown` | 17,256,751 | 86,424,547 | 1,589 s | 6,228 MB |

The first two are within the exact search's bound of 3,000,000 states, and pass it with the
same counts: 59 s and 1,663 MB, and 42 s and 1,381 MB.
