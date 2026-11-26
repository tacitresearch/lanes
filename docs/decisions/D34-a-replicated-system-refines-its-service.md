# D34. A replicated system refines its service by a relation, not a mapping

`Lanes/Semantics/Simulation.lean`, `Lanes/Actors/Loses.lean`,
`systems/raft-kv/RaftKVProofs/Refines.lean`. Rule 5.4 asks for a refinement map that is a short
projection, with history added to the implementation where the map needs it. For the Raft
cluster that was the first plan: a ghost for the commands that have taken effect and a ghost
that counts requests, so that the service's `pending` is a function of the state. It was not
taken.

- *`pending` is bounded, not computed.* A request that a link loses, that a follower drops, or
  whose entry a later leader replaces is never served. The service allows that: it stays in
  `pending` for ever. So the simulation says only that `pending` has at least the requests in
  flight and those of the entries that may still be committed. With `≤` in place of `=`, losing
  a message cannot break the relation, nothing has to remember what was lost, and no ghost
  counts inputs. `Ghost` is per actor and could not have counted a request that never reaches
  one.
- *The relation is existential in the committed list.* `Sim c t log` holds for some `log` that
  is committed (`Committed`) and that every node's committed entries are a start of. The
  longest such list is not a function anyone has to define; the proof only ever extends the
  one it has, by what the node that moved has newly committed.
- *`Refines` already allowed it.* It is a weak simulation: a step is answered by a saturated
  step, so one step of a node that commits three entries is three internal steps of the
  service. `Refines.of_map` is the special case with one. What was missing was a way in for a
  `System`: `System.Refines.of_steps` is `Inductive.of_monotone` for refinement. The relation
  must survive losing messages and timers (`SysState.Loses`, which is `Below` with the outbox
  kept exactly and the network as a sublist, since a refinement counts); then an input, an
  output, a delivery, a second handling, a timer and a recovery are left, each without loss.
- *Ghosts go one way and back.* The invariants are about the cluster with its history, so the
  simulation is too, and `System.Refines.of_ghost` gives the statement about the cluster that
  runs (`Refines.of_lift`: refinement carried back along a function that forgets state the
  steps do not read).
- *Checked first, and the hypothesis with it.* The statement assumes only that the link from
  outside to a node does not duplicate. The checker passes with lossy, reordering and
  duplicating links between nodes and with requests lost on the way in, and with a duplicating
  link from outside it finds a request answered twice in 18 steps.
- *What it cost.* Lemmas over an abstract signature do not fire as `simp` lemmas on a concrete
  one when a type such as `σ.Out` is an argument (`Effect.emits_map_emit`): the discrimination
  tree keys on `Signature.Out _`. `Effect.emits_map`, whose arguments are `Effect σ i` and a
  free type, does. The proof reads the invariant of `Commit.lean` (`Committed`, its
  `comparable` and `grow`, `Commits.nodes`), not the headline theorems, because a step needs
  the invariant before and after with the history between them.
- *The second user.* The key-value store with front ends (`Examples/KVProofs.lean`) took
  `of_steps` with no ghost and a relation of three bounds, each a `filterMap` over the messages
  in flight, so losing a message was two lines and the eight deliveries closed by `rfl` once
  two lemmas (a front end passes a request on; the store makes one take effect) took the new
  network and outbox as equations. What it showed is that those two lemmas, and the input,
  output and loss cases, are the same in every service behind actors and belong in the library,
  and that the duplicate and timer cases are noise when the environment and the actors rule
  them out.
