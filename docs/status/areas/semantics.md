### Semantics

Where: `Lanes/Core/{World,Step,Run}.lean`, `Lanes/Proof/`.

- A five-case proof rule for invariants that hold under every fault, built in layers (`Monotone.and_net`, `and_state`, `of_iff`).
- A kind of message that only the outside sends is handled no more often than it is put in, where the links from outside do not duplicate (`System.handled_le_put`).
- A system behind hidden inputs and outputs does what it does in the open, event for event (`SysState.run_filterMapIO`, `System.Invariant.filterMapIO`).
- Ghost histories with an erasure theorem.
- One executable step function.
- Per-actor invariants lift to systems.
- Per-event lemmas.
- Projection of a join's runs, for the left side: a run of the join, seen from `a`, is a run of `a` alone that shows the same deeds, the messages its actors handle and the outputs handed over (`SysState.run_left`), so a count of what `a` does that is proved of `a` alone holds in any join.
- Projection of a join: a reachable state of `a.join b w` seen from `a` is a reachable state of `a` alone with a network link from outside (`System.Reachable.left`), so invariants of `a` hold of it inside any join (`System.Invariant.join_left`); the same for `b` up to the order of messages on different links, and exactly when the boot of `a` sends `b` nothing.
