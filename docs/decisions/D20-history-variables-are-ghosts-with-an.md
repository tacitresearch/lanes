# D20. History variables are ghosts with an erasure theorem

Status: Accepted

`Lanes/Proof/Ghost.lean`. A `Ghost` gives each actor a history, updated on every step from the
state and the message. `SysState.erase_step` proves the system with ghosts takes exactly the
steps of the system without them, so `System.Invariant.of_ghost` carries an invariant proved
with histories to the real system.

Why: protocol safety often needs the past ("this node voted for that candidate in term 3").
The alternatives were to store the history in the actor's real state, which costs memory at run
time and changes the code being verified, or to prove about traces, which is heavy. A ghost
costs nothing at run time, and there is a theorem saying so.

`Lanes/Proof/Past.lean` has the one ghost most proofs want: `Ghost.past` keeps every state an
actor has left, and `SysState.seen` is those with the present one. Proofs that state the past
over `seen` share a ghost, so one can use the other's invariant; with a ghost each they could
not be combined. The Raft proofs (`examples/raft-kv/RaftKV/Proofs/`) are written this way.
