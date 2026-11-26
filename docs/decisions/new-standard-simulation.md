# D?. A service behind actors is proved with one simulation, and an application gives only its steps

`Lanes/Semantics/Account.lean`, `Lanes/Semantics/Simulation.lean`, `Examples/KVProofs.lean`,
`systems/ledger/Ledger/Proofs/Refines.lean`. The project proves every application refines its
spec, so a refinement proof has to be routine. Three were written by hand: the batch server
(`Tests/BatchProofs.lean`), the key-value store behind front ends (`Examples/KVProofs.lean`) and
Raft (`systems/raft-kv/RaftKVProofs/Refines.lean`). Each defined the same relation with
`System.Refines.of_steps` (D34) and proved the same lemmas about it.

*What repeats.* Each relation has three parts: the spec's value is read from the actors' states
(or from a witness: Raft's committed list); the spec's pending inputs are at least those the
system still holds, on messages in flight (`pend`) and in states or the witness (`held`); the
spec's outbox is at least the outputs waiting, those on their way (`owe`) and those owed by a
state (`owing`). Then each proof shows: an input adds one to both sides; an output is in the
spec's outbox; losing messages lowers only the left side; a delivery either passes on what the
message carried (KV's `forward`) or makes inputs take effect, one internal step of the spec each
(KV's `take`, Batch's `serves`, Raft's `extend`). Only the last is about the application, and in
it only the step of the actor: which inputs took effect and what its sends and outputs carry.

*The library.* `Account sys S W` is the four readings (`pend`, `owe`, `held`, `owing`) and the
value relation. `Account.Sim` is the relation. An application proves, for each message an actor
handles, `Account.Moves`: from any value its relation allows, some inputs `xs` take effect
(`Service.run`), and what the state after holds and owes, with `xs`, is at most what the state
before held and owed. `Moves.forward`, `Moves.take` and `Moves.of_le` are the three shapes a step
has, stated as equations about the step's sends and outputs, so a front end's step closes by
`rfl`. `Account.implements` does the rest: the input, output, loss, crash and restart cases,
the internal steps of the spec (`Service.takes`), and the duplicate and timer cases from
`Moves` too.

*Losses follow the environment.* `of_steps` asks that the relation survive every loss
(`SysState.Loses`), whatever the environment allows. A system whose correctness rests on an
ordered, lossless link (the ledger's user-to-ledger links) has a relation that losing one
message from the middle of that link breaks, and so no proof by `of_steps`.
`System.Refines.of_events` asks only for the losses the environment has: a message dropped on a
lossy link, an actor taken down when it may crash or stop, timers. `of_steps` is now proved from
it. In `Account.implements` the readings over the network are monotone by construction; only a
value relation that reads the network has to say why the environment's losses keep it.

*The value is a relation with a witness.* The ledger decides a request at the user and serves it
at the ledger; it takes effect at the ledger, but the user's record has already moved, and the
moves cannot be undone from the messages (a log-in evicts a session). Its value relation says
that the spec's record of each user, with the requests the user has decided and the ledger has
not served (the witness, a list), decided in order, gives the user's record and the messages on
the user's link to the ledger. No ghost is needed (D34's argument: an existential is free in a
relation).

*Trace arguments.* A proof that a system does *not* refine its spec follows the spec along the
run with predicates stable under internal steps (`Service.Stable`). `Stable.of_inputs` gives the
usual one: the inputs that may be pending, what they keep of the value and what they output.
`Stable.took` is "an output carrying an input's id was produced when that input took effect":
once an output of the id is in the outbox, the input is not pending and what it established
holds.

Limits:

- *Raft is not moved.* Its pending side is a set of entries with a covering condition, which is
  `held` with the set in the witness, and its value is `Logged`; it fits, but its proof was
  left as it is.
- *The relation ignores timers and which actors are up.* A system whose timers carry requests
  (a retry that holds the request) needs a `held` that reads them, which `Account` does not have.
