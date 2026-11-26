# D?. A service behind actors is proved with one simulation, and an application gives only its steps

`Lanes/Semantics/Account.lean`, `Lanes/Semantics/Simulation.lean`, `Lanes/Semantics/Service.lean`,
`Examples/KVProofs.lean`, `Tests/BatchProofs.lean`, `systems/ledger/Ledger/Proofs/Refines.lean`.
The project proves every application refines its spec, so a refinement proof has to be routine.
Three were written by hand: the batch server, the key-value store behind front ends and Raft
(`systems/raft-kv/RaftKVProofs/Refines.lean`). Each defined the same relation with
`System.Refines.of_steps` (D34) and proved the same lemmas about it.

*What repeats.* Each relation has three parts: the spec's value is read from the actors' states
(or from a witness: Raft's committed list); the spec's pending inputs are at least those the
system still holds, on messages in flight and in states or the witness; the spec's outbox is at
least the outputs waiting, those on their way and those a state owes. Then each proof shows: an
input adds one to both sides; an output is in the spec's outbox; losing messages lowers only the
left side; a delivery either passes on what the message carried (the store's front ends) or
makes inputs take effect, one internal step of the spec each (the store, the batch server's
flush, Raft's commit). Only the last is about the application, and in it only the step of the
actor: which inputs took effect, and what its sends and outputs carry.

*The library.* `Account sys S W` is four readings, the input a message carries (`pend`), the
output one carries (`owe`), those the states and a witness `W` hold (`held`, `owing`), and the
value relation. `Account.Sim` is the relation. An application proves, for each message an actor
handles, `Account.Moves`: from any value the relation allows, some inputs `xs` take effect
(`Service.run`), and what the state after holds and owes, with `xs`, is at most what the state
before held and owed. `Moves.forward`, `Moves.take` and `Moves.quiet` are the shapes a step
usually has, stated as equations about the step's sends and outputs, so a front end's step
closes by `rfl`; `Moves.of_loses` is a loss the value does not read. `Account.implements` does
the rest: the input, output, loss and crash cases and the internal steps of the spec
(`Service.takes`).

*Losses follow the environment.* `of_steps` asks that the relation survive every loss
(`SysState.Loses`), whatever the environment allows. The ledger rests on ordered, lossless
links from each user to the ledger, and its relation is broken by losing one message from the
middle of such a link, so it has no proof by `of_steps`. `System.Refines.of_events` asks only for
the losses the environment has: a message dropped on a lossy link, an actor taken down when it
may crash or stops itself, timers; a delivery knows the message is deliverable, so on an ordered
link it is the oldest. Its cases are relation-preserving moves, so a crash may also be answered
by internal steps of the spec: when the ledger crashes, the requests its users had answered take
effect. `of_steps` is proved from it, and it takes deadlines (D42).

*The value is a relation with a witness.* The ledger decides a request at the user and serves it
at the ledger. It takes effect at the ledger, but the user's record has already moved, and the
move cannot be undone from the message (a log-in evicts a session). The witness is the list of
requests decided and not served, and the relation says that the spec's record of each user, with
that user's requests in the list decided in order, gives the user's record and the messages on
the user's link to the ledger. No ghost is needed (D34: an existential is free in a relation).

*Trace arguments.* A proof that a system does *not* refine its spec follows the spec along the
run with predicates stable under internal steps (`Service.Stable`). `Service.Only` is the usual
one: the inputs that may be pending, what they keep of the value and what they output.
`Service.Took` is "an output carrying an input's id waits only once that input has taken
effect": then the input is not pending and what it established holds.

*What it cost.* The store's refinement went from 155 lines to 83, of which 43 are its readings and
its invariant; its stale-read argument from 101 to 74; the batch server's file from 197 to 125.
The ledger, proved for the first time, is 463 lines, with the crash of the ledger about 90 of them.

Limits and what still repeats:

- *Every proof restates where messages come from.* The store, the batch server and the ledger
  each prove an invariant that no timer is armed and that each message in flight has one of a
  few shapes (from outside to a front end, from a front end to the store), by
  `Monotone.timers` and `and_net`, and then decode it in the delivery, duplicate and drop cases.
  A layer "every message in flight is one that `accept` makes or some actor's step sends" is
  provable once, for every system.
- *Moving an input between a message and the state.* The batch server's queue and the ledger's
  witness take an input off a message and hold it, and later make it take effect from there;
  both are written as `Moves` by hand, with the same multiset arithmetic. They are `forward` and
  `take` with `held` in place of a message.
- *What a step sends and outputs* is computed in every proof (`sends_tell`, `ledger_sends`), and
  the lemmas over an abstract signature do not fire on a concrete one (D34).
- *A link read in order.* The ledger reads the messages on each user's link with a `filterMap`
  of its own, with four lemmas; the messages on one link, in order, with what delivering the
  oldest, sending, dropping and crashing do to them, belong in the library.
- *The ledger's links to the ledger must not lose.* The checker passes with links that lose
  (`Check.lean`): a lost answer can take effect when the message before it on the link is served.
  The relation does not say so; one whose witness marks lost answers would.
- *Raft is not moved.* Its pending side is a set of entries with a covering condition, which is
  `held` with the set in the witness, and its value is `Logged`; it fits, but its proof was
  left as it is.
- *The relation ignores timers and which actors are up.* A system whose timers carry requests
  needs a `held` that reads them, which `Account` does not have.
