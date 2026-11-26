# D?. A service behind actors is proved with one simulation, and an application gives only its steps

`Lanes/Semantics/Account.lean`, `Lanes/Semantics/Sent.lean`, `Lanes/Semantics/Link.lean`,
`Lanes/Semantics/Simulation.lean`, `Lanes/Semantics/Service.lean`, `Lanes/Actors/Run.lean`,
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
before held and owed. Usually it proves less: `Account.Handles` is what one step does, read
locally, from what the message carried and what the state held to what its sends carry, what
the state after holds and what took effect, and `Moves.handle` (a message delivered) and
`Moves.grow` (a timer, a recovery, a duplicate) do the arithmetic over the rest of the network.
A server that queues an input holds it in its state (`held`) and makes it take effect at a
flush; the ledger holds it in the witness; both are `Handles` with `held` moving, and neither
writes the multiset arithmetic. `Moves.forward`, `Moves.take` and `Moves.quiet` are the shapes
a step usually has, stated as equations about the step's sends and outputs, so a front end's
step closes by `rfl`; `Moves.of_loses` is a loss the value does not read. `Account.implements`
does the rest: the input, output, loss and crash cases and the internal steps of the spec
(`Service.takes`).

*Where messages come from.* Every proof had an invariant that no timer is armed and that each
message in flight has one of a few shapes, and decoded it in the delivery, duplicate and drop
cases. `System.Sent` is the inductive "an input the system accepts, or what some actor's step
or recovery sends from some state", `System.Armed` the same for timers, and `System.traced`
proves, once for every system and environment, that every message in flight is `Sent` and
every timer `Armed`. The cases of `Account.implements` take the witness: an application cases
on it and lets `simp` compute what that step sends, so the shapes are found, not stated. It is
weaker than a shape invariant of the application's own (the sending state is any state, not a
reachable one), which has been enough: the store, the batch server and the ledger lost theirs.

*What a step sends, computed.* D34 found that lemmas over an abstract signature do not fire as
`simp` lemmas on a concrete one. The cause is in the discrimination tree: an implicit argument
that is a type is a key, so `List.map` at `σ.Out` (`Effect.emits_map_emit`) is keyed on
`Signature.Out _`, while a concrete signature is an `abbrev` that reduces to its fields, and the
key there is the field's type itself. So `Lanes/Actors/Run.lean` now has `@[simp]` lemmas whose
left sides have no such argument: `sends`, `emits` and `armed` of `[]`, of each constructor
consed, of `++` and of a `map` (over a free type, the result a `filterMap` that `simp` reduces
for a concrete function). `simp [system, actor]` then computes a step's sends, outputs and
timers; nothing else in the repository changed under them.

*One link in order.* `linkMsgs src dst net` is the messages on one link, oldest first, with what
a send (`linkMsgs_append`, `linkMsgs_cons_self`), delivering the oldest on an ordered link
(`linkMsgs_of_deliverable`), a loss (`linkMsgs_erase_self`, `linkMsgs_erase_of_ne`) and a crash
of the receiver (`linkMsgs_down`) do to it. The ledger reads its users' links with it.

*Losses follow the environment.* `of_steps` asks that the relation survive every loss
(`SysState.Loses`), whatever the environment allows. The ledger rests on ordered links from
each user to the ledger, and its relation reads what is on them, so losing a message from the
middle of a link that does not lose would break it, and it has no proof by `of_steps`. `System.Refines.of_events` asks only for
the losses the environment has: a message dropped on a lossy link, an actor taken down when it
may crash or stops itself, timers; a delivery knows the message is deliverable, so on an ordered
link it is the oldest. Its cases are relation-preserving moves, so a crash may also be answered
by internal steps of the spec. `of_steps` is proved from it, and it takes deadlines (D42).

*The value is a relation with a witness.* The ledger decides a request at the user and serves it
at the ledger. It takes effect at the ledger, but the user's record has already moved, and the
move cannot be undone from the message (a log-in evicts a session). The witness is the list of
requests decided and not served, each marked with whether its message is still on the link, and
the relation says that the spec's record of each user, with that user's requests in the list
decided in order, gives the user's record and the messages on the user's link to the ledger. No ghost is needed (D34: an existential is free in a relation).

*Trace arguments.* A proof that a system does *not* refine its spec follows the spec along the
run with predicates stable under internal steps (`Service.Stable`). `Service.Only` is the usual
one: the inputs that may be pending, what they keep of the value and what they output.
`Service.Took` is "an output carrying an input's id waits only once that input has taken
effect": then the input is not pending and what it established holds.

*What it cost.* The store's refinement went from 155 lines to 83 with `Account`, and to 51 with
`Sent` (and `put` carrying its front end, from main); its stale-read argument from 101 to 74.
The batch server's file went from 197 to 125, and to 90. The ledger was 463 lines with each
user's link to the ledger assumed reliable; it is 481 with those links allowed to lose: its
witness marks each request with whether its message is still on the link, a loss or a crash of
the ledger unmarks, and when the ledger serves a message the unmarked requests before it take
effect if their user answered them, and are dropped if the book was to serve them, which leaves
the user's record as it was. Its shape invariant, its reading of a link and the answered
requests taking effect at a crash are gone; what was added is the marks (`decideAll_erase`,
`decideAll_eq_cons`, `decideAll_mark`) and the regrouping of the witness by user. Its premise is
now that each user's link to the ledger is ordered and does not duplicate.

Limits and what still repeats:

- *A witness read by key.* The ledger's witness is one list read per user, and replacing one
  user's part (`filter_regroup`, `held_regroup`) is list arithmetic it states itself. A witness
  that is a family by key, with `held` summed over it, would take it into the library.
- *No timers in three proofs.* The store and the ledger each prove that `Armed` is empty by
  cases on every step (`unarmed`, five lines); it is the same `simp` each time.
- *Raft is not moved.* Its pending side is the requests in flight and a `Finset` of entries
  past the committed list that covers every entry in a log or in an `append` in flight: `held`
  with the set and the list in the witness, and the covering condition in `value`, which reads
  the network. Its steps commit several entries at once, which `Moves` allows (`xs`). What it
  would gain is the input, output, loss and recovery cases and the iteration of `Sim.extend`
  over `Service.takes`, about 60 of its 552 lines; its per-step proof (`Accounts.grow`,
  `Sim.step`, about 150 lines) would be restated as `Handles`. That is not clearly shorter, so
  it was left as it is.
- *The relation ignores timers and which actors are up.* A system whose timers carry requests
  needs a `held` that reads them, which `Account` does not have.
