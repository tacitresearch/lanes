# D21. A proof rule for invariants no fault can break

Status: Accepted

`Lanes/Proof/Monotone.lean`. `System.Inductive.of_monotone` proves an invariant under every
environment model from five cases: the blank state, an input, an actor's step, an actor's
recovery, and that removing messages, timers and outputs keeps it.

`System.Monotone` is the five cases as a value. `Monotone.and` adds a property to one already
shown, each case assuming the first of the state it starts from and ends in, so an invariant is
built in layers without restating the earlier ones. `Monotone.timers` is the layer nearly every
protocol starts from: timers carry only what actors arm.

Most layers read the actors' states and ask something of each message in flight, and for
those the cases about removing and about an input say nothing new. `Monotone.and_net` takes
one fact in their place: the layer survives any change of what is in flight that brings no
message but inputs. `Monotone.and_state` is the same for a layer that reads only the states.
Layers added this way nest as `((A ∧ B) ∧ C) ∧ D`; `Monotone.of_iff` gives the stack a
structure with a field for each layer, so that a proof reads `h.votes` and not `h.1.1.2`.
`SysState.Pending` is what a step case knows of the message handled once the timers layer is
in: it is in flight, or one of the timers actors arm.

Why: a direct proof has eight event cases and must reason about erased messages, filtered
mailboxes and crashes, although loss, duplication, reordering and crashes can only remove
things or replay a step. This is the usual "the network is a set of messages ever sent"
argument of Raft and Paxos proofs, stated once for the Lanes semantics. It does not fit
invariants that count messages in flight, such as conservation of money; those are false under
loss anyway and are proved directly for a faultless environment.
