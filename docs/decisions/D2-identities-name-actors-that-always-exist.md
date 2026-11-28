# D2. Identities name actors that always exist (virtual actors)

Status: Accepted

There is no spawn effect and no registry in the semantics. Identity types may be infinite
families (`account (n : Nat)`); an actor that has never run is in its `init` state and starts on
its first message. Actors listed in `System.boot` start when the system does.

Why: the global state is then a total function from identities to states, which is the simplest
thing to state invariants and refinement maps over. Dynamic populations (one session actor per
user) need no extra machinery. This is the Orleans model.
