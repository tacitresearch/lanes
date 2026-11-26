# D26. An adapter is a model of the outside and a handler, tested against each other

`Lanes/Actors/Outside.lean`, `Lanes/Env/Clock.lean`. Whatever a system does not contain (a
client, a clock, another service) reaches it through outputs and inputs, never through an
effect that does IO, so `step` stays pure and every answer from outside is in the journal when
a shard is replayed. An adapter for such a thing is two parts:

- an `Outside`: which inputs the thing may send, given what it has seen. The checker explores
  the system against it (`Outside.driver` with a few sample inputs), and theorems name it as
  their assumption;
- a handler: what the real thing does with an output, in IO.

A conformance test records a real run and checks it with `Outside.allows`: the real thing did
only what the model allows.

Why: a property checked against a model of the outside says nothing if the real outside does
something else, and nothing else ties the two together. The gate's guarantee assumed request
ids are never reused; that assumption is now `Http.outside`, and the real server is tested
against it.

Why a model and not an actor: an actor is deterministic, and what the outside does is a
choice. The semantics already puts every choice in the events, and inputs are events.

Consequences:

- `Runtime.idle` waits for the system, not for an adapter that is about to answer. A test waits
  for the answer it expects.
- Outputs are handed over in an order the semantics does not fix. A model that assumed the
  order of outputs was caught by the checker while this was being written.
