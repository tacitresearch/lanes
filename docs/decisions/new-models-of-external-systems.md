# D?. Models of external systems: classes in Lanes, vendors in integrations

A system talks to things it does not contain through outputs and inputs (D26), and what such a
thing may do is an `Outside` (`Lanes/Outside/Basic.lean`): the checker explores the system
against it, and a recorded run of the real thing is tested against it with `Outside.allows`.
Today there are three: the clock, the HTTP client and the jobs' pool. Applications will talk to
databases, object stores, queues and payment APIs, and each such model is a premise of every
theorem about the system that uses it. This decision is where those models go and what they
say. Only `Outside` has moved so far (to `Lanes/Outside/`); the rest is the plan.

## Classes, not vendors

`Lanes/Outside/` holds one model per class of external system, each an `Outside` with the
inputs and outputs of its class and the state that says what an answer may be:

- **A transactional store with an isolation level.** Requests are transactions of reads and
  writes; the model keeps the committed history, and what a transaction may read is what its
  isolation level allows (serializable, snapshot, read committed), so a system checked against
  `snapshot` is checked against write skew. A commit may fail as a conflict.
- **An object store.** Puts, gets, deletes and lists by key, with whether a read sees the last
  write (read-after-write, as S3 now gives, or eventual) and conditional writes by version.
- **A queue.** Delivery at least once with a visibility timeout, acknowledgement, and order per
  group or none; a message may come again after it was handled.
- **An effectful API with idempotency keys and webhooks.** A request that changes something
  carries a key; the model says a repeat with the same key has the effect once and answers as
  the first did, and that the effect may be reported later, once or more, as a webhook input.

## Combinators on `Outside`

What these share is written once, as functions from an `Outside` to an `Outside`:

- **An RPC with an ambiguous timeout**: a request is answered, refused, or times out, and a
  timeout says nothing about whether it took effect. Retrying is then only safe through the
  next one (rule 3.4).
- **Idempotency**: an outside whose requests carry keys, in which a repeat is the first's
  effect and answer, in the way `Service.once` is for a system's own spec (D48).
- **An event stream**: effects reported later, out of order and repeated, as inputs.

The models above are built from these, so a theorem proved against "an RPC with idempotency" holds
of every class built that way.

## Vendors in `integrations/`

A vendor (a particular database, object store or payment API) is a Lake package under
`integrations/`, outside `Lanes/`: its client and handler, and the claim that it conforms to a
class, which is a trusted premise. It is not proved. It is tested: the package records runs
against the real service or a local stand-in (a database in a container, a vendor's test mode)
and checks them with `Outside.allows` against the class's model, as `Tests/HttpClient.lean`
does for the HTTP client. A vendor that breaks its class's model breaks that test, not a proof.
This keeps `Lanes/` free of vendors' names and releases, and lets an integration be released, or
dropped, on its own.
