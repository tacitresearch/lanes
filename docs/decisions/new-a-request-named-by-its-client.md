# D?. A request named by its client takes effect once, and its answer may be handed over again

`Lanes/Behaviours/Once.lean`, `Lanes/Semantics/Once.lean`, `Lanes/Check/Once.lean`,
`Examples/{KV,KVProofs}.lean`. Every refinement theorem so far assumed that some link does not
duplicate: `Examples.KV.implements` that no link does, `RaftKV.implementsMachine` that no
client's link to a node does, the gate's at-most-once that the link from outside does not. A
client retries, and a retry is a duplicate. The answer of Raft's client sessions and of Stripe's
idempotency keys is taken: the client names each request (its identity and a sequence number),
and the service acts on a name once and answers it again with what it answered.

- *The spec is a combinator on the service, with sets.* `Service.once svc key` has the value of
  `svc`, the inputs that have arrived, the keys that have taken effect and the answers given,
  each a set. An input arrives; one whose key has not taken effect may take effect, with `svc`'s
  step; an answer given may be handed over, and stays given. It is weaker than `Service.spec`
  in two named ways: a second request under a taken key never takes effect, and an answer may be
  handed over more than once. The second is forced, not chosen: a duplicate on the link into the
  actor that answers, or a client's retry after the answer was lost, has to be answered, and so
  the client sees the answer twice; it knows the name and can drop the repeat. The checker shows
  it: with the memo, the map spec without `once` is broken by an answer handed over twice.
- *Sets, because a relation built on membership cannot be broken by a copy.* A simulation that
  counts (`≤` on multisets, D34) is broken by a message handled twice: the spec has one pending
  request for two in flight. A simulation that says "every request in flight has arrived, every
  answer owed has been given" is not, and the spec's state only grows, so what it covered before
  a step it covers after. The duplicate case of a proof is then the delivery case with the
  message kept. `System.Refines.of_handles` is `of_steps` with that said once: deliveries,
  duplicates and timeouts are one obligation, an actor handling a message with any part of the
  network left, and the statement has no hypothesis on the environment at all.
- *The memo is a wrapper on the actor that acts, keyed by client, one entry each.*
  `Once.actor a key` remembers per client the last sequence number acted on and the effects of
  acting. The same number again gets the same effects (a read is answered with what it read
  then, not now); a lower one gets nothing; a higher one is acted on. An unbounded table of
  every key would be simpler to prove and is refused by rule 2.6. One entry per client is
  enough for a client that sends its next request once the last is answered, and the spec
  allows the rest: a request overtaken by a later one of its client stays arrived and never
  takes effect, which `once` permits as `spec` permits a lost request. The memo is durable; a
  restart that lost it would act on a repeat.
- *What was not taken.* A theorem from "implements `svc` where links do not duplicate" to
  "implements `once svc` where they do", for any system, by putting one deduplicating actor in
  front: the duplicates the existing theorems exclude are inside the system as well as in
  front (the store's link for the key-value store), a front cannot replay an answer it has not
  seen, and carrying a refinement of the right side of a join through the join has no theorem
  (D31 has the left side's). It would also be one actor for a distributed system.
- *The key-value store.* A front end is a client's session: the store's `put` now names the
  front end it came through, as `get` already did, and the key of a request is its front end and
  number. `onceSystem` is `system` with `Once.actor store`. Checked first, on one key, two
  values and two front ends: with every link duplicating, and with every link losing,
  reordering and duplicating and a crash, it refines `once` of the map spec; a client that
  retries its first write after its second gets one effect of each; without the memo that retry
  takes effect again, and a read duplicated on its way to the store is answered with two values.
  Then `Examples.KV.implements_once`, in every environment.
- *Checked, not proved: the monitor.* `Service.onceMonitored` is the subset construction for
  `once`, as `Service.monitored` is for `spec`; it has no soundness theorem yet.
