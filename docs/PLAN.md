# Plan

What is being worked on now, and why. The plan of the first slice and the findings of the five
review rounds, with what each fixed, are in `docs/history/plan-review-rounds.md`. When a step
here is done, take it off and put its result in `docs/status/`.

## Why this order

Lanes is for software an agent writes and nobody reads line by line, so a claim rests on a proof
(`docs/decisions/D45-everything-is-proved.md`). The proofs so far are of the framework and of
applications that took hundreds of lines each. So the work is to make a proof cheap enough to be routine, to show for every definition
what rests on what, and to give applications the library they need without growing what is
trusted. Launch work (the flagship application, deployment, the write-up) waits for these,
because a launch claim is what a critic tests first.

## In progress

1. **Proving an application is cheap.** A library for the simulation relations every
   request-and-reply service repeats, a cheaper invariant rule, then a counterexample-to-induction
   finder. The measure is `examples/ledger`'s refinement of its spec.
   Done towards it: a request named by its client takes effect once (`Service.once`, D48),
   `System.Refines.of_handles`, a relation rule that a duplicated message cannot break, and
   deadlines that pass where a message is served, with which the ledger's timed refinement is
   proved (`Account.implements_timed`, `Ledger.implements_timed`).
2. **Evidence for every definition of `Lanes/`.** The inventory is generated (`docs/INVENTORY.md`,
   D47); what has none is listed in `docs/inventory-none.md`, which only shrinks. Take entries off
   it by proving, testing or listing them in `TRUSTED.md`.
3. **The standard library**, triaged from Go's in `docs/STDLIB.md`. Of its P0, all is done but
   a table of rate-limit buckets per key and TLS and names in the HTTP client, each proved
   against its spec and tested against Go (`docs/decisions/D50-differential-tests-against-go.md`).
4. **Less trusted, fewer premises.** The premise that a client's link does not duplicate taken off the gate and Raft, as D48 took it
   off the key-value store; idle actors not at their start saved when they rest and read back when mail comes (those at
   their start are released already), which waits for a place to keep their state.
5. **Slow work that is not one request's**, as the ledger's friction log asks
   (`examples/ledger/README.md`). The jobs actor is in (`Lanes/Behaviours/Jobs/Basic.lean`). Left: the
   answer carried to its requester through the join, at most once there, as the gate's is; a
   queue for jobs beyond `maxInFlight`; ending sessions in bulk and statements in the ledger.
6. **Short, current docs.** One rules file (`AGENTS.md`), `docs/ARCHITECTURE.md` in place of the
   original design, this page and `docs/ROADMAP.md` without their history, and `lanes lint`
   checking that docs cite files that exist.
7. **Models of external systems.** Classes of external system as models under `Lanes/Outside/`
   (a transactional store with an isolation level, an object store, a queue, an API with
   idempotency keys and webhooks), built from combinators on `Outside` (an RPC whose timeout is
   ambiguous, idempotency, an event stream), and vendors as packages under `integrations/` whose
   conformance to a class is a trusted premise tested against the real service. The combinators
   and the API with idempotency keys and webhooks are written, with payments and email as
   instances (`Lanes/Outside/Effects/`, `examples/payments`), and the object store, with an S3
   client (`Lanes/Outside/ObjectStore.lean`, `Lanes/Web/IO/S3.lean`), and email through SES in
   `integrations/aws`, against a fake; next are the store and the queue, and a first integration
   that records runs of a real service.
