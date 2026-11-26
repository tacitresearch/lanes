# Plan

What is being worked on now, and why. The plan of the first slice and the findings of the five
review rounds, with what each fixed, are in `docs/history/plan-review-rounds.md`. When a step
here is done, take it off and put its result in `docs/status/`.

## Why this order

Lanes is for software an agent writes and nobody reads line by line, so a claim rests on a proof
(`docs/decisions/D45-everything-is-proved.md`). The proofs so far are of the framework and of
two applications that took hundreds of lines each; the checker, not a proof, still carries the
ledger. So the work is to make a proof cheap enough to be routine, to show for every definition
what rests on what, and to give applications the library they need without growing what is
trusted. Launch work (the flagship application, deployment, the write-up) waits for these,
because a launch claim is what a critic tests first.

## In progress

1. **Proving an application is cheap.** A library for the simulation relations every
   request-and-reply service repeats, a cheaper invariant rule, then a counterexample-to-induction
   finder. The measure is `systems/ledger`'s refinement of its spec, proved, where today it is
   checked on instances.
   Done towards it: a request named by its client takes effect once (`Service.once`, D48), and
   `System.Refines.of_handles`, a relation rule that a duplicated message cannot break.
2. **Evidence for every definition of `Lanes/`.** The inventory is generated (`docs/INVENTORY.md`,
   D47); what has none is listed in `docs/inventory-none.md`, which only shrinks. Take entries off
   it by proving, testing or listing them in `TRUSTED.md`.
3. **The standard library**, triaged from Go's in `docs/STDLIB.md`. Its P0 steps 7 (`fsync`) and
   8 (libsodium) are done (`docs/decisions/D46-bind-what-touches-physics.md`). Next, each on its
   own branch: base64, IP addresses, media types and time formats, which depend on nothing; then
   URLs and rate limits, which need IP addresses; then TLS and names in the HTTP client.
4. **Less trusted, fewer premises.** Our own HTTP/1.1 request reader in place of `Std.Http`'s;
   the premise that a client's link does not duplicate taken off the gate and Raft, as D48 took it
   off the key-value store; idle actors not at their start saved when they rest and read back when mail comes (those at
   their start are released already), which waits for a place to keep their state.
5. **Slow work that is not one request's**, as the ledger's friction log asks
   (`systems/ledger/README.md`): background jobs, ending sessions in bulk, statements.
6. **Short, current docs.** One rules file (`AGENTS.md`), `docs/ARCHITECTURE.md` in place of the
   original design, this page and `docs/ROADMAP.md` without their history, and `lanes lint`
   checking that docs cite files that exist.
