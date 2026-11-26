# Status

Where the implementation stands against `DESIGN.md`. Update this file in the same change that
moves an item.

Last updated: 2026-11-26.

## Working

| Area | What exists | Where |
| --- | --- | --- |
| Actor API | `Actor`, `Signature`, `Effect`, `System`, `EnvModel`; `actor_invariant` tactic | `Lanes/Actors/{Actor,System}.lean` |
| Semantics | One executable step function; per-event lemmas; per-actor invariants lift to systems | `Lanes/Actors/{World,Step,Lift}.lean` |
| Deterministic scheduler | Seeded runs, replayable event lists, drivers for the outside world | `Lanes/Actors/Scheduler.lean` |
| Model checker | Breadth-first, exact states, `always`/`sometimes`, constraints, deadlock, coverage, shortest traces; refinement to a `Service` without a mapping | `Lanes/Check/` |
| Concurrent runtime | Task and bounded mailbox per actor, timers, self-stop, restart policy; recorded traces replay through the semantics | `Lanes/Actors/Runtime.lean` |
| Proof layer | `Spec`, `Refines` (weak simulation with a label map), `of_map`, `trans`, trace inclusion; system semantics as a CSLib `LTS`; `Service.spec`; sum lemmas | `Lanes/Semantics/` |
| Behaviours | `Server` (request and reply), with `Server.implements` proved | `Lanes/Behaviours/Server.lean`, `Lanes/Semantics/Service.lean` |
| Web | HTTP/1.1 adapter, requests and responses as data, `Html` with proved escaping, template macro | `Lanes/Env/Http.lean`, `Lanes/Http/`, `Lanes/Html/` |
| Data | `Enum`, JSON (parser, printers, `ToJson`/`FromJson`), all total and `Std`-only | `Lanes/Data/` |
| Tooling | `lanes new`, `lanes lint` (text-level), `lanes check`; CI workflow; axiom gate | `LanesCli/`, `.github/workflows/ci.yml`, `Tests/Axioms.lean` |

## Reference apps

| App | Checked | Proved |
| --- | --- | --- |
| Bank (`Examples/Bank.lean`) | Conservation on 2 accounts; lost-credit bug found under lossy links; runs on the runtime and over HTTP | Balance never negative (all environments); money conserved for any number of accounts in a faultless environment |
| Key-value store (`Examples/KV.lean`) | Refines the map spec; stale-read bug of a read cache found | Not yet |
| Leader election (`Examples/Election.lean`) | At most one leader per term on 3 nodes with reordering and a crash (165k states); split-brain bug found | Not yet |

## Against the DESIGN exit criteria

- **Phase 1** (runtime and actor API): met, except that the gateway app does not exist and the
  election invariant is checked, not proved.
- **Phase 2** (semantics, specs, refinement): semantics, lifting theorem and refinement theory
  are in. Trace checking runs in the test suite. Not done: the scheduler simulation proof, the
  Raft KV store.
- **Phase 3** (model checking and system proofs): checker finds the seeded split-brain bug;
  money conservation is proved for all instances. Not done: at-most-one-leader proof,
  counterexample-to-induction finder, `lanes prove`, symmetry reduction, parallel search.
- **Phases 4 to 8**: only the HTTP server adapter, the HTML layer and JSON exist.

## Next, in order

1. Prove election safety for all instances. It needs the quorum library (majority intersection
   on Mathlib's `Finset.card`), which Raft needs too.
2. Counterexample-to-induction finder and `inv_split`, then `lanes prove`.
3. Refinement proof for the key-value store with front ends (the first multi-actor refinement).
4. Persistence adapter, so `Actor.recover` is backed by storage, then crash faults in the runtime.
5. Raft: protocol model, invariants, refinement to `ReplicatedLog`, reference implementation.
6. Checker v2: fingerprints, parallel search, compact state representation.

## Known limits

- The checker runs about 17k states per second (measured on the election model, 4 cores,
  single-threaded). Fine for small instances; v2 is needed for Raft-sized ones.
- `lanes lint` is text-level. `no-io-in-step`, `bounded`, `field-leak` and `fn-length` need the
  elaborator and are not implemented.
- Templates take text children as string literals (`<p>"text"</p>`), not bare text.
- No TLS, HTTP client, WebSockets or database adapter. `Std.Http` has no client.
- The runtime's in-memory "durable" state does not survive a process crash (see `TRUSTED.md`).
- The runtime never releases an actor: every identity ever addressed keeps its cell, task and
  mailbox. A session-per-user system grows without bound. Releasing an actor means its state must
  live somewhere else, so this waits for the persistence adapter (item 4 above).
- An actor's outbox (sends waiting for a full mailbox) has no bound of its own. It is bounded
  only by the back-pressure full mailboxes put on inputs from outside.
- Templates cannot contain inline `<script>` or `<style>` text, and URL attributes accept only
  relative, `http`, `https`, `mailto` and `tel` URLs.
- The CI workflow has not run yet: it triggers on pull requests and on `main`.
