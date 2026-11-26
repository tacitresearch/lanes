# Status

Where the implementation stands against `DESIGN.md`. Update this file in the same change that
moves an item.

Last updated: 2026-11-27.

## Working

| Area | What exists | Where |
| --- | --- | --- |
| Actor API | `Actor`, `Signature`, `Effect`, `System`, `EnvModel`; `actor_invariant` tactic | `Lanes/Actors/{Actor,System}.lean` |
| Semantics | One executable step function; per-event lemmas; per-actor invariants lift to systems; ghost histories with an erasure theorem; a five-case proof rule for invariants that hold under every fault | `Lanes/Actors/{World,Step,Lift,Ghost,Monotone}.lean` |
| Deterministic scheduler | Seeded runs, replayable event lists, drivers for the outside world | `Lanes/Actors/Scheduler.lean` |
| Model checker | Breadth-first, exact states, `always`/`sometimes`, constraints, deadlock, coverage, shortest traces; refinement to a `Service` without a mapping. Proved: it lists exactly the enabled events of a state, merging states is safe, a complete PASS means every `always` property holds in every world of the instance (`Check.system_sound`; `==` must be equality on actor states and the driver's state, so not yet under a monitored driver), the spec monitor accepts exactly what the spec allows, and every trace the search reports is real (`Check/SearchSound.lean`) | `Lanes/Check/`, `Lanes/Semantics/Monitor.lean` |
| Runtime | A kernel of pure functions (routing, start and stop, timers, batching, idleness) proved to follow the semantics whatever its caller does (`Kernel.exec_reachable`, `Kernel.exec_outputs`), inside a 185-line shell: one thread per shard, bounded inbox. A message costs the same at 1,000 and 100,000 actors | `Lanes/Actors/{Kernel,KernelSound,Runtime}.lean` |
| Proof layer | `Spec`, `Refines` (weak simulation with a label map), `of_map`, `trans`, trace inclusion; system semantics as a CSLib `LTS`; `Service.spec`; sum lemmas | `Lanes/Semantics/` |
| Behaviours | `Server` (request and reply), with `Server.implements` proved | `Lanes/Behaviours/Server.lean`, `Lanes/Semantics/Service.lean` |
| Web | HTTP/1.1 adapter whose logic is the gate actor (each request answered exactly once, model-checked); requests and responses as data; `Html` with escaping proved safe, URL attributes checked at render (tested, not proved); scoped template macro with components, fragments and attribute splices; typed routes (`Route.match?_link`, `percentDecode_percentEncode` proved); htmx attributes as typed values taken from routes | `Lanes/Http/`, `Lanes/Env/Http.lean`, `Lanes/Html/` |
| Data | `Enum`, JSON (parser, printers, `ToJson`/`FromJson`), majority quorums (`Quorum.majority_inter`), all total and `Std`-only | `Lanes/Data/` |
| Tooling | `lanes new`, `lanes lint` (text-level), `lanes check`; CI workflow; axiom gate | `LanesCli/`, `.github/workflows/ci.yml`, `Tests/Axioms.lean` |

## Reference apps

| App | Checked | Proved |
| --- | --- | --- |
| Bank (`Examples/Bank.lean`) | Conservation on 2 accounts; lost-credit bug found under lossy links; runs on the runtime and over HTTP | Balance never negative (all environments); money conserved for any number of accounts in a faultless environment |
| Key-value store (`Examples/KV.lean`) | Refines the map spec; stale-read bug of a read cache found | Not yet |
| Leader election (`Examples/Election.lean`) | At most one leader per term on 3 nodes with reordering and a crash (165k states); split-brain bug found | At most one leader per term for any number of nodes and terms under every environment model: loss, duplication, reordering, crashes (`Examples/ElectionProofs.lean`) |

## Against the DESIGN exit criteria

- **Phase 1** (runtime and actor API): met, except that the gateway app does not exist. The runtime's logic is proved, which Phase 1 did
  not ask for.
- **Phase 2** (semantics, specs, refinement): semantics, lifting theorem and refinement theory
  are in. Trace checking runs in the test suite. Not done: the scheduler simulation proof, the
  Raft KV store.
- **Phase 3** (model checking and system proofs): checker finds the seeded split-brain bug;
  money conservation is proved for all instances. At most one leader per term is proved. Not done:
  counterexample-to-induction finder, `lanes prove`, symmetry reduction, parallel search.
- **Phases 4 to 8**: only the HTTP server adapter, the HTML layer and JSON exist.

## Next, in order

1. Make the monotone proof rule cheaper to use, from what the election proof showed: a variant
   that takes per-state, per-message and per-timer predicates and discharges `below` itself, a
   frame lemma for the actors that did not move, and projections for ghost state.
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
- The gate keeps waiting requests in a list, so each request costs time linear in `maxPending`.
- The runtime's in-memory "durable" state does not survive a process crash (see `TRUSTED.md`).
- The runtime never releases an actor: every identity ever addressed keeps its cell in the
  kernel. A session-per-user system grows without bound. Releasing an actor means its state must
  live somewhere else, so this waits for the persistence adapter.
- One shard only. Several shards, and with them parallelism, are not built yet.
- Handing one input to a sleeping shard costs a thread wake-up, about 90 µs here. A busy shard
  does not sleep between inputs.
- That the kernel's agenda holds exactly the pending timers is tested, not proved.
- The kernel's message queue has no bound of its own (see `TRUSTED.md`).
- Templates cannot contain inline `<script>` or `<style>` text, and URL attributes accept only
  relative, `http`, `https`, `mailto` and `tel` URLs.
- The CI workflow has not run yet: it triggers on pull requests and on `main`.
