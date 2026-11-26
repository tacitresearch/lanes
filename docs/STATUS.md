# Status

Where the implementation stands against `DESIGN.md`. Update this file in the same change that
moves an item.

Last updated: 2026-11-27.

## Working

| Area | What exists | Where |
| --- | --- | --- |
| Actor API | `Actor`, `Signature`, `Effect`, `System`, `EnvModel`; `actor_invariant` tactic; `System.join` (two systems wired into one) and `System.mapIO` | `Lanes/Actors/{Actor,System,Join}.lean` |
| Semantics | One executable step function; per-event lemmas; per-actor invariants lift to systems; ghost histories with an erasure theorem; a five-case proof rule for invariants that hold under every fault; projection of a join: a reachable state of `a.join b w` seen from `a` is a reachable state of `a` alone with a network link from outside (`System.Reachable.left`), so invariants of `a` hold of it inside any join (`System.Invariant.join_left`); the same for `b` up to the order of messages on different links, and exactly when the boot of `a` sends `b` nothing | `Lanes/Actors/{World,Step,Lift,Ghost,Monotone,JoinSound}.lean` |
| Deterministic scheduler | Seeded runs, replayable event lists, drivers for the outside world; `Check.fuzz` runs many seeded runs with the environment's faults against `always` and `sometimes` properties and reports the seed and trace of a failure. `FairScheduler` takes the event the system has owed longest, counting a timer that is armed again as owed from then; its run is a fair run of the proof layer | `Lanes/Actors/{Scheduler,FairScheduler}.lean`, `Lanes/Check/Fuzz.lean` |
| Model checker | Breadth-first, exact states, `always`/`sometimes`, constraints, deadlock, coverage, shortest traces; refinement to a `Service` without a mapping. Proved: it lists exactly the enabled events of a state, merging states is safe, a complete PASS means every `always` property holds in every world of the instance (`Check.system_sound_of_respects`; `==` must be equality on actor states, and on the driver's state an equivalence with a matching hash that the driver respects, `Driver.Respects`; `Check.system_sound` is the case where it is equality), the spec monitor accepts exactly what the spec allows, a monitor never holds a candidate twice (in its type), so monitors compare and hash as sets and a monitored driver respects `==` (`Service.monitored_respects`), a complete PASS of a refinement check means the monitor has a candidate in every world (`Check.refines_sound`) and the inputs and outputs of every run of the instance are a trace of the spec (`Check.refines_traces`; the spec's state must have `==` as equality), and a reported violation is a real run of the semantics (`Check.system_violated`) | `Lanes/Check/`, `Lanes/Semantics/Monitor.lean`, `Lanes/Semantics/MonitorSound.lean` |
| Runtime | A kernel of pure functions (routing, start and stop, timers, batching, idleness) proved to follow the semantics whatever its caller does (`Kernel.exec_reachable`, `Kernel.exec_outputs`), never to lose a pending timer or spin on one (`Kernel.exec_wellFormed`), and to let neither timers nor messages starve the other (`Kernel.WellFormed.step_of_queued`, `step_of_due`), inside a 271-line shell: one thread per shard, bounded inbox. A message costs the same at 1,000 and 100,000 actors Durable with a journal: the shard replays what its kernel was asked and returns in the same state, proved for whole and torn journals and tested with SIGKILL; a journal that is damaged, another system's, or written with another codec is refused and left as it is (`Journal.open?`), and one process at a time holds a journal Several shards: `System.shard` is a system as one shard sees it, on the unchanged kernel, and `Cluster` routes between them | `Lanes/Actors/{Shard,Cluster,Kernel,KernelSound,KernelTimers,Journal,Runtime}.lean`, `Lanes/Env/Journal.lean` |
| Proof layer | `Spec`, `Refines` (weak simulation with a label map), `of_map`, `trans`, trace inclusion; system semantics as a CSLib `LTS`; `Service.spec`; sum lemmas. Liveness: infinite runs with stuttering (`System.Run`), weak fairness for each `Obligation` of the system on its own (deliveries, timers, starting an actor that has mail, outputs; never the environment's events), where a timer is obliged to fire only if it stays pending and no step arms it again, as in the runtime (`Obligation.Restarted`; a watchdog that is pinged forever never barks in a fair run, `Examples/WatchdogProofs.lean`), `System.LeadsTo` with its proof rule (`LeadsTo.ensures_of_invariant`), transitivity and monotonicity. Fair runs exist: every finite run extends to a fair run, for every system and environment model (`System.exists_fair_run_of_run`), so every reachable state is on one | `Lanes/Semantics/` |
| Behaviours | `Server` (request and reply), with `Server.implements` proved | `Lanes/Behaviours/Server.lean`, `Lanes/Semantics/Service.lean` |
| Web | HTTP/1.1 adapter whose logic is the gate actor. Proved for every system, bridge and configuration: an arrival is answered at most once in any environment whose link from outside to the gate does not duplicate (`Http.answered_le_arrived`, with crashes, loss, reordering and duplication elsewhere allowed), a waiting request keeps its deadline armed (`Http.deadlines_armed`) and no step arms it again (`Http.deadline_not_restarted`), and in every fair run in which the gate does not crash a request the gate has admitted is answered, by the system or with `504` (`Http.pending_leaves`, `Http.pending_answered`). That an arrival reaches the gate, and so that it is answered exactly once, is model-checked on two requests, not proved; requests and responses as data; `Html` with escaping proved safe, URL attributes checked at render (tested, not proved); scoped template macro with components, fragments and attribute splices; typed routes (`Route.match?_link`, `percentDecode_percentEncode` proved); htmx attributes as typed values taken from routes | `Lanes/Http/`, `Lanes/Env/Http.lean`, `Lanes/Html/` |
| Adapters | `Outside`: what something outside may do, explored by the checker and tested against recorded runs of the real thing (`Outside.allows`). The HTTP server passes against the gate's assumption; a clock adapter (wall time that never goes back, also across a restart) and an HTTP client adapter (HTTP/1.1, no TLS), each with model, handler and conformance test | `Lanes/Actors/Outside.lean`, `Lanes/Env/{Clock,HttpClient}.lean`, `Lanes/Http/Wire.lean` |
| Data | `Enum`, JSON (parser, printers, `ToJson`/`FromJson`), majority quorums, `Codec` (records with a round-trip law, kept by pairs, sums, lists and maps; `Codec.struct%` and `Codec.sum%` write one for a structure or an inductive type in a line), `Frame` (length and checksum framing with the torn-write theorem) (`Quorum.majority_inter`), all total and `Std`-only | `Lanes/Data/` |
| Tooling | `lanes new`, `lanes lint` (text-level, and the size of trusted files), `lanes check`; CI on every push to the pull request (build with warnings as errors, lint, tests, model checks, a generated app); axiom gate | `LanesCli/`, `.github/workflows/ci.yml`, `Tests/Axioms.lean` |

## Reference apps

| App | Checked | Proved |
| --- | --- | --- |
| Bank (`Examples/Bank.lean`) | Conservation on 2 accounts; lost-credit bug found under lossy links; runs on the runtime and over HTTP | Balance never negative (all environments); money conserved for any number of accounts in a faultless environment |
| Key-value store (`Examples/KV.lean`) | Refines the map spec; stale-read bug of a read cache found | Not yet |
| Leader election (`Examples/Election.lean`) | At most one leader per term on 3 nodes with reordering and a crash (165k states); split-brain bug found | At most one leader per term for any number of nodes and terms under every environment model: loss, duplication, reordering, crashes (`Examples/ElectionProofs.lean`) |
| Watchdog (`Examples/Watchdog.lean`) | Under the fair scheduler a dog whose keeper keeps pinging never barks, and one whose keeper rests barks | There is a fair run in which the keeper pings forever, the dog's timer is pending at every position and the dog never barks; in every run that fires each timer that stays pending, it barks (`Examples/WatchdogProofs.lean`) |

## Against the DESIGN exit criteria

- **Phase 1** (runtime and actor API): met, except that the gateway app does not exist. The runtime's logic is proved, which Phase 1 did
  not ask for.
- **Phase 2** (semantics, specs, refinement): semantics, lifting theorem and refinement theory
  are in. Trace checking runs in the test suite. Not done: the scheduler simulation proof, the
  Raft KV store.
- **Phase 3** (model checking and system proofs): checker finds the seeded split-brain bug;
  money conservation is proved for all instances. At most one leader per term is proved. Not done:
  counterexample-to-induction finder, `lanes prove`, symmetry reduction, parallel search.
- **Phase 4** (liveness): fair runs, leads-to and its proof rule are in, with one theorem, the
  gate's, and fair runs are proved to exist. Not done: ranking functions, the lasso search,
  "eventually a leader".
- **Phases 5 to 8**: only the HTTP server adapter, the HTML layer and JSON exist.

## Next, in order

1. Make the monotone proof rule cheaper to use, from what the election proof showed: a variant
   that takes per-state, per-message and per-timer predicates and discharges `below` itself, a
   frame lemma for the actors that did not move, and projections for ghost state.
2. Counterexample-to-induction finder and `inv_split`, then `lanes prove`.
3. Refinement proof for the key-value store with front ends (the first multi-actor refinement).
4. Snapshots, so a journal can be cut and idle actors released.
5. Raft: protocol model, invariants, refinement to `ReplicatedLog`, reference implementation.
6. Checker v2: fingerprints, parallel search, compact state representation.

## Known limits

- The checker runs about 17k states per second (measured on the election model, 4 cores,
  single-threaded). Fine for small instances; v2 is needed for Raft-sized ones.
- `lanes lint` is text-level. `no-io-in-step`, `bounded`, `field-leak` and `fn-length` need the
  elaborator and are not implemented.
- Templates take text children as string literals (`<p>"text"</p>`), not bare text.
- No TLS, WebSockets or database adapter. The HTTP client speaks plain HTTP/1.1 to IPv4
  addresses; call past the local network through a proxy.
- The gate keeps waiting requests in a list, so each request costs time linear in `maxPending`.
- A journal survives the death of the process, not loss of power: Lean's `IO` has no `fsync`.
- No snapshots: a journal grows without bound and a restart replays all of it.
- A timer does not advance while the process is down, and after a restart it also loses the
  time that had passed since the last journal entry before the process died.
- While a timer is pending a shard waits for input with a select, not a plain receive, and an
  input costs about 220 µs, not 100. Behind the gate a deadline is almost always pending.
- A step that emits very many outputs is quadratic in their number (`Kernel.performAll`
  appends one at a time): 20,000 outputs from one step take most of a second.
- `System.join` leaves the inputs it wires open to the outside until `mapIO` hides them, and
  the gate in front of a system is not yet built with `join`.
- The runtime never releases an actor: every identity ever addressed keeps its cell in the
  kernel. A session-per-user system grows without bound. Releasing an actor means its state must
  live somewhere else, so this waits for the persistence adapter.
- Several shards run (`Lanes.Cluster`), tested but without the theorem that together they behave
  as the one system, and not yet with a journal.
- Handing one input to a sleeping shard costs a thread wake-up, about 90 µs here. A busy shard
  does not sleep between inputs.
- That a pending timer fires in time is proved as far as the kernel goes: its agenda holds
  exactly the pending timers, it never tells the shell to sleep past one, and it fires one that
  is due on its next step or, when a message is waiting too, the step after
  (`Kernel.exec_wellFormed`, `Kernel.WellFormed.wait_of_due`, `step_of_due`, `wait_for_ms`).
  That the clock advances and the shell's sleep ends is assumed (see `TRUSTED.md`).
- Liveness theorems are about fair runs of the semantics. That the runtime's runs are fair is
  not proved, and "eventually" carries no bound.
- The kernel's message queue has no bound of its own (see `TRUSTED.md`).
- Templates cannot contain inline `<script>` or `<style>` text, and URL attributes accept only
  relative, `http`, `https`, `mailto` and `tel` URLs.
