# Decisions

Decisions taken while implementing `DESIGN.md`: the ones it left open, and the places where the
implementation departs from its sketches. Each entry gives the decision and the reason. Newest
last.

One file per decision, `Dn-<slug>.md`, whose first line is `# Dn. Title`. A new decision is a
new file `new-<slug>.md` whose first line is `# D?. Title`: its author does not choose its
number, so two branches that each add one never touch the same file. Refer to it by its path
until it has a number. `lake exe lanes lint --fix --main`, run on the main branch after a merge,
numbers it, renames it, rewrites the references to its path, and regenerates the index below;
`lanes lint` fails on two decisions with one number and on a stale index, and with `--main` on a
decision without a number.

## Index

- [D1. Message typing: per-actor message types, indexed by identity](D1-message-typing.md)
- [D2. Identities name actors that always exist (virtual actors)](D2-identities-name-actors-that-always-exist.md)
- [D3. `Effect` is `send | emit | after | cancel | stop`; no `io`, no `reply`](D3-effect-is-send-emit-after-cancel.md)
- [D4. The system boundary is explicit: `In`, `Out`, `accept`](D4-the-system-boundary-is-explicit.md)
- [D5. Start is recovery](D5-start-is-recovery.md)
- [D6. One executable definition of the semantics](D6-one-executable-definition-of-the-semantics.md)
- [D7. `Actor` takes its effect type as a parameter](D7-actor-takes-its-effect-type-as.md)
- [D8. The model checker stores full states](D8-the-model-checker-stores-full-states.md)
- [D9. Library files use Lean's module system](D9-library-files-use-lean-s-module.md)
- [D10. Toolchain and pins](D10-toolchain-and-pins.md)
- [D11. Two import roots: `Lanes` and `Lanes.Semantics`](D11-two-import-roots.md)
- [D12. Template tags have no space after `<`](D12-template-tags-have-no-space-after.md)
- [D13. The runtime orders steps with one logical clock](D13-the-runtime-orders-steps-with-one.md)
- [D14. Proofs of system invariants go through per-event lemmas](D14-proofs-of-system-invariants-go-through.md)
- [D15. JSON is a `Std`-only port of `Lean.Data.Json`](D15-json-is-a-std-only-port.md)
- [D16. An actor never waits inside a step](D16-an-actor-never-waits-inside-a.md)
- [D17. URL attributes are rendered through `Html.safeUrl`](D17-url-attributes-are-rendered-through-html.md)
- [D18. The runtime is a proved kernel inside a thin shell](D18-the-runtime-is-a-proved-kernel.md)
- [D19. The HTTP adapter's logic is a gate actor](D19-the-http-adapter-s-logic-is.md)
- [D20. History variables are ghosts with an erasure theorem](D20-history-variables-are-ghosts-with-an.md)
- [D21. A proof rule for invariants no fault can break](D21-a-proof-rule-for-invariants-no.md)
- [D22. Routes are values with a proof; htmx attributes come from them](D22-routes-are-values-with-a-proof.md)
- [D23. Time is data, and a shard is a thread](D23-time-is-data.md)
- [D24. Durability is a journal of what the kernel was asked, replayed](D24-durability-is-a-journal-of-what.md)
- [D25. Composition is a join, and what survives it is projection](D25-composition-is-a-join.md)
- [D26. An adapter is a model of the outside and a handler, tested against each other](D26-an-adapter-is-a-model-of.md)
- [D27. Liveness: infinite runs, weak fairness per obligation, leads-to](D27-liveness.md)
- [D28. A shard is a system, and a cluster is runtimes with a router](D28-a-shard-is-a-system.md)
- [D29. A snapshot is a restart without the crash](D29-a-snapshot-is-a-restart-without.md)
- [D30. Shards in different processes are joined by a link that promises little](D30-shards-in-different-processes-are-joined.md)
- [D31. The gate is a system, joined in front; what a join keeps of a run is its deeds](D31-the-gate-is-a-system.md)
- [D32. The inbox is a batch, and waiting for room is the rare path](D32-the-inbox-is-a-batch.md)
- [D33. The checker: measure, then normalise once per state](D33-the-checker.md)
- [D34. A replicated system refines its service by a relation, not a mapping](D34-a-replicated-system-refines-its-service.md)
- [D35. An append carries a batch, and only news brings the next](D35-an-append-carries-a-batch.md)
- [D36. What a durable system has to say for itself: a map with a codec, a journal begun on purpose, a name that covers the replay](D36-what-a-durable-system-has-to.md)
- [D37. No router between shards in one process](D37-no-router-between-shards-in-one.md)
- [D38. Types are declared inside a command that derives what Lean's handlers cannot](D38-types-are-declared-inside-a-command.md)
- [D39. The HTTP reader is specified by writers, and its limit is on the response](D39-the-http-reader-is-specified-by.md)
- [D40. The runtime shell and the HTTP server only perform](D40-the-runtime-shell-and-the-http.md)
- [D41. A fair run of a join is a fair run of its left side, seen without the messages from outside](D41-a-fair-run-of-a-join.md)
- [D42. A spec names its inputs and outputs, and time passes in it as deadlines the system's timers are](D42-a-spec-names-its-inputs-and.md)
- [D43. One gate: `serve` runs the gate joined in front](D43-one-gate.md)
- [D44. A request is prepared before it is journalled](D44-request-prepared-before-journal.md)
- [D45. Everything is proved; the checker finds bugs, a proof is the evidence](D45-everything-is-proved.md)
- [D46. Bind what touches physics](D46-bind-what-touches-physics.md)
- [D47. The inventory is computed from the built library](D47-the-inventory-is-computed.md)
- [D48. A request named by its client takes effect once, and its answer may be handed over again](D48-a-request-named-by-its-client.md)
- [D49. The server reads requests by a strict profile, and every refusal closes the connection](D49-the-server-reads-requests-by-a-strict-profile.md)
- [D50. A parser is proved against its RFC and tested against Go, and every difference is decided](D50-differential-tests-against-go.md)
- [D51. An actor at rest is released, and the kernel's theorems hold up to the starts that bring it back](D51-release-actors-at-rest.md)
- [D52. A service behind actors is proved with one simulation, and an application gives only its steps](D52-standard-simulation.md)
- [D53. A JSON key given twice keeps its last value](D53-json-repeated-keys.md)
- [D54. Raft acts once on a command its client names, and an answer it no longer keeps is not handed over](D54-raft-acts-once.md)
- [D55. Work outside a step is a job: an actor with an outbox, a deadline per attempt and a bound](D55-jobs.md)
- [D56. A deadline may pass where a message is served](D56-a-deadline-passes-where-it-is-served.md)
- [D57. The server runs its own connections, and a pure function decides for each](D57-the-server-runs-its-own-connections.md)
- [D58. URLs, media types and rate limits against Go, and where they depart from it](D58-urls-media-types-rate-limits-against-go.md)
- [D59. Threads park, and a connection's loop runs where it is told something](D59-threads-park.md)
- [D60. Examples are for reading, fixtures are for the tests](D60-examples-are-for-reading.md)
- [D61. Models of external systems: classes in Lanes, vendors in integrations](D61-models-of-external-systems.md)
- [D62. The layout is by concern, and `import Lanes` is the API](D62-the-layout-is-by-concern.md)
- [D63. The fixtures hold what the tests use, the examples the proofs](D63-fixtures-hold-what-tests-use.md)
- [D64. Actors step in parallel within a wave, and connections run on threads of the server's own](D64-actors-run-in-parallel.md)
- [D65. Models of external services: calls that may not answer, keys, webhooks, and things with a lifecycle](D65-models-of-external-services.md)
- [D66. A migration carries the old kernel across a deploy, once, with a proof](D66-a-migration-carries-the-kernel-across.md)
- [D67. A TLS client, from the OpenSSL Lean's toolchain ships](D67-a-tls-client-from-the-openssl-lean-ships.md)
