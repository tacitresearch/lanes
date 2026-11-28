# Decisions

Why each piece of Lanes is the way it is. Each entry gives the decision and the reason;
`docs/ARCHITECTURE.md` says how the pieces fit as they are now. The early ones refer to
DESIGN.md, the first design, which is no longer in the repository: `docs/ARCHITECTURE.md`
replaced it.

One file per decision, `Dn-<slug>.md`, whose first line is `# Dn. Title`. A new decision is a
new file `new-<slug>.md` whose first line is `# D?. Title`: its author does not choose its
number, so two branches that each add one never touch the same file. Refer to it by its path
until it has a number. Whoever opens the pull request runs `lake exe lanes lint --fix --main`
against the current main branch, which numbers it, renames it, rewrites the references to its
path, and regenerates the index below; `lanes lint` fails on two decisions with one number and on
a stale index, and with `--main` (as CI runs it on the main branch) on a decision without a
number.

The line under a decision's title is its status: `Status: Accepted`, `Status: Superseded by
Dn`, or `Status: Partly superseded by Dn (the part)`. A decision is never rewritten but for that
line, which the decision that supersedes it changes. The index lists the current decisions
first, then those superseded. Each list is sorted by the files' slugs, not by number, so that
two new decisions land at different lines. The numbers give the order in which they were taken.

## Index

### Current

- [D56. A deadline may pass where a message is served](D56-a-deadline-passes-where-it-is-served.md)
- [D41. A fair run of a join is a fair run of its left side, seen without the messages from outside](D41-a-fair-run-of-a-join.md): partly superseded by D86 (the right side of a join)
- [D86. A fair run of a join is a fair run of its right side too, by the join with its sides exchanged](D86-a-fair-run-of-a-join-is-one-of-its-right-side.md)
- [D21. A proof rule for invariants no fault can break](D21-a-proof-rule-for-invariants-no.md)
- [D34. A replicated system refines its service by a relation, not a mapping](D34-a-replicated-system-refines-its-service.md)
- [D48. A request named by its client takes effect once, and its answer may be handed over again](D48-a-request-named-by-its-client.md): partly superseded by D110-volatile-actors.md (a memo that survives a restart: a key that must is a row in the database)
- [D42. A spec names its inputs and outputs, and time passes in it as deadlines the system's timers are](D42-a-spec-names-its-inputs-and.md)
- [D77. A test kit, `Lanes.Testing`, beside `Lanes` and not in it](D77-a-test-kit.md)
- [D67. A TLS client, from the OpenSSL Lean's toolchain ships](D67-a-tls-client-from-the-openssl-lean-ships.md)
- [D7. `Actor` takes its effect type as a parameter](D7-actor-takes-its-effect-type-as.md)
- [D64. Actors step in parallel within a wave, and connections run on threads of the server's own](D64-actors-run-in-parallel.md): partly superseded by D73 (`Runtime.Config.workers` turning parallel steps on, off by default), D110-volatile-actors.md (waves: steps committed in a journal's order) and new-free-running.md (actors stepping in parallel within a wave)
- [D26. An adapter is a model of the outside and a handler, tested against each other](D26-an-adapter-is-a-model-of.md)
- [D74. AWS as an integration: a role's credentials refreshed by a proved policy, and SES as the email model](D74-aws-integration.md): partly superseded by D110-volatile-actors.md (AWS as a Lake package under `integrations/`: it is `Services/Aws`)
- [D46. Bind what touches physics](D46-bind-what-touches-physics.md): partly superseded by D95-one-crypto-library.md (libsodium)
- [D78. Uploads bounded by a signed policy, and large ones in parts](D78-bounded-and-large-uploads.md)
- [D92. The checker at scale: a hash that sees order, a fingerprinted mode, reductions](D92-checker-scale.md)
- [D82. CloudFront signed URLs and cookies, and signatures made with a private key](D82-cloudfront-signed-urls.md)
- [D25. Composition is a join, and what survives it is projection](D25-composition-is-a-join.md)
- [D89. What one side of a join sends the other is handled there, in every fair run](D89-deliveries-across-a-join.md)
- [D50. A parser is proved against its RFC and tested against Go, and every difference is decided](D50-differential-tests-against-go.md)
- [D100. Each doc has one job, and is generated or tested where it can be](D100-each-doc-has-one-job.md): partly superseded by D110-volatile-actors.md (the inventory computed by `lanesInventory`)
- [D3. `Effect` is `send | emit | after | cancel | stop`; no `io`, no `reply`](D3-effect-is-send-emit-after-cancel.md)
- [D45. Everything is proved; the checker finds bugs, a proof is the evidence](D45-everything-is-proved.md): partly superseded by D110-volatile-actors.md (the generated inventory of every public definition)
- [D60. Examples are for reading, fixtures are for the tests](D60-examples-are-for-reading.md): partly superseded by D63 (the examples' proofs copied into the fixtures)
- [D63. The fixtures hold what the tests use, the examples the proofs](D63-fixtures-hold-what-tests-use.md)
- [D106. The gate before the shard](D106-gate-before-shard.md): partly superseded by D110-volatile-actors.md (its reasons of waves and a runtime of objects, and the section on the journal)
- [D93. Each generated line is about one item, and unreleased changes are fragments](D93-generated-lines-are-local.md): partly superseded by D100-each-doc-has-one-job.md (the status fragments) and by D110-volatile-actors.md (the changelog fragments)
- [D20. History variables are ghosts with an erasure theorem](D20-history-variables-are-ghosts-with-an.md)
- [D104. Honest results: a bounded pass exits 2, each failure has a kind, a binding is proved of its reference](D104-honest-results.md)
- [D2. Identities name actors that always exist (virtual actors)](D2-identities-name-actors-that-always-exist.md)
- [D55. Work outside a step is a job: an actor with an outbox, a deadline per attempt and a bound](D55-jobs.md): partly superseded by D110-volatile-actors.md (jobs that survive a restart through the journal: they are rows in the database)
- [D15. JSON is a `Std`-only port of `Lean.Data.Json`](D15-json-is-a-std-only-port.md)
- [D53. A JSON key given twice keeps its last value](D53-json-repeated-keys.md)
- [D99. Layered packages in one repository, one version, prebuilt builds (proposal)](D99-layered-packages.md): partly superseded by D110-volatile-actors.md (the durable layer, the courier, and services as packages of their own: they live in one area of the same package); its section 3, Mathlib and CSLib removed, is done (D112-proof-libraries.md)
- [D9. Library files use Lean's module system](D9-library-files-use-lean-s-module.md)
- [D27. Liveness: infinite runs, weak fairness per obligation, leads-to](D27-liveness.md)
- [D1. Message typing: per-actor message types, indexed by identity](D1-message-typing.md)
- [D65. Models of external services: calls that may not answer, keys, webhooks, and things with a lifecycle](D65-models-of-external-services.md)
- [D61. Models of external systems: classes in Lanes, vendors in integrations](D61-models-of-external-systems.md): partly superseded by D110-volatile-actors.md (vendors as Lake packages under `integrations/`: they live in `Lanes/Services/`)
- [D81. Models of more outside systems: queues, caches, clocks, shared caches, rate limits and disk faults](D81-more-outside-models.md)
- [D69. The server tells its operators how it is, and nothing it tells enters a system](D69-observability.md): partly superseded by D110-volatile-actors.md (the journal's metrics, and readiness after a replay)
- [D95. One crypto library: the OpenSSL Lean ships](D95-one-crypto-library.md)
- [D6. One executable definition of the semantics](D6-one-executable-definition-of-the-semantics.md)
- [D43. One gate: `serve` runs the gate joined in front](D43-one-gate.md)
- [D80. Every parser has an oracle and every model a recorded run, in one place, and lint keeps the list](D80-oracles.md)
- [D83. PostgreSQL over TLS, with channel binding, and a pool of connections](D83-postgres-over-tls.md)
- [D68. PostgreSQL is spoken in Lean, and a transactional store is a model](D68-postgres-protocol-in-lean.md): partly superseded by D111-typed-store.md (the store model: typed tables, keys and scans replace the key-value model for new code)
- [D112. Mathlib and CSLib in the proof layer, measured](D112-proof-libraries.md)
- [D98. A small proof surface, and each property written once](D98-proof-surface.md)
- [D14. Proofs of system invariants go through per-event lemmas](D14-proofs-of-system-invariants-go-through.md)
- [D108. Reads from the state](D108-reads-from-state.md): partly superseded by D110-volatile-actors.md (its reasons: a read no longer skips a journal's sync, and waves are gone) and by new-free-running.md (the actors of a peek read at one boundary)
- [D51. An actor at rest is released, and the kernel's theorems hold up to the starts that bring it back](D51-release-actors-at-rest.md)
- [D44. A request is prepared before it is journalled](D44-request-prepared-before-journal.md): partly superseded by D110-volatile-actors.md (the journal that preparing kept secrets out of)
- [D22. Routes are values with a proof; htmx attributes come from them](D22-routes-are-values-with-a-proof.md)
- [D96. One model with proofs, and runtimes proved against it](D96-runtime-contract.md): partly superseded by D110-volatile-actors.md (the default runtime, and the contract's clauses that rest on a journal: one order, output ids, no acknowledged input lost across a restart)
- [D71. S3 and Signature Version 4, in Lanes as the protocol of a class of object stores](D71-s3-and-signature-version-4.md)
- [D72. Sign-in with OAuth 2.0 and OpenID Connect, done where a request arrives](D72-sign-in-with-oauth.md): partly superseded by D110-volatile-actors.md (each provider a Lake package of its own: Google and GitHub are presets of `Services/Oidc`)
- [D52. A service behind actors is proved with one simulation, and an application gives only its steps](D52-standard-simulation.md)
- [D5. Start is recovery](D5-start-is-recovery.md)
- [D101. The step's final shape: a context, quarantine, restarts and totality](D101-step-shape.md): partly superseded by D110-volatile-actors.md (`now` and `seed` taken from the journal, and quarantine through the journal)
- [D76. Bodies and responses stream through the gate, in pieces and parts, one at a time](D76-streams-through-the-gate.md)
- [D12. Template tags have no space after `<`](D12-template-tags-have-no-space-after.md)
- [D33. The checker: measure, then normalise once per state](D33-the-checker.md)
- [D31. The gate is a system, joined in front; what a join keeps of a run is its deeds](D31-the-gate-is-a-system.md)
- [D19. The HTTP adapter's logic is a gate actor](D19-the-http-adapter-s-logic-is.md): partly superseded by D31 and D43 (the gate is a system joined in front, not `gated`)
- [D39. The HTTP reader is specified by writers, and its limit is on the response](D39-the-http-reader-is-specified-by.md)
- [D84. The kernel takes an actor's state out of its cell before the step](D84-the-kernel-takes-the-state-out-before-the-step.md)
- [D62. The layout is by concern, and `import Lanes` is the API](D62-the-layout-is-by-concern.md)
- [D8. The model checker stores full states](D8-the-model-checker-stores-full-states.md)
- [D18. The runtime is a proved kernel inside a thin shell](D18-the-runtime-is-a-proved-kernel.md): partly superseded by D110-volatile-actors.md (parallelism from several shards: one process's scheduler runs actors in parallel)
- [D40. The runtime shell and the HTTP server only perform](D40-the-runtime-shell-and-the-http.md)
- [D49. The server reads requests by a strict profile, and every refusal closes the connection](D49-the-server-reads-requests-by-a-strict-profile.md)
- [D57. The server runs its own connections, and a pure function decides for each](D57-the-server-runs-its-own-connections.md)
- [D4. The system boundary is explicit: `In`, `Out`, `accept`](D4-the-system-boundary-is-explicit.md)
- [D59. Threads park, and a connection's loop runs where it is told something](D59-threads-park.md)
- [D23. Time is data, and a shard is a thread](D23-time-is-data.md): partly superseded by D110-volatile-actors.md (a shard on one thread: the scheduler becomes free-running)
- [D10. Toolchain and pins](D10-toolchain-and-pins.md): partly superseded by D99-layered-packages.md, D110-volatile-actors.md and D112-proof-libraries.md (CSLib and Mathlib, which Lanes no longer requires, and a toolchain that follows CSLib's)
- [D111. The typed store: pure transactions over typed tables, at SERIALIZABLE](D111-typed-store.md)
- [D38. Types are declared inside a command that derives what Lean's handlers cannot](D38-types-are-declared-inside-a-command.md): partly superseded by D110-volatile-actors.md (the binary codec `Codable`: `lanes_data` derives JSON and database rows)
- [D17. URL attributes are rendered through `Html.safeUrl`](D17-url-attributes-are-rendered-through-html.md)
- [D58. URLs, media types and rate limits against Go, and where they depart from it](D58-urls-media-types-rate-limits-against-go.md)
- [D109. The video site split into an actor per member, and a scheduler per entity](D109-videos-per-member.md): partly superseded by D110-volatile-actors.md (the video site, which leaves the main branch, and the waves it was split for)
- [D110. Actors are volatile, and durable state lives in outside services with models](D110-volatile-actors.md)
- [D107. The waves' premise, measured on the video site: the work spreads once reads leave the journal](D107-waves-premise.md): partly superseded by D110-volatile-actors.md (waves as the default: it stands as a measurement)

### Superseded

- [D66. A migration carries the old kernel across a deploy, once, with a proof](D66-a-migration-carries-the-kernel-across.md): superseded by D110-volatile-actors.md
- [D28. A shard is a system, and a cluster is runtimes with a router](D28-a-shard-is-a-system.md): superseded by D110-volatile-actors.md
- [D29. A snapshot is a restart without the crash](D29-a-snapshot-is-a-restart-without.md): superseded by D110-volatile-actors.md
- [D73. The shard chooses from its own timing whether a batch's steps are worked out in parallel](D73-adaptive-waves.md): superseded by D110-volatile-actors.md
- [D16. An actor never waits inside a step](D16-an-actor-never-waits-inside-a.md): superseded by D18
- [D35. An append carries a batch, and only news brings the next](D35-an-append-carries-a-batch.md): superseded by D110-volatile-actors.md
- [D97. A data format that outlives its version: one schema per file, values read by name](D97-data-format.md): superseded by D110-volatile-actors.md
- [D24. Durability is a journal of what the kernel was asked, replayed](D24-durability-is-a-journal-of-what.md): superseded by D110-volatile-actors.md
- [D94. A served journal is versioned by the application's name; the gate's settings are read from it](D94-journal-version.md): superseded by D110-volatile-actors.md
- [D103. Former names and defaults in `lanes_data`: `(was old)` and `:= value`](D103-lanes-data-aliases.md): superseded by D110-volatile-actors.md
- [D37. No router between shards in one process](D37-no-router-between-shards-in-one.md): superseded by D110-volatile-actors.md
- [D70. An application is deployed as one instance with its journal on a volume of its own, behind a load balancer](D70-one-instance-one-volume.md): superseded by D110-volatile-actors.md
- [D105. Output ids: where they come from, where the journal's id is kept, and a start with no effects](D105-output-ids.md): superseded by D110-volatile-actors.md
- [D102. Peers open every connection with a versioned handshake and a shared key](D102-peer-handshake.md): superseded by D110-volatile-actors.md
- [D54. Raft acts once on a command its client names, and an answer it no longer keeps is not handed over](D54-raft-acts-once.md): superseded by D110-volatile-actors.md
- [D30. Shards in different processes are joined by a link that promises little](D30-shards-in-different-processes-are-joined.md): superseded by D110-volatile-actors.md
- [D32. The inbox is a batch, and waiting for room is the rare path](D32-the-inbox-is-a-batch.md): superseded by D110-volatile-actors.md (one write to the journal for a batch) and by new-free-running.md (the inbox taken at once)
- [D47. The inventory is computed from the built library](D47-the-inventory-is-computed.md): superseded by D110-volatile-actors.md
- [D13. The runtime orders steps with one logical clock](D13-the-runtime-orders-steps-with-one.md): superseded by D18
- [D91. A video is ready only after a transcode worker outside the site says so, signed](D91-the-video-pipeline.md): superseded by D110-volatile-actors.md
- [D11. Two import roots: `Lanes` and `Lanes.Semantics`](D11-two-import-roots.md): superseded by D99-layered-packages.md and D110-volatile-actors.md
- [D87. The video site's calls to the store are jobs of the scheduler, named by what they are for](D87-videos-on-the-scheduler.md): superseded by D110-volatile-actors.md
- [D88. Steps worked out on the pool update their states in place](D88-waves-in-place.md): superseded by D110-volatile-actors.md
- [D36. What a durable system has to say for itself: a map with a codec, a journal begun on purpose, a name that covers the replay](D36-what-a-durable-system-has-to.md): superseded by D110-volatile-actors.md
- [D79. Work that is due later is a job of the scheduler: held by its id, run by its own timer, retried until it ends](D79-work-that-is-due-later-is-a-job-of-the-scheduler.md): superseded by D110-volatile-actors.md
