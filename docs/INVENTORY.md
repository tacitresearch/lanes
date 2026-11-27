# Inventory

Every public definition of `Lanes` and `LanesCli`, with its status and the evidence for it.
Generated from the built modules by `lake exe lanes lint --fix` (`LanesCli/Inventory.lean`);
do not edit. What each status means, and what is not listed, is in
`docs/decisions/D47-the-inventory-is-computed.md`. The definitions of `Lanes/` with status
none are on `docs/inventory-none.md`, which only shrinks.

## Summary

| Area | Definitions | proved | trusted | checked | tested | spec | none |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Lanes/Behaviours` | 136 | 81 | 5 | 24 | 0 | 26 | 0 |
| `Lanes/Check` | 101 | 80 | 0 | 8 | 0 | 11 | 2 |
| `Lanes/Core` | 103 | 45 | 0 | 34 | 1 | 10 | 13 |
| `Lanes/Data` | 68 | 43 | 0 | 4 | 1 | 0 | 20 |
| `Lanes/Durable` | 70 | 58 | 2 | 0 | 0 | 9 | 1 |
| `Lanes/Lib` | 603 | 384 | 32 | 1 | 102 | 75 | 9 |
| `Lanes/Net` | 37 | 6 | 5 | 0 | 0 | 25 | 1 |
| `Lanes/Outside` | 172 | 133 | 4 | 6 | 1 | 28 | 0 |
| `Lanes/Proof` | 40 | 16 | 0 | 0 | 0 | 23 | 1 |
| `Lanes/Runtime` | 180 | 100 | 21 | 0 | 29 | 30 | 0 |
| `Lanes/Semantics` | 63 | 11 | 0 | 0 | 0 | 51 | 1 |
| `Lanes/Testing` | 106 | 0 | 0 | 1 | 105 | 0 | 0 |
| `Lanes/Web` | 691 | 357 | 57 | 46 | 175 | 54 | 2 |
| `LanesCli` | 126 | 0 | 0 | 0 | 55 | 0 | 71 |
| All | 2496 | 1314 | 126 | 124 | 469 | 342 | 121 |

## `Lanes/Behaviours/Jobs/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jobs.Phase.codec` | proved | its type, `Codec` |
| `Jobs.instCodablePhase` | proved | its type, `Codable` |
| `Jobs.Active.codec` | proved | its type, `Codec` |
| `Jobs.instCodableActive` | proved | its type, `Codable` |
| `Jobs.Outcome.codec` | proved | its type, `Codec` |
| `Jobs.instCodableOutcome` | proved | its type, `Codable` |
| `Jobs.Input.codec` | proved | its type, `Codec` |
| `Jobs.instCodableInput` | proved | its type, `Codable` |
| `Jobs.Output.codec` | proved | its type, `Codec` |
| `Jobs.instCodableOutput` | proved | its type, `Codable` |
| `Jobs.Msg.codec` | proved | its type, `Codec` |
| `Jobs.instCodableMsg` | proved | its type, `Codable` |
| `Jobs.Config.slots` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.Config.cap` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.Config.backoff` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.keys` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.attach_active_leaves` |
| `Jobs.entry` | proved | `Jobs.answer_of_leaves`, `Jobs.entry_step`, `Jobs.not_arms` and 1 more |
| `Jobs.put` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.remove` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.Within` | spec | a predicate |
| `Jobs.Attempts` | spec | a predicate |
| `Jobs.sig` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.actor_attempts` and 11 more |
| `Jobs.timer` | proved | `Jobs.not_arms` |
| `Jobs.fail` | proved | through `Jobs.actor`, `Jobs.attach` and 2 more: `Jobs.active_answered`, `Jobs.active_leaves` and 13 more |
| `Jobs.step` | proved | `Jobs.answer_of_leaves`, `Jobs.dispatch_active`, `Jobs.entry_step` and 2 more |
| `Jobs.rearm` | proved | through `Jobs.actor`, `Jobs.attach` and 1 more: `Jobs.active_answered`, `Jobs.active_leaves` and 8 more |
| `Jobs.actor` | proved | `Jobs.actor_attempts`, `Jobs.actor_within` |
| `Jobs.system` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.answered_le_handled` and 3 more |
| `Jobs.Use.wiring` | proved | through `Jobs.attach`: `Jobs.attach_active_leaves`, `Jobs.attach_within` |
| `Jobs.attach` | proved | `Jobs.attach_active_leaves`, `Jobs.attach_within` |
| `Jobs.pool` | checked | `Tests/Jobs.lean` |

## `Lanes/Behaviours/Jobs/IO/Pool.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jobs.Port.alone` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.handler` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.compute` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.withHeader` | trusted | TRUSTED.md: The jobs pool |
| `Jobs.call` | trusted | TRUSTED.md: The jobs pool |

## `Lanes/Behaviours/Jobs/Sound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jobs.left` | spec | used only in statements |
| `Jobs.Moved` | spec | a predicate |
| `Jobs.Armed` | spec | a predicate |
| `Jobs.answered` | spec | used only in statements |
| `Jobs.handled` | spec | used only in statements |

## `Lanes/Behaviours/Once/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Once.Memo.find?` | proved | through `Once.server`: `Once.server_implements` |
| `Once.Memo.record` | proved | through `Once.server`: `Once.server_implements` |
| `Once.Memo.seen` | proved | through `Once.server`: `Once.server_implements` |
| `Once.actor` | proved | through `Once.server`: `Once.server_implements` |
| `Once.server` | proved | `Once.server_implements` |

## `Lanes/Behaviours/Once/Check.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.insertNew` | checked | `Tests/KV.lean` |
| `Check.sameSet` | checked | `Tests/KV.lean` |
| `Check.setHash` | checked | `Tests/KV.lean` |
| `Check.OnceState.equiv` | checked | `Tests/KV.lean` |
| `Check.OnceState.take` | checked | `Tests/KV.lean` |
| `Check.OnceState.hash` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.insertAll` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.expand` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.close` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.ok` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.instBEq` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.instHashable` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.start` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.input` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.output` | checked | `Tests/KV.lean` |
| `Check.refinesOnce` | checked | `Tests/KV.lean` |
| `Service.onceMonitored` | checked | `Tests/KV.lean` |

## `Lanes/Behaviours/Schedule/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Schedule.Retry.codec` | proved | its type, `Codec` |
| `Schedule.instCodableRetry` | proved | its type, `Codable` |
| `Schedule.Work.codec` | proved | its type, `Codec` |
| `Schedule.instCodableWork` | proved | its type, `Codable` |
| `Schedule.Spec.codec` | proved | its type, `Codec` |
| `Schedule.instCodableSpec` | proved | its type, `Codable` |
| `Schedule.Phase.codec` | proved | its type, `Codec` |
| `Schedule.instCodablePhase` | proved | its type, `Codable` |
| `Schedule.Job.codec` | proved | its type, `Codec` |
| `Schedule.instCodableJob` | proved | its type, `Codable` |
| `Schedule.State.codec` | proved | its type, `Codec` |
| `Schedule.instCodableState` | proved | its type, `Codable` |
| `Schedule.Attempt.codec` | proved | its type, `Codec` |
| `Schedule.instCodableAttempt` | proved | its type, `Codable` |
| `Schedule.Refusal.codec` | proved | its type, `Codec` |
| `Schedule.instCodableRefusal` | proved | its type, `Codable` |
| `Schedule.Outcome.codec` | proved | its type, `Codec` |
| `Schedule.instCodableOutcome` | proved | its type, `Codable` |
| `Schedule.Outcome.isEnd` | spec | used only in statements |
| `Schedule.Input.codec` | proved | its type, `Codec` |
| `Schedule.instCodableInput` | proved | its type, `Codable` |
| `Schedule.Output.codec` | proved | its type, `Codec` |
| `Schedule.instCodableOutput` | proved | its type, `Codable` |
| `Schedule.Msg.codec` | proved | its type, `Codec` |
| `Schedule.instCodableMsg` | proved | its type, `Codable` |
| `Schedule.hashJitter` | checked | `Tests/Schedule.lean` |
| `Schedule.Config.cap` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.Config.backoff` | proved | `Schedule.retry_waits` |
| `Schedule.Config.wait` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.keys` | proved | `Schedule.attach_held_leaves`, `Schedule.every_noticed`, `Schedule.held_leaves` |
| `Schedule.entry` | proved | `Schedule.attach_answer_handled`, `Schedule.attach_end_handled`, `Schedule.attach_held_leaves` and 9 more |
| `Schedule.put` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.remove` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.set` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.sig` | proved | `Schedule.actor_attempts`, `Schedule.actor_within`, `Schedule.armed` and 15 more |
| `Schedule.timer` | proved | through `Schedule.actor`, `Schedule.attach` and 1 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 11 more |
| `Schedule.fail` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.over` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.run` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.answerOf` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.onJob` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.touch` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.enroll` | proved | through `Schedule.actor`, `Schedule.attach` and 2 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 18 more |
| `Schedule.step` | proved | `Schedule.attempt_ends`, `Schedule.dispatch_due`, `Schedule.leaves_answered` and 4 more |
| `Schedule.rearm` | proved | through `Schedule.actor`, `Schedule.attach` and 1 more: `Schedule.actor_attempts`, `Schedule.actor_within` and 11 more |
| `Schedule.actor` | proved | `Schedule.actor_attempts`, `Schedule.actor_within` |
| `Schedule.system` | proved | `Schedule.armed`, `Schedule.attempts`, `Schedule.calls_le_scheduled` and 4 more |
| `Schedule.Use.wiring` | spec | used only in statements |
| `Schedule.attach` | spec | used only in statements |
| `Schedule.sameBag` | checked | `Tests/Schedule.lean` |
| `Schedule.bagHash` | checked | `Tests/Schedule.lean` |
| `Schedule.instBEqCallee` | checked | `Tests/Schedule.lean` |
| `Schedule.instHashableCallee` | checked | `Tests/Schedule.lean` |
| `Schedule.callee` | checked | `Tests/Schedule.lean` |

## `Lanes/Behaviours/Schedule/Sound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Schedule.Msg.target` | spec | used only in statements |
| `Schedule.Act.msg` | spec | used only in statements |
| `Schedule.Work.periodic` | spec | used only in statements |
| `Schedule.tells` | spec | used only in statements |
| `Schedule.isCall` | spec | used only in statements |
| `Schedule.left` | spec | used only in statements |
| `Schedule.Moved` | spec | a predicate |
| `Schedule.Same` | spec | a predicate |
| `Schedule.OwnTimers` | spec | a predicate |
| `Schedule.Job.Within` | spec | a predicate |
| `Schedule.Spec.job` | spec | used only in statements |
| `Schedule.State.Within` | spec | a predicate |
| `Schedule.State.Attempts` | spec | a predicate |
| `Schedule.Armed` | spec | a predicate |
| `Schedule.calls` | spec | used only in statements |
| `Schedule.schedulings` | spec | used only in statements |

## `Lanes/Behaviours/Server.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Server.sig` | proved | `Once.server_implements`, `Server.implements` |
| `Server.actor` | proved | through `Server.system`: `Server.implements` |
| `Server.system` | proved | `Server.implements` |

## `Lanes/Check/Clients.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Driver.after` | checked | `Tests/Clients.lean` |

## `Lanes/Check/EquivDecide.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Matches` | spec | a predicate |

## `Lanes/Check/Fingerprint.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Fingerprint.Search.add` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and 1 more: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.start` | proved | `Check.fingerprint_tasks` |
| `Check.Fingerprint.Search.successors` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and 1 more: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.visit` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and 1 more: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.expandWith` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and 1 more: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.expand` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and 1 more: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.advance` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and 1 more: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.run` | proved | `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_tasks` |
| `Check.Fingerprint.Search.batchSize` | proved | through `Check.Fingerprint.Search.runParallel`, `Check.fingerprint`: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.expandInTasks` | proved | through `Check.Fingerprint.Search.runParallel`, `Check.fingerprint`: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and 4 more |
| `Check.Fingerprint.Search.runParallel` | proved | `Check.Fingerprint.Search.runParallel_eq` |
| `Check.Fingerprint.Search.choicesTo` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and 3 more |
| `Check.Fingerprint.replaySteps` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and 3 more |
| `Check.Fingerprint.replay` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and 3 more |
| `Check.Fingerprint.recheck` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and 3 more |
| `Check.Fingerprint.Found.record` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and 3 more |
| `Check.Fingerprint.Search.report` | proved | `Check.fingerprint_tasks` |
| `Check.fingerprint` | proved | `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted`, `Check.fingerprint_tasks` and 2 more |

## `Lanes/Check/Fuzz.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.FuzzReport.ok` | checked | `Tests/Election.lean` |
| `Check.fuzz` | checked | `Tests/Election.lean` |
| `Check.FuzzReport.render` | none |  |

## `Lanes/Check/Monitor.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.State.equiv` | proved | `Check.Monitor.withinFrom_eq`, `Service.State.equiv_iff`, `Service.State.equiv_of_ret` |
| `Service.State.hash` | proved | through `Check.Monitor.instHashable`: `Check.refines_sound`, `Check.refines_traces` |
| `Service.State.Distinct` | spec | a predicate |
| `Check.Monitor.insertAll` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.expand` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.freshFrom` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.closeStep` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.rounds` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.close` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.ok` | proved | `Check.Monitor.ok_iff`, `Check.refines_sound` |
| `Check.Monitor.withinFrom` | proved | `Check.Monitor.withinFrom_eq` |
| `Check.Monitor.instBEq` | proved | `Check.Monitor.beq_iff_abs_eq`, `Check.refines_sound`, `Check.refines_traces` and 1 more |
| `Check.Monitor.instHashable` | proved | `Check.refines_sound`, `Check.refines_traces` |
| `Check.Monitor.start` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.input` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.output` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Check.Monitor.fire` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 4 more |
| `Service.monitored` | proved | `Check.refines_sound`, `Check.refines_traces`, `Service.monitored_respects` |
| `Check.refines` | proved | `Check.refines_sound`, `Check.refines_traces` |

## `Lanes/Check/MonitorEquiv.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Monitor.Within` | spec | a predicate |

## `Lanes/Check/Reduce.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Model.reduce` | proved | `Check.Model.Reduction.of_reduced`, `Check.Model.Reduction.reachable`, `Check.search_reduce_deadlock` and 5 more |
| `Check.systemReduced` | proved | `Check.systemReduced_sound` |

## `Lanes/Check/ReduceSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.World.SameUpTo` | spec | a predicate |

## `Lanes/Check/Search.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Property.name` | proved | `Check.search_unreached` |
| `Check.Property.holds` | proved | `Check.World.Reduction.ofDriver`, `Check.refines_sound`, `Check.refines_traces` and 3 more |
| `Check.Trace.last` | proved | `Check.fingerprint_deadlock`, `Check.fingerprint_violated`, `Check.fingerprint_witness` and 9 more |
| `Check.Trace.labels` | proved | `Check.systemFingerprinted_violated`, `Check.system_violated` |
| `Check.Report.ok` | checked | `Tests/Bank.lean`, `Tests/Batch.lean`, `Tests/Cache.lean` and 31 more |
| `Check.Path.last` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Path.toTraceAux` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Path.toTrace` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.violation` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.witnessFor` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.witness` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.unwitnessed` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 14 more |
| `Check.Hashed.of` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Hashed.instBEq` | proved | through `Check.Search`, `Check.search`: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Hashed.instHashable` | proved | through `Check.Search`, `Check.search`: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.add` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.contains` | checked | `Tests/Join.lean` |
| `Check.Search.addInit` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 14 more |
| `Check.Search.start` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 14 more |
| `Check.Search.visit` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.successors` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.expandWith` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.expand` | proved | through `Check.Search.run`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.run` | proved | `Check.Search.explore_eq`, `Check.Search.runBatches_eq` |
| `Check.Search.expandAll` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.mapInTasks` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.taskSize` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.batchSize` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and 1 more: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and 16 more |
| `Check.Search.runBatches` | proved | `Check.Search.runBatches_eq` |
| `Check.Search.explore` | proved | `Check.Search.explore_eq` |
| `Check.Search.report` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and 14 more |
| `Check.search` | proved | `Check.search_deadlock`, `Check.search_deadlock_free`, `Check.search_reached` and 13 more |

## `Lanes/Check/SearchSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Model.Steps` | spec | a predicate |
| `Check.Trace.Valid` | spec | a predicate |
| `Check.Path.Valid` | spec | a predicate |
| `Check.Failure.Found` | spec | a predicate |
| `Check.Search.Stored` | spec | a predicate |
| `Check.Search.Live` | spec | a predicate |

## `Lanes/Check/System.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Node.of` | proved | `Scenario.reachable_iff` |
| `Check.instBEqNodeOfInspect` | proved | `Check.Node.beq_iff` |
| `Check.Node.tagged` | proved | through `Check.Node.trafficHash`, `Check.system` and 1 more: `Check.Node.trafficHash_eq`, `Check.refines_sound` and 5 more |
| `Check.Node.trafficHash` | proved | `Check.Node.trafficHash_eq` |
| `Check.instHashableNodeOfInspect` | proved | through `Check.system`, `Check.systemFingerprinted`: `Check.refines_sound`, `Check.refines_traces` and 4 more |
| `Check.Trace.map` | proved | through `Check.system`, `Check.systemFingerprinted`: `Check.refines_sound`, `Check.refines_traces` and 4 more |
| `Check.Report.map` | proved | through `Check.system`, `Check.systemFingerprinted`: `Check.refines_sound`, `Check.refines_traces` and 4 more |
| `Check.model` | proved | `Scenario.reachable_iff` |
| `Check.system` | proved | `Check.refines_sound`, `Check.refines_traces`, `Check.system_sound` and 2 more |
| `Check.Node.props` | proved | through `Check.systemFingerprinted`: `Check.systemFingerprinted_violated` |
| `Check.Node.options` | proved | through `Check.systemFingerprinted`: `Check.systemFingerprinted_violated` |
| `Check.systemFingerprinted` | proved | `Check.systemFingerprinted_violated` |
| `Check.Trace.render` | checked | `Tests/Election.lean`, `Tests/Tutorial.lean`, `Tests/TutorialWeb.lean` |
| `Check.Report.render` | checked | `Tests/Election.lean`, `Tests/Tutorial.lean`, `Tests/TutorialWeb.lean` |
| `Check.Report.renderSystem` | checked | `Tests/Election.lean`, `Tests/Tutorial.lean`, `Tests/TutorialWeb.lean` |

## `Lanes/Check/SystemSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.isInternal` | none |  |
| `World.quiet` | spec | used only in statements |

## `Lanes/Core/Actor.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Actor.run` | spec | used only in statements |
| `Actor.mapEff` | none |  |
| `Actor.Invariant` | spec | a predicate |

## `Lanes/Core/FairScheduler.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.actor?` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `Effect.timeouts` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `SysState.arms` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `SysState.owed` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `SysState.maybeOwed` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.requeue` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.init` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.take` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.next` | proved | through `System.Run.fairAfter`: `System.Run.fairAfter_fair` |
| `FairScheduler.advance` | tested | `Tests/Fair.lean` |

## `Lanes/Core/Inspect.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instHashableEmpty_lanes` | checked | `Tests/Election.lean`, `Tests/Join.lean` |
| `instHashableEnvelope` | checked | `Tests/Join.lean` |
| `instHashableEffect` | checked | `Tests/KV.lean` |
| `instReprEffect` | checked | `Tests/KV.lean` |
| `shortNames` | checked | `Tests/KV.lean` |
| `brief` | checked | `Tests/KV.lean` |
| `Envelope.render` | checked | `Tests/KV.lean` |
| `Event.render` | checked | `Tests/KV.lean` |
| `Event.kind` | none |  |
| `Event.kinds` | none |  |
| `SysState.candidates` | proved | through `SysState.successors`: `SysState.mem_successors_iff`, `SysState.step_of_mem_successors` |
| `SysState.successors` | proved | `SysState.mem_successors_iff`, `SysState.step_of_mem_successors` |
| `Slot.of` | checked | `Tests/Join.lean` |
| `Slot.find` | checked | `Tests/Join.lean` |
| `Slot.stateAt` | checked | `Tests/Join.lean` |
| `Slot.timersAt` | checked | `Tests/Join.lean` |
| `Slot.same` | none |  |
| `Slot.allSame` | none |  |
| `Slot.hash` | none |  |
| `Slots.of` | checked | `Tests/Join.lean` |
| `Slots.state` | checked | `Tests/Join.lean` |
| `Slots.up` | checked | `Tests/Join.lean` |
| `Slots.timers` | checked | `Tests/Join.lean` |
| `SysState.compactWith` | checked | `Tests/Join.lean` |
| `SysState.compact` | checked | `Tests/Join.lean` |
| `SysState.without` | proved | through `SysState.equiv`, `SysState.netEquiv`: `SysState.equiv_iff`, `netEquiv_iff` |
| `SysState.netEquiv` | proved | `netEquiv_iff` |
| `SysState.equiv` | proved | `SysState.equiv_iff` |
| `SysState.trafficHash` | checked | `Tests/Join.lean` |
| `SysState.hash` | checked | `Tests/Join.lean` |
| `SysState.render` | none |  |

## `Lanes/Core/Join.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instDecidableEqJoinMsg` | proved | its type, `Decidable` |
| `joinSig` | proved | `Jobs.attach_active_leaves`, `Jobs.attach_within`, `Obligation.Due.of_thinRight` and 30 more |
| `Wiring.left` | proved | through `Schedule.attach`, `SysState.over` and 5 more: `Obligation.Due.of_thinRight`, `Schedule.attach_answer_handled` and 33 more |
| `Wiring.right` | proved | through `Schedule.attach`, `System.join` and 2 more: `Obligation.Due.of_thinRight`, `Schedule.attach_answer_handled` and 28 more |
| `System.join` | proved | `Obligation.Due.of_thinRight`, `SysState.deliverable_of_thinRight`, `SysState.exists_block` and 23 more |
| `Signature.withIO` | proved | `SysState.run_filterMapIO`, `System.Invariant.filterMapIO`, `System.LeadsTo.filterMapIO` and 2 more |
| `Effect.filterMapOut` | proved | through `SysState.over`, `System.filterMapIO` and 1 more: `SysState.run_filterMapIO`, `System.Invariant.filterMapIO` and 3 more |
| `System.filterMapIO` | proved | `SysState.run_filterMapIO`, `System.Invariant.filterMapIO`, `System.LeadsTo.filterMapIO` and 2 more |
| `System.mapIO` | checked | `Tests/Join.lean` |
| `instHashableSum_lanes` | checked | `Tests/Fronted.lean`, `Tests/Jobs.lean`, `Tests/Join.lean` |
| `Signature.Inspect.join` | checked | `Tests/Jobs.lean`, `Tests/Join.lean` |
| `System.Inspect.join` | checked | `Tests/Jobs.lean`, `Tests/Join.lean` |
| `Signature.Inspect.withIO` | checked | `Tests/Join.lean` |
| `System.Inspect.filterMapIO` | checked | `Tests/Join.lean` |
| `System.Inspect.mapIO` | checked | `Tests/Join.lean` |

## `Lanes/Core/Run.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Effect.sends` | proved | `Account.Fires.grow`, `Account.Fires.handle`, `Account.Moves.grow` and 1 more |
| `Effect.armed` | none |  |
| `Effect.emits` | proved | `Schedule.leaves_answered`, `Schedule.told_of_leaves` |
| `Effect.retime` | spec | used only in statements |
| `Event.quiet` | spec | used only in statements |
| `SysState.startedWith` | spec | used only in statements |
| `SysState.started` | spec | used only in statements |
| `SysState.nextOnLink` | spec | used only in statements |

## `Lanes/Core/Scheduler.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Driver.silent` | checked | `Tests/Election.lean` |
| `Driver.script` | checked | `Tests/KV.lean` |
| `Driver.anyOrder` | checked | `Tests/Bank.lean`, `Tests/Batch.lean`, `Tests/Clients.lean` and 10 more |
| `World.init` | checked | `Tests/Bank.lean` |
| `World.next` | proved | `World.Equiv.next` |
| `simulate` | checked | `Tests/Bank.lean` |

## `Lanes/Core/Service.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.start` | none |  |
| `Service.State.call` | none |  |
| `Service.apply` | none |  |
| `Service.State.ret` | proved | `Check.Monitor.distinct_filterMap_ret`, `Service.State.equiv_of_ret` |
| `Service.State.fire` | none |  |

## `Lanes/Core/System.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Effect.isStop` | proved | `Schedule.attach_answer_handled`, `Schedule.attach_end_handled`, `SysState.mem_net_of_step` and 5 more |
| `Effect.instDecidableEq` | proved | its type, `Decidable` |
| `Envelope.instDecidableEq` | proved | `Account.Fires.handle`, `Account.Moves.handle`, `Account.implements` and 8 more |
| `Envelope.sameLink` | proved | through `SysState.nextOnLink`: `SysState.nextOnLink_spec` |
| `Link.reliable` | proved | through `EnvModel.link`, `EnvModel.lossy` and 2 more: `Account.implements`, `Account.implements_timed` and 33 more |
| `Link.network` | checked | `Tests/Bank.lean`, `Tests/Election.lean`, `Tests/Join.lean` and 1 more |
| `Link.unordered` | checked | `Tests/Election.lean`, `Tests/Jobs.lean`, `Tests/Outside.lean` and 1 more |
| `EnvModel.reliable` | spec | used only in statements |
| `EnvModel.distributed` | none |  |

## `Lanes/Core/World.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `update` | proved | through `SysState.down`, `SysState.handle` and 5 more: `Account.implements`, `Account.implements_timed` and 54 more |
| `Event.timed` | proved | `Account.implements`, `Account.implements_timed`, `Check.refines_traces` and 16 more |
| `Event.visible` | spec | used only in statements |
| `SysState.blank` | proved | `System.Inductive.of_monotone`, `System.Monotone.and`, `System.Monotone.and_net` |
| `SysState.hasMail` | proved | `SysState.hasMail_of_thinRight` |
| `SysState.perform` | proved | through `SysState.handle`, `SysState.init` and 4 more: `Account.implements`, `Account.implements_timed` and 53 more |
| `SysState.performAll` | proved | through `SysState.handle`, `SysState.init` and 4 more: `Account.implements`, `Account.implements_timed` and 53 more |
| `SysState.down` | proved | `Account.implements`, `Account.implements_timed`, `System.Refines.of_events` and 2 more |
| `SysState.settle` | proved | `SysState.Loses.settle` |
| `SysState.handle` | proved | `Http.fronted_handle_arrive`, `Http.served_handle_arrive` |
| `SysState.startActor` | proved | through `SysState.init`, `SysState.run` and 2 more: `Account.implements`, `Account.implements_timed` and 50 more |
| `SysState.deliverable` | proved | `Account.implements`, `Account.implements_timed`, `SysState.deliverable_of_thinRight` and 4 more |
| `SysState.step` | proved | `Http.Gate.answered_of_leaves`, `Http.Gate.deadline_not_restarted`, `Outside.Beside.keeps` and 13 more |
| `SysState.init` | proved | `Account.implements`, `Account.implements_timed`, `Check.systemFingerprinted_violated` and 29 more |
| `SysState.run` | proved | `Check.systemFingerprinted_violated`, `Check.system_violated`, `Http.Gate.answered_le_handled` and 21 more |
| `System.Invariant` | spec | a predicate |

## `Lanes/Data/Codec.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Codec.bytes` | proved | its type, `Codec` |
| `Codec.unit` | proved | its type, `Codec` |
| `Codec.string` | proved | its type, `Codec` |
| `Codec.nat` | proved | its type, `Codec` |
| `Codec.pair` | proved | its type, `Codec` |
| `Codec.map` | proved | its type, `Codec` |
| `Codec.sigma` | proved | its type, `Codec` |
| `Codec.subtype` | proved | its type, `Codec` |
| `Codec.bool` | proved | its type, `Codec` |
| `Codec.fin` | proved | its type, `Codec` |
| `Codec.int` | proved | its type, `Codec` |
| `Codec.sum` | proved | its type, `Codec` |
| `Codec.option` | proved | its type, `Codec` |
| `Codec.readMany` | tested | `Tests/Codec.lean`, `Tests/Durable.lean`, `Tests/MonitorSpeed.lean` and 4 more |
| `Codec.list` | proved | its type, `Codec` |
| `Codec.extTreeMap` | proved | its type, `Codec` |
| `Codable.instByteArray` | proved | its type, `Codable` |
| `Codable.instUnit` | proved | its type, `Codable` |
| `Codable.instString` | proved | its type, `Codable` |
| `Codable.instNat` | proved | its type, `Codable` |
| `Codable.instBool` | proved | its type, `Codable` |
| `Codable.instInt` | proved | its type, `Codable` |
| `Codable.instFin` | proved | its type, `Codable` |
| `Codable.instOption` | proved | its type, `Codable` |
| `Codable.instList` | proved | its type, `Codable` |
| `Codable.instProd` | proved | its type, `Codable` |
| `Codable.instSum` | proved | its type, `Codable` |
| `Codable.instSubtypeOfDecidablePred` | proved | its type, `Codable` |
| `Codable.instSigma` | proved | its type, `Codable` |
| `Codable.instExtTreeMapOfTransCmpOfLawfulEqCmp` | proved | its type, `Codable` |
| `Codec.of` | proved | its type, `Codec` |
| `Codec.fresh` | none |  |
| `Codec.tuple` | none |  |
| `Codec.product` | none |  |
| `Codec.inject` | none |  |

## `Lanes/Data/Declare.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Migrate.same` | proved | `Migrate.migrate_same` |
| `Enum.ofEquiv` | proved | its type, `Enum` |
| `Declare.params` | none |  |
| `Declare.classBinders` | none |  |
| `Declare.productType` | none |  |
| `Declare.sumType` | none |  |
| `Declare.splitDeriving` | none |  |
| `Declare.leanDeriving` | none |  |
| `Declare.codable` | none |  |
| `Declare.conjunction` | none |  |
| `Declare.fieldwise` | none |  |
| `Declare.comparedByBEq` | none |  |
| `Declare.independent` | none |  |
| `Declare.migrate` | none |  |
| `Declare.enum` | none |  |

## `Lanes/Data/Enum.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Enum.instEmpty` | proved | its type, `Enum` |
| `Enum.instUnit` | proved | its type, `Enum` |
| `Enum.instBool` | proved | its type, `Enum` |
| `Enum.instFin` | proved | its type, `Enum` |
| `Enum.instOption` | proved | its type, `Enum` |
| `Enum.instSum` | proved | its type, `Enum` |
| `Enum.instProd` | proved | its type, `Enum` |
| `Enum.instSubtypeOfDecidablePred` | proved | its type, `Enum` |
| `Enum.funBEq` | checked | `Tests/Clients.lean`, `Tests/KV.lean` |
| `Enum.funHashable` | checked | `Tests/Clients.lean`, `Tests/KV.lean` |
| `Enum.funRepr` | checked | `Tests/Clients.lean`, `Tests/KV.lean` |

## `Lanes/Data/Fifo.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Fifo.toList` | proved | `Kernel.WellFormed.step_of_queued` |
| `Fifo.push` | none |  |
| `Fifo.pop?` | none |  |
| `Fifo.filter` | none |  |
| `Fifo.length` | proved | `Peers.Courier.Reachable.queue_le` |
| `Fifo.isEmpty` | checked | `Tests/Courier.lean`, `Tests/Kernel.lean`, `Tests/Release.lean` |

## `Lanes/Data/Quorum.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Quorum.isMajority` | proved | `Quorum.majority_inter` |

## `Lanes/Durable/Disk.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Disk.apply` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.save`, `Journal.Disk.Torn.mend` and 1 more |
| `Journal.Disk.crash` | proved | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash` and 3 more |
| `Journal.Disk.Found.index` | proved | `Journal.Disk.Torn.read` |
| `Journal.Disk.read` | proved | `Journal.Disk.Torn.mend`, `Journal.Disk.Torn.mend_crash`, `Journal.Disk.Torn.read` and 2 more |
| `Journal.Disk.start` | proved | `Journal.Disk.read_of_start`, `Journal.Disk.start_foreign` |
| `Journal.Disk.mend` | proved | `Journal.Disk.Torn.mend`, `Journal.Disk.Torn.mend_crash` |
| `Journal.Disk.load` | proved | `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Torn.load` and 3 more |
| `Journal.appendWrites` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` |
| `Journal.saveWrites` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` |
| `Journal.memo` | spec | used only in statements |
| `Journal.Disk.Holds` | spec | a predicate |
| `Journal.Disk.Torn` | spec | a predicate |

## `Lanes/Durable/Frame.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Frame.fits` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` and 10 more |
| `Frame.checksum` | proved | `Frame.decode_checksum_ne` |
| `Frame.stamped` | proved | `Frame.decode_checksum_ne` |
| `Frame.one` | proved | through `Frame.encode`: `Frame.decode_checksum_ne`, `Frame.decode_encode` and 4 more |
| `Frame.encode` | proved | `Frame.decode_checksum_ne`, `Frame.decode_encode`, `Frame.decode_take` and 3 more |
| `Frame.decode` | proved | `Frame.decode_checksum_ne`, `Frame.decode_encode`, `Frame.decode_extract_prefix` and 7 more |
| `Frame.whole` | proved | `Frame.decode_take_eq`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and 3 more |
| `Frame.span` | proved | `Journal.open?_cut`, `Parcel.receive_send` |
| `Frame.unfinished` | none |  |

## `Lanes/Durable/IO/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.fsync` | trusted | TRUSTED.md: The journal's files |
| `Journal.Store.open` | trusted | TRUSTED.md: The journal's files |

## `Lanes/Durable/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Entry.codec` | proved | its type, `Codec` |
| `Journal.Entry.bytes` | proved | through `Journal.Entry.fits`, `Journal.encode`: `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash` and 10 more |
| `Journal.Entry.ofBytes` | proved | through `Journal.open?`: `Journal.Disk.open?_of_read`, `Journal.open?_cut` and 1 more |
| `Journal.Entry.fits` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and 9 more |
| `Journal.write` | proved | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.load_cut` and 1 more |
| `Journal.read` | proved | through `Journal.open?`: `Journal.Disk.open?_of_read`, `Journal.open?_cut` and 1 more |
| `Journal.encode` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save_crash` |
| `Journal.header` | proved | `Journal.Disk.load_cut`, `Journal.Disk.start_foreign`, `Journal.Disk.torn_nil` and 7 more |
| `Journal.label` | proved | `Journal.label_zero` |
| `Journal.named?` | proved | `Journal.Disk.start_foreign` |
| `Journal.file` | proved | `Journal.Disk.load_cut`, `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.open?` | proved | `Journal.Disk.open?_of_read`, `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.Entry.op?` | proved | through `Journal.ops`: `Journal.recover_handed`, `Journal.recover_kernel` and 4 more |
| `Journal.Entry.marks` | spec | used only in statements |
| `Journal.ops` | proved | `Journal.recover_handed`, `Journal.recover_kernel`, `Journal.recover_outputs` and 3 more |
| `Journal.replay1` | proved | through `Journal.Begun.toFound`, `Journal.recover` and 4 more: `Journal.Begun.resume_upgraded`, `Journal.Disk.Holds.load_append_crash` and 20 more |
| `Journal.recover` | proved | `Journal.Disk.load_cut`, `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn` and 7 more |
| `Journal.replay` | proved | `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and 5 more |
| `Journal.Entry.savedAt` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and 3 more |
| `Journal.since` | proved | through `Journal.Begun.load`, `Journal.Begun.toFound` and 1 more: `Journal.Begun.resume_upgraded`, `Journal.Upgrade.begin_crash` and 2 more |
| `Journal.resume` | proved | `Journal.Begun.resume_upgraded`, `Journal.resume_eq_recover`, `Journal.resume_eq_replay` |
| `Journal.turn` | proved | through `Journal.turns`: `Journal.turns_kernel` |
| `Journal.turnAll` | proved | `Journal.turnAll_eq_exec`, `Journal.turnAll_spread` |
| `Journal.turns` | spec | used only in statements |

## `Lanes/Durable/Migration.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Migration.cell` | proved | `Migration.cell_kernel` |
| `Migration.envelope` | proved | through `Migration.kernel`: `Journal.Upgrade.begin_crash`, `Journal.Upgrade.inv_load` and 4 more |
| `Migration.image` | proved | through `Migration.kernel`: `Journal.Upgrade.begin_crash`, `Journal.Upgrade.inv_load` and 4 more |
| `Migration.kernel` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.inv_load`, `Migration.cell_kernel` and 3 more |

## `Lanes/Durable/Reading.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Reading.OfJournal` | spec | a predicate |
| `Journal.Reading.OfSnapshot` | spec | a predicate |
| `Journal.Disk.ofReadings` | proved | `Journal.Disk.Torn.load_readings`, `Journal.Disk.ofReadings_eq` |

## `Lanes/Durable/Snapshot.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.Due.codec` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.cell` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.envelope` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.image` | proved | its type, `Codec` |
| `Journal.savedHeader` | proved | `Journal.savedHeader_inj` |
| `Journal.savedRecords` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` and 4 more |
| `Journal.saved` | proved | `Journal.saved?_other`, `Journal.saved?_saved` |
| `Journal.saved?` | proved | `Journal.saved?_other`, `Journal.saved?_saved` |

## `Lanes/Durable/Upgrade.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Upgrade.reads` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn` |
| `Journal.Upgrade.writes` | proved | `Journal.Upgrade.holds` |
| `Journal.Upgrade.upgraded` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn`, `Journal.Upgrade.start_torn` |
| `Journal.Upgrade.start` | proved | `Journal.Upgrade.start_torn` |
| `Journal.Disk.begin` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn` |
| `Journal.Begun.load` | spec | used only in statements |
| `Journal.Begun.toFound` | proved | `Journal.Begun.resume_upgraded` |
| `Journal.Upgrade.past` | spec | used only in statements |

## `Lanes/Lib/Crypto/Certificate.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Certificate.Hash.apply` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |
| `Certificate.element` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |
| `Certificate.signatureAlgorithm` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |
| `Certificate.pkcs1` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |
| `Certificate.ecdsa` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |
| `Certificate.hashOf` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |
| `Certificate.endPoint` | tested | `Tests/Postgres.lean`, `Tests/PostgresTls.lean` |

## `Lanes/Lib/Crypto/Hmac.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hmac.blockOf` | tested | `Tests/Crypto.lean`, `Tests/SigV4.lean` |
| `Hmac.Pads.of` | tested | `Tests/Crypto.lean`, `Tests/SigV4.lean` |
| `Hmac.reference` | tested | `Tests/Crypto.lean`, `Tests/SigV4.lean` |
| `Bytes.sameReference` | tested | `Tests/Crypto.lean` |
| `Bytes.hexDigit` | proved | through `Bytes.hex`: `Bytes.unhex?_hex` |
| `Bytes.hex` | proved | `Bytes.unhex?_hex` |
| `Bytes.nibble?` | proved | through `Bytes.unhex?`: `Bytes.unhex?_hex` |
| `Bytes.unhexList` | proved | through `Bytes.unhex?`: `Bytes.unhex?_hex` |
| `Bytes.unhex?` | proved | `Bytes.unhex?_hex` |

## `Lanes/Lib/Crypto/Md5.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Md5.shifts` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.sines` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.initial` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.rotl` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.mix` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.compress` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.wordAt` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.blockAt` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.padding` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.absorb` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.State.bytes` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |
| `Md5.hash` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/Postgres.lean` |

## `Lanes/Lib/Crypto/Pbkdf2.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Pbkdf2.xor` | tested | `Tests/Postgres.lean` |
| `Pbkdf2.be32` | tested | `Tests/Postgres.lean` |
| `Pbkdf2.block` | tested | `Tests/Postgres.lean` |
| `Pbkdf2.block.go` | tested | `Tests/Postgres.lean` |
| `Pbkdf2.derive` | tested | `Tests/Postgres.lean` |

## `Lanes/Lib/Crypto/PublicKey.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Bytes.toNat` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Bytes.ofNat` | proved | `Bytes.size_ofNat` |
| `Der.digits` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.length` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.tlv` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.integer` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.sequence` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.bitString` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.rsaAlgorithm` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.p256Algorithm` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `Der.read?` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `PublicKey.rsaSize` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and 1 more |
| `PublicKey.valid` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `PublicKey.spki` | proved | `PublicKey.ofSpki?_spki` |
| `PublicKey.derSignature` | tested | `Tests/Sign.lean`, `Tests/Signature.lean` |
| `PublicKey.ofSpki?` | proved | `PublicKey.ofSpki?_spki` |
| `PublicKey.lines` | tested | `Tests/Sign.lean` |
| `PublicKey.pem` | tested | `Tests/Sign.lean` |
| `Rsa.powMod` | proved | `Rsa.powMod_eq` |
| `Rsa.digestInfo` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and 1 more |
| `Rsa.encode` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and 1 more |
| `Rsa.verifyReference` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and 1 more |

## `Lanes/Lib/Crypto/Sha256.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Sha256.roundConstants` | tested | `Tests/Crypto.lean` |
| `Sha256.initial` | tested | `Tests/Crypto.lean` |
| `Sha256.rotr` | tested | `Tests/Crypto.lean` |
| `Sha256.schedule` | tested | `Tests/Crypto.lean` |
| `Sha256.compress` | tested | `Tests/Crypto.lean` |
| `Sha256.wordAt` | tested | `Tests/Crypto.lean` |
| `Sha256.blockAt` | tested | `Tests/Crypto.lean` |
| `Sha256.padding` | tested | `Tests/Crypto.lean` |
| `Sha256.absorb` | tested | `Tests/Crypto.lean` |
| `Sha256.digestFrom` | tested | `Tests/Crypto.lean` |
| `Sha256.State.bytes` | tested | `Tests/Crypto.lean` |
| `Sha256.reference` | tested | `Tests/Crypto.lean` |

## `Lanes/Lib/Crypto/Sha512.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Sha512.roundConstants` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.initial` | tested | `Tests/Crypto.lean` |
| `Sha512.initial384` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.rotr` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.schedule` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.compress` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.wordAt` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.blockAt` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.padding` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.absorb` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.State.bytes` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |
| `Sha512.hash` | tested | `Tests/Crypto.lean` |
| `Sha512.hash384` | tested | `Tests/Crypto.lean`, `Tests/Postgres.lean` |

## `Lanes/Lib/Crypto/Sign.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `PrivateKeyImpl` | trusted | TRUSTED.md: The signing key |
| `PrivateKey.readPem` | trusted | TRUSTED.md: The signing key |
| `PrivateKey.spki` | trusted | TRUSTED.md: The signing key |
| `instReprSigningKey` | trusted | TRUSTED.md: The signing key |
| `SigningKey.ofPem` | trusted | TRUSTED.md: The signing key |
| `SigningKey.sign` | trusted | TRUSTED.md: The signing key |

## `Lanes/Lib/Crypto/Sodium.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Sha256.hash` | trusted | TRUSTED.md: The C |
| `hmac` | trusted | TRUSTED.md: The C |
| `Bytes.same` | trusted | TRUSTED.md: The C |
| `randomBytes` | trusted | TRUSTED.md: The C |
| `Argon2id.hash` | trusted | TRUSTED.md: The C |

## `Lanes/Lib/Crypto/Verify.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `PublicKey.verifies` | proved | `Jose.verify_ok`, `OAuth.IdToken.verify_accepted` |

## `Lanes/Lib/Encoding/Base64.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Base64.Alphabet.last` | proved | through `Base64.decode`, `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 6 more |
| `Base64.Alphabet.code` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 4 more |
| `Base64.Alphabet.char` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 4 more |
| `Base64.Alphabet.valueOf` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.Alphabet.value?` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.Encoding.std` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Scram.respond_binds` |
| `Base64.Encoding.rawStd` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.url` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.rawUrl` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean`, `Tests/Oracle/Jose.lean` and 1 more |
| `Base64.sextet` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 4 more |
| `Base64.byte` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.pad` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 4 more |
| `Base64.encodeList` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and 4 more |
| `Base64.full` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.tail1` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.tail2` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.decodeList` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and 2 more |
| `Base64.encode` | proved | `Base64.allowed_of_mem_encode`, `Base64.decode_encode`, `Base64.decode_eq_some_iff` and 3 more |
| `Base64.decode` | proved | `Base64.decode_encode`, `Base64.decode_eq_none_of_length`, `Base64.decode_eq_none_of_not_allowed` and 1 more |
| `Base64.Encoding.Allowed` | spec | a predicate |
| `Base64.encodedLength` | spec | used only in statements |

## `Lanes/Lib/Encoding/Digits.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Digits.join` | proved | `Digits.join_split` |
| `Digits.split` | proved | `Digits.join_split` |
| `Digits.digits` | proved | through `Digits.toChars`: `Digits.head_toChars`, `Digits.ofChars?_toChars` |
| `Digits.char` | proved | through `Digits.fixed`, `Digits.toChars`: `Digits.head_toChars`, `Digits.ofChars?_fixed` and 1 more |
| `Digits.valueOf` | proved | through `Digits.ofChars?`: `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.value?` | proved | through `Digits.ofChars?`: `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.lower` | spec | used only in statements |
| `Digits.values?` | proved | through `Digits.ofChars?`: `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.ofChars?` | proved | `Digits.ofChars?_fixed`, `Digits.ofChars?_toChars` |
| `Digits.toChars` | proved | `Digits.head_toChars`, `Digits.ofChars?_toChars` |
| `Digits.fixed` | proved | `Digits.ofChars?_fixed` |

## `Lanes/Lib/Encoding/Json/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `JsonNumber.ofDecimal` | proved | through `JsonNumber.fromInt`, `JsonNumber.fromNat` and 1 more: `Json.getInt?_eq_ok`, `Json.getNat?_eq_ok` and 1 more |
| `JsonNumber.fromInt` | proved | `Json.getInt?_eq_ok` |
| `JsonNumber.fromNat` | proved | `Json.getNat?_eq_ok` |
| `JsonNumber.ofScientific` | proved | `Json.ofScientific_mantissa` |
| `JsonNumber.instCoeNat` | none |  |
| `JsonNumber.instCoeInt` | none |  |
| `JsonNumber.instOfNat` | tested | `Tests/Json.lean`, `Tests/Ops.lean`, `Tests/Oracle/All.lean` and 1 more |
| `JsonNumber.instInhabited` | none |  |
| `JsonNumber.instOfScientific` | tested | `Tests/Json.lean` |
| `JsonNumber.instNeg` | tested | `Tests/Json.lean` |
| `JsonNumber.instHashable` | tested | `Tests/Json.lean` |
| `JsonNumber.toInt?` | proved | through `Json.getInt?`: `Json.getInt?_eq_ok` |
| `JsonNumber.toNat?` | proved | through `Json.getNat?`: `Json.getNat?_eq_ok` |
| `JsonNumber.maxLeadingZeros` | proved | through `JsonNumber.toString`: `Json.number_toString` |
| `JsonNumber.toString` | proved | `Json.number_toString` |
| `JsonNumber.instToString` | none |  |
| `JsonNumber.instRepr` | tested | `Tests/Json.lean` |
| `Json.decEq` | proved | its type, `Decidable` |
| `Json.decEqArray` | proved | its type, `Decidable` |
| `Json.decEqList` | proved | its type, `Decidable` |
| `Json.decEqFields` | proved | its type, `Decidable` |
| `Json.decEqFieldList` | proved | its type, `Decidable` |
| `Json.decEqField` | proved | its type, `Decidable` |
| `Json.instDecidableEq` | proved | its type, `Decidable` |
| `Json.hash` | tested | `Tests/Json.lean` |
| `Json.instHashable` | tested | `Tests/Json.lean` |
| `Json.reprPrec` | tested | `Tests/Json.lean` |
| `Json.instRepr` | tested | `Tests/Json.lean` |
| `Json.instCoeNat` | none |  |
| `Json.instCoeInt` | none |  |
| `Json.instCoeString` | none |  |
| `Json.instCoeBool` | none |  |
| `Json.instOfNat` | tested | `Tests/Json.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` |
| `Json.sortFields` | proved | through `Json.depth`, `Json.mkObj` and 1 more: `Http.Ops.Access.parse_line`, `Json.getObjVal?_mkObj` and 7 more |
| `Json.dedupFields` | proved | through `Json.depth`, `Json.mkObj` and 1 more: `Http.Ops.Access.parse_line`, `Json.getObjVal?_mkObj` and 7 more |
| `Json.duplicateKey?` | tested | `Tests/Json.lean` |
| `Json.mkObj` | proved | `Json.getObjVal?_mkObj` |
| `Json.mkObj?` | tested | `Tests/Json.lean` |
| `Json.isNull` | proved | `Json.isNull_iff` |
| `Json.getObj?` | spec | used only in statements |
| `Json.getArr?` | proved | `Json.getArr?_eq_ok` |
| `Json.getStr?` | proved | `Json.getStr?_eq_ok` |
| `Json.getNum?` | proved | `Json.getNum?_eq_ok` |
| `Json.getNat?` | proved | `Json.getNat?_eq_ok` |
| `Json.getInt?` | proved | `Json.getInt?_eq_ok` |
| `Json.getBool?` | proved | `Json.getBool?_eq_ok` |
| `Json.getObjVal?` | proved | `Jose.Compact.read_alg`, `Jose.readHeader_alg`, `Jose.verify_ok` and 3 more |
| `Json.getArrVal?` | proved | `Json.getArrVal?_eq_ok` |
| `Json.getObjValD` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and 4 more |

## `Lanes/Lib/Encoding/Json/Classes.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instFromJsonJson` | proved | `fromJson?_toJson_json` |
| `instToJsonJson` | proved | `fromJson?_toJson_json` |
| `instFromJsonJsonNumber` | proved | `fromJson?_toJson_jsonNumber` |
| `instToJsonJsonNumber` | proved | `fromJson?_toJson_jsonNumber` |
| `instFromJsonUnit` | proved | `fromJson?_toJson_unit` |
| `instToJsonUnit` | proved | `fromJson?_toJson_unit` |
| `instFromJsonBool` | proved | `fromJson?_toJson_bool` |
| `instToJsonBool` | proved | `fromJson?_toJson_bool` |
| `instFromJsonNat` | proved | `fromJson?_toJson_nat` |
| `instToJsonNat` | proved | `fromJson?_toJson_nat` |
| `instFromJsonInt` | proved | `fromJson?_toJson_int` |
| `instToJsonInt` | proved | `fromJson?_toJson_int` |
| `instFromJsonString` | proved | `fromJson?_toJson_string` |
| `instToJsonString` | proved | `fromJson?_toJson_string` |
| `instFromJsonFin` | proved | `fromJson?_toJson_fin` |
| `instToJsonFin` | proved | `fromJson?_toJson_fin` |
| `instFromJsonArray` | proved | `fromJson?_toJson_array` |
| `instToJsonArray` | proved | `fromJson?_toJson_array` |
| `instFromJsonList` | proved | `fromJson?_toJson_list` |
| `instToJsonList` | proved | `fromJson?_toJson_list` |
| `instFromJsonOption` | proved | `fromJson?_toJson_none`, `fromJson?_toJson_some` |
| `instToJsonOption` | proved | `fromJson?_toJson_none`, `fromJson?_toJson_some` |
| `instFromJsonProd` | proved | `fromJson?_toJson_prod` |
| `instToJsonProd` | proved | `fromJson?_toJson_prod` |
| `Json.getObjValAs?` | tested | `Tests/Json.lean` |
| `Json.opt` | tested | `Tests/Json.lean` |

## `Lanes/Lib/Encoding/Json/Grammar.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Json.Grammar.IsWs` | spec | a predicate |
| `Json.Grammar.Ws` | spec | a predicate |
| `Json.Grammar.IsDigit` | spec | a predicate |
| `Json.Grammar.instDecidableIsWs` | proved | its type, `Decidable` |
| `Json.Grammar.instDecidableIsDigit` | proved | its type, `Decidable` |
| `Json.Grammar.Digits` | spec | a predicate |
| `Json.Grammar.IntPart` | spec | a predicate |
| `Json.Grammar.Unescaped` | spec | a predicate |
| `Json.Grammar.Spaced.Ws` | spec | a predicate |
| `Json.Grammar.Text` | spec | a predicate |
| `Json.normalize` | spec | used only in statements |
| `Json.depth` | spec | used only in statements |
| `JsonNumber.digits` | spec | used only in statements |
| `Json.digits` | spec | used only in statements |

## `Lanes/Lib/Encoding/Json/Parser.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Json.Parser.fail` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.next?` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.accept` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.skipWsFrom` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.skipWs` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.acceptAll` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.hexDigit?` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.hexDigit` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.hex4` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.lowSurrogate` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.escape` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.strFrom` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.str` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.digitsFrom` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.whole` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.fraction` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.exponentDigits` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.exponent` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.unsigned` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.num` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.literal` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.key` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.value` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.Parser.elements` | spec | used only in statements |
| `Json.Parser.fields` | spec | used only in statements |
| `Json.Parser.document` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and 4 more |
| `Json.parse` | proved | `Http.Ops.Access.parse_line`, `Json.parse_complete`, `Json.parse_compress` and 3 more |

## `Lanes/Lib/Encoding/Json/ParserSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Json.Parser.rest` | spec | used only in statements |
| `Json.Parser.NoWs` | spec | a predicate |
| `Json.Parser.NumStop` | spec | a predicate |
| `Json.Parser.ValueStart` | spec | a predicate |
| `Json.Parser.Reads` | spec | a predicate |
| `Json.Parser.ValueSound` | spec | a predicate |
| `Json.Parser.ElementsSound` | spec | a predicate |
| `Json.Parser.FieldsSound` | spec | a predicate |

## `Lanes/Lib/Encoding/Json/Printer.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Json.needsEscape` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and 4 more |
| `Json.escapeChar` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and 4 more |
| `Json.escape` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and 4 more |
| `Json.renderString` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and 4 more |
| `Json.separate` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and 4 more |
| `Json.compressTo` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and 4 more |
| `Json.compress` | proved | `Json.fromUTF8?_compress`, `Json.parse_compress`, `Json.text_compress` |
| `Json.newline` | proved | through `Json.pretty`: `Json.fromUTF8?_pretty`, `Json.parse_pretty` and 1 more |
| `Json.prettyTo` | proved | through `Json.pretty`: `Json.fromUTF8?_pretty`, `Json.parse_pretty` and 1 more |
| `Json.pretty` | proved | `Json.fromUTF8?_pretty`, `Json.parse_pretty`, `Json.text_pretty` |
| `Json.instToString` | none |  |

## `Lanes/Lib/Metrics.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Metrics.Histogram.bump` | proved | through `Metrics.Histogram.observeAll`: `Metrics.Histogram.buckets_pairwise`, `Metrics.Histogram.observeAll_eq` |
| `Metrics.Histogram.observe` | proved | through `Metrics.Histogram.observeAll`: `Metrics.Histogram.buckets_pairwise`, `Metrics.Histogram.observeAll_eq` |
| `Metrics.Histogram.observeAll` | proved | `Metrics.Histogram.buckets_pairwise`, `Metrics.Histogram.observeAll_eq` |
| `Metrics.Histogram.buckets` | spec | used only in statements |
| `Metrics.escapeLabelChar` | proved | through `Metrics.escapeLabel`: `Metrics.newline_not_mem_escapeLabel`, `Metrics.readLabelValue_escapeLabel` |
| `Metrics.escapeLabel` | proved | `Metrics.newline_not_mem_escapeLabel`, `Metrics.readLabelValue_escapeLabel` |
| `Metrics.escapeHelpChar` | proved | through `Metrics.escapeHelp`: `Metrics.newline_not_mem_escapeHelp`, `Metrics.readHelp_escapeHelp` |
| `Metrics.escapeHelp` | proved | `Metrics.newline_not_mem_escapeHelp`, `Metrics.readHelp_escapeHelp` |
| `Metrics.readLabelValue` | spec | used only in statements |
| `Metrics.readHelp` | spec | used only in statements |
| `Metrics.nameChar` | proved | through `Metrics.sanitize`: `Metrics.sanitize_of_valid`, `Metrics.valid_sanitize` |
| `Metrics.validChars` | spec | used only in statements |
| `Metrics.valid` | spec | used only in statements |
| `Metrics.sanitizeChars` | proved | through `Metrics.sanitize`: `Metrics.sanitize_of_valid`, `Metrics.valid_sanitize` |
| `Metrics.sanitize` | proved | `Metrics.sanitize_of_valid`, `Metrics.valid_sanitize` |
| `Metrics.trimZeros` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.decimal` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.decimalInt` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.Series.kind` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.renderLabels` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.sample` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.renderHistogram` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.Family.render` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.render` | tested | `Tests/Ops.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Metrics.lean` |
| `Metrics.contentType` | tested | `Tests/Ops.lean` |

## `Lanes/Lib/Mime/MediaType.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `MediaType.token` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.skipWs` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.value` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.parseParams` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.parseRaw` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.isToken` | proved | through `MediaType.format`, `MediaType.valid`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.names` | proved | through `MediaType.format`, `MediaType.lower`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.valid` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq` |
| `MediaType.lower` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq` |
| `MediaType.parse` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq`, `MediaType.parse_print` |
| `MediaType.quote` | proved | through `MediaType.format`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.valueChars` | proved | through `MediaType.format`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.chars` | proved | through `MediaType.format`: `MediaType.parse_format`, `MediaType.parse_format_eq` and 1 more |
| `MediaType.format` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq`, `MediaType.parse_print` |

## `Lanes/Lib/Mime/MediaTypeSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `MediaType.EndsToken` | spec | a predicate |
| `MediaType.esc` | spec | used only in statements |
| `MediaType.paramChars` | spec | used only in statements |

## `Lanes/Lib/Net/Ip.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Ip.octet?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.parse4` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.print4` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.hexGroup?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.groups?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.expand` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.fields?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.parse6` | proved | through `Ip.Prefix.parse`, `Ip.parse`: `Ip.Prefix.parse_print`, `Ip.parse_print` |
| `Ip.parse` | proved | `Ip.parse_print` |
| `Ip.zeroRun` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 4 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 7 more |
| `Ip.runAt` | proved | `Ip.longestZeroRun_none`, `Ip.longestZeroRun_some` |
| `Ip.longestZeroRun` | proved | `Ip.longestZeroRun_none`, `Ip.longestZeroRun_some` |
| `Ip.withEllipsis` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.hexFields` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.fields` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.mappedPrefix` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.print6` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and 3 more: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 5 more |
| `Ip.print` | proved | `Ip.parse_print` |
| `Ip.Found` | spec | a predicate |
| `Ip.Addr.width` | proved | `Ip.Prefix.contains_iff` |
| `Ip.Addr.toNat` | spec | used only in statements |
| `Ip.mask` | proved | through `Ip.Prefix.contains`, `Ip.Prefix.masked`: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 1 more |
| `Ip.Addr.masked` | proved | through `Ip.Prefix.contains`, `Ip.Prefix.masked`: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and 1 more |
| `Ip.Prefix.masked` | proved | `Ip.Prefix.contains_masked`, `Ip.Prefix.masked_masked` |
| `Ip.Prefix.contains` | proved | `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` |
| `Ip.Prefix.print` | proved | `Ip.Prefix.parse_print` |
| `Ip.decimal?` | proved | through `Ip.Prefix.parse`: `Ip.Prefix.parse_print` |
| `Ip.Prefix.parse` | proved | `Ip.Prefix.parse_print` |
| `Ip.Addr.isLoopback` | proved | `Ip.isLoopback_v4`, `Ip.isLoopback_v6` |

## `Lanes/Lib/Net/Url.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Url.isAlpha` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.isDigit` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.isHex` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.isUnreserved` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.isSubDelim` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.isPchar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.isPathChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.isQueryChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.isUserChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.isNameChar` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.isSchemeChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.encoded` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.lowerChar` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.lower` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.schemeOk` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.Host.chars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.Authority.chars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.pathChars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.chars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.print` | proved | `Url.parse_print`, `Url.parse_print_of_valid` |
| `Url.cut` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.breakSlash` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.schemeEnd` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.parseHost` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.parseAuthority` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.parseRaw` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.Host.valid` | proved | through `Url.normalize`, `Url.parse` and 1 more: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and 2 more |
| `Url.Authority.valid` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.pathFits` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and 1 more |
| `Url.valid` | proved | `Url.parse_print_of_valid` |
| `Url.parse` | proved | `Url.parse_print`, `Url.parse_print_of_valid` |
| `Url.dots` | proved | through `Url.normalize`, `Url.removeDots` and 2 more: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and 6 more |
| `Url.piece` | proved | through `Url.normalize`, `Url.removeDots` and 2 more: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and 6 more |
| `Url.join` | proved | through `Url.normalize`, `Url.removeDots` and 2 more: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and 6 more |
| `Url.removeDotsChars` | proved | through `Url.normalize`, `Url.removeDots` and 2 more: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and 6 more |
| `Url.removeDots` | proved | `Url.dotFree_removeDots`, `Url.removeDots_of_dotFree`, `Url.removeDots_removeDots` and 1 more |
| `Url.directory` | proved | through `Url.resolve`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_resolve` and 2 more |
| `Url.merge` | proved | through `Url.resolve`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_resolve` and 2 more |
| `Url.resolve` | proved | `Url.dotFree_resolve`, `Url.resolve_of_absolute`, `Url.resolve_of_scheme` |
| `Url.resolveExamples` | proved | `Tests.Oracle.Url.resolve_examples` |
| `Url.resolveText` | proved | `Tests.Oracle.Url.resolve_examples` |
| `Url.hexValue` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.upperHex` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.pct` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.lowerName` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.Host.normalize` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.Authority.normalize` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.relativePath` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.normalizePath` | proved | through `Url.normalize`: `Url.normalize_normalize` |
| `Url.normalize` | proved | `Url.normalize_normalize` |
| `Url.queryEscape` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Url.lean` |
| `Url.encodeQuery` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Url.lean` |
| `Url.decodeQuery` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Url.lean` |

## `Lanes/Lib/Net/UrlSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Url.NonDot` | spec | a predicate |
| `Url.DotFree` | spec | a predicate |
| `Url.Good` | spec | a predicate |
| `Url.Stack` | spec | a predicate |
| `Url.AccOk` | spec | a predicate |
| `Url.Inv` | spec | a predicate |
| `Url.segs` | spec | used only in statements |
| `Url.Ends` | spec | a predicate |
| `Url.isUpperHex` | spec | used only in statements |
| `Url.pctOk` | spec | used only in statements |
| `Url.pending` | spec | used only in statements |
| `Url.Delim` | spec | a predicate |

## `Lanes/Lib/Postgres/Bytes.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Inverse` | spec | a predicate |
| `Postgres.byte` | proved | `Postgres.inverse_byte` |
| `Postgres.putU16` | proved | `Postgres.inverse_u16` |
| `Postgres.getU16` | proved | `Postgres.inverse_u16` |
| `Postgres.putU32` | proved | `Postgres.inverse_u32` |
| `Postgres.getU32` | proved | `Postgres.inverse_u32` |
| `Postgres.untilNul` | proved | `Postgres.untilNul_append` |
| `Postgres.Plain` | spec | a predicate |
| `Postgres.instDecidablePlain` | proved | its type, `Decidable` |
| `Postgres.putStr` | proved | `Postgres.inverse_str` |
| `Postgres.getStr` | proved | `Postgres.inverse_str` |
| `Postgres.take` | proved | `Postgres.take_append` |
| `Postgres.putValue` | proved | `Postgres.inverse_value` |
| `Postgres.getValue` | proved | `Postgres.inverse_value` |
| `Postgres.ValueOk` | spec | a predicate |
| `Postgres.many` | proved | `Postgres.many_append` |
| `Postgres.putList16` | proved | `Postgres.inverse_list16` |
| `Postgres.getList16` | proved | `Postgres.inverse_list16` |
| `Postgres.getTerminated` | proved | `Postgres.getTerminated_append` |
| `Postgres.putTerminated` | proved | `Postgres.getTerminated_append` |
| `Postgres.whole` | proved | `Postgres.whole_append` |
| `Postgres.StartsNonzero` | spec | a predicate |

## `Lanes/Lib/Postgres/Conn.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Isolation.sql` | proved | through `Postgres.Conn.Request.encode`, `Postgres.Conn.Request.messages` and 2 more: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 14 more |
| `Postgres.Conn.Request.kind` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.instDecidableNamed` | proved | its type, `Decidable` |
| `Postgres.Conn.instDecidablePredOptionByteArrayValueOk` | proved | its type, `Decidable` |
| `Postgres.Conn.instDecidablePredFrontendOk` | proved | its type, `Decidable` |
| `Postgres.Conn.fits` | proved | through `Postgres.Conn.run`, `Postgres.Conn.start` and 2 more: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 15 more |
| `Postgres.Conn.Request.messages` | proved | `Postgres.Conn.valid_decode` |
| `Postgres.Conn.Request.encode` | proved | `Postgres.Conn.step_query` |
| `Postgres.Conn.valid` | proved | `Postgres.Conn.step_query`, `Postgres.Conn.valid_decode` |
| `Postgres.Conn.room` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.fail` | proved | `Postgres.Conn.onMessage_sasl_authOk`, `Postgres.Conn.step_refusedTls` |
| `Postgres.Conn.outcome` | proved | `Postgres.Conn.outcome_committed` |
| `Postgres.Conn.texts` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and 1 more: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and 18 more |
| `Postgres.Conn.onReply` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and 1 more: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and 18 more |
| `Postgres.Conn.nonceOk` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and 1 more: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and 18 more |
| `Postgres.Conn.Config.scramOnly` | proved | `Postgres.Conn.onMessage_requireScram` |
| `Postgres.Conn.unbound` | proved | through `Postgres.Conn.choose`, `Postgres.Conn.onMessage` and 2 more: `Postgres.Conn.choose_endPoint`, `Postgres.Conn.choose_require` and 20 more |
| `Postgres.Conn.choose` | proved | `Postgres.Conn.choose_endPoint`, `Postgres.Conn.choose_require` |
| `Postgres.Conn.onAuth` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and 1 more: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and 18 more |
| `Postgres.Conn.onSasl` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and 1 more: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and 18 more |
| `Postgres.Conn.onSaslFinal` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and 1 more: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and 18 more |
| `Postgres.Conn.onMessage` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened`, `Postgres.Conn.onMessage_requireScram` and 2 more |
| `Postgres.Conn.drain` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.receive` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.submit` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.startup` | proved | `Postgres.Conn.step_secured` |
| `Postgres.Conn.sslRequest` | proved | `Postgres.Conn.tls_first` |
| `Postgres.Conn.alpn` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.start` | proved | `Postgres.Conn.run_bound`, `Postgres.Conn.start_queue`, `Postgres.Conn.tls_first` |
| `Postgres.Conn.beforeTls` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.alpnOk` | proved | `Postgres.Conn.step_secured` |
| `Postgres.Conn.secure` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and 13 more |
| `Postgres.Conn.Phase.beforeTls` | proved | `Postgres.Conn.run_beforeTls`, `Postgres.Conn.step_beforeTls` |
| `Postgres.Conn.reusable` | tested | `Tests/Postgres.lean` |
| `Postgres.Conn.step` | proved | `Postgres.Conn.step_beforeTls`, `Postgres.Conn.step_buffer`, `Postgres.Conn.step_closed` and 7 more |
| `Postgres.Conn.run` | spec | used only in statements |

## `Lanes/Lib/Postgres/ConnSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Conn.queries` | spec | used only in statements |
| `Postgres.Conn.answers` | spec | used only in statements |
| `Postgres.Conn.ids` | spec | used only in statements |
| `Postgres.Conn.Fifo` | spec | a predicate |
| `Postgres.Conn.Commits` | spec | a predicate |
| `Postgres.Conn.Answered` | spec | a predicate |
| `Postgres.Conn.Action.bytes` | spec | used only in statements |
| `Postgres.Conn.sent` | spec | used only in statements |
| `Postgres.Conn.Bound` | spec | a predicate |

## `Lanes/Lib/Postgres/IO/Client.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Client.Config.encryption` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.flush` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.transmit` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.receive` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.handshake` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.perform` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.tell` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.await` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.within` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.exec` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Session.close` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.connect` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Store.perform` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Store.handler` | trusted | TRUSTED.md: The PostgreSQL client's IO |

## `Lanes/Lib/Postgres/IO/Pool.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Pool.new` | trusted | TRUSTED.md: The PostgreSQL pool's IO |
| `Postgres.Pool.fresh` | trusted | TRUSTED.md: The PostgreSQL pool's IO |
| `Postgres.Pool.answer` | trusted | TRUSTED.md: The PostgreSQL pool's IO |
| `Postgres.Pool.tell` | trusted | TRUSTED.md: The PostgreSQL pool's IO |
| `Postgres.Pool.checkout` | trusted | TRUSTED.md: The PostgreSQL pool's IO |
| `Postgres.Pool.checkin` | trusted | TRUSTED.md: The PostgreSQL pool's IO |
| `Postgres.Pool.withSession` | trusted | TRUSTED.md: The PostgreSQL pool's IO |

## `Lanes/Lib/Postgres/Message.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.TxStatus.byte` | proved | through `Postgres.Backend.body`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.TxStatus.ofByte` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.protocol30` | proved | through `Postgres.Frontend.decode`, `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and 2 more |
| `Postgres.Column.put` | proved | through `Postgres.Backend.body`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Column.get` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody` and 1 more: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and 2 more |
| `Postgres.Column.Ok` | spec | a predicate |
| `Postgres.Field.put` | proved | through `Postgres.Backend.body`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Field.get` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Field.Ok` | spec | a predicate |
| `Postgres.getFields` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.getNames` | proved | through `Postgres.Backend.decodeBody`, `Postgres.Frame.read`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and 2 more |
| `Postgres.Named` | spec | a predicate |
| `Postgres.putParam` | proved | through `Postgres.Frontend.body`, `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and 2 more |
| `Postgres.getParam` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody` and 1 more: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and 2 more |
| `Postgres.Backend.tag` | proved | `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Backend.body` | proved | `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Backend.Ok` | spec | a predicate |
| `Postgres.Backend.decodeAuth` | proved | through `Postgres.Backend.decodeBody`, `Postgres.Frame.read`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and 2 more |
| `Postgres.Backend.decodeBody` | proved | `Postgres.Backend.decodeBody_body` |
| `Postgres.Backend.decode` | proved | `Postgres.Backend.read_encode` |
| `Postgres.Frontend.expect` | spec | used only in statements |
| `Postgres.Frontend.tag` | proved | through `Postgres.Frontend.body`, `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and 2 more |
| `Postgres.Frontend.body` | proved | `Postgres.Frontend.decode_encode` |
| `Postgres.Frontend.Ok` | spec | a predicate |
| `Postgres.Frontend.wire` | proved | through `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and 2 more |
| `Postgres.Frontend.encode` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured`, `Postgres.Conn.valid_decode` and 1 more |
| `Postgres.Frontend.decodeBody` | proved | through `Postgres.Frontend.decode`: `Postgres.Conn.valid_decode`, `Postgres.Frontend.decode_encode` |
| `Postgres.Frontend.decodeStartup` | proved | through `Postgres.Frontend.decode`: `Postgres.Conn.valid_decode`, `Postgres.Frontend.decode_encode` |
| `Postgres.Frontend.decode` | proved | `Postgres.Conn.valid_decode`, `Postgres.Frontend.decode_encode` |
| `Postgres.Backend.wire` | proved | through `Postgres.Backend.encode`: `Postgres.Backend.read_encode` |
| `Postgres.Backend.encode` | proved | `Postgres.Backend.read_encode` |
| `Postgres.Frame.read` | proved | `Postgres.Backend.read_encode`, `Postgres.Frame.read_done`, `Postgres.Frame.read_more` |

## `Lanes/Lib/Postgres/Pool.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Pool.State.size` | proved | `Postgres.Pool.run_size` |
| `Postgres.Pool.refill` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.hand` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.onCheckout` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.onOpened` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.onFailed` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.onCheckin` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.onExpire` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.step` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and 1 more |
| `Postgres.Pool.run` | spec | used only in statements |
| `Postgres.Pool.Out` | spec | a predicate |

## `Lanes/Lib/Postgres/Scram.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.md5Answer` | checked | `Tests/PostgresConn.lean` |
| `Postgres.Scram.mechanism` | proved | through `Postgres.Scram.Binding.data`, `Postgres.Scram.respond`: `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint` and 3 more |
| `Postgres.Scram.mechanismPlus` | proved | `Postgres.Conn.choose_endPoint` |
| `Postgres.Scram.Binding.header` | proved | through `Postgres.Scram.Binding.data`, `Postgres.Scram.respond`: `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint` and 3 more |
| `Postgres.Scram.Binding.mechanism` | proved | through `Postgres.Scram.Binding.data`, `Postgres.Scram.respond`: `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint` and 3 more |
| `Postgres.Scram.Binding.data` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint`, `Postgres.Scram.respond_binds` |
| `Postgres.Scram.saslName` | proved | through `Postgres.Scram.respond`: `Postgres.Scram.respond_binds`, `Postgres.Scram.respond_iterations` and 1 more |
| `Postgres.Scram.firstBare` | proved | through `Postgres.Scram.respond`: `Postgres.Scram.respond_binds`, `Postgres.Scram.respond_iterations` and 1 more |
| `Postgres.Scram.first` | tested | `Tests/Postgres.lean` |
| `Postgres.Scram.field` | proved | through `Postgres.Scram.respond`, `Postgres.Scram.verify`: `Postgres.Conn.onMessage_requireScram`, `Postgres.Conn.onMessage_saslFinal` and 3 more |
| `Postgres.Scram.parseServerFirst` | proved | `Postgres.Scram.respond_iterations`, `Postgres.Scram.respond_nonce` |
| `Postgres.Scram.respond` | proved | `Postgres.Scram.respond_binds`, `Postgres.Scram.respond_iterations`, `Postgres.Scram.respond_nonce` |
| `Postgres.Scram.verify` | proved | `Postgres.Conn.onMessage_requireScram`, `Postgres.Conn.onMessage_saslFinal` |

## `Lanes/Lib/Postgres/Table.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Table.create` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/Postgres.lean`, `Tests/Postgres.lean` and 1 more |
| `Postgres.Table.Isolation.ofStore` | tested | `Tests/Postgres.lean` |
| `Postgres.Table.request` | tested | `Tests/Postgres.lean` |
| `Postgres.scanRows` | tested | `Tests/Postgres.lean` |
| `Postgres.Table.answer` | tested | `Tests/Postgres.lean` |
| `Postgres.Table.over` | tested | `Tests/Postgres.lean` |

## `Lanes/Lib/RateLimit.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `RateLimit.Config.cap` | proved | `RateLimit.allowed_le`, `RateLimit.credit_allowAll_le`, `RateLimit.credit_allow_le` and 1 more |
| `RateLimit.full` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/RateLimit.lean` |
| `RateLimit.refill` | proved | through `RateLimit.allow`, `RateLimit.allowAll` and 1 more: `RateLimit.allow_after_reserve`, `RateLimit.allowed_le` and 3 more |
| `RateLimit.allow` | proved | `RateLimit.allow_after_reserve`, `RateLimit.credit_allow_le` |
| `RateLimit.wait` | proved | through `RateLimit.reserve`: `RateLimit.allow_after_reserve`, `RateLimit.credit_reserve_le` |
| `RateLimit.reserve` | proved | `RateLimit.allow_after_reserve`, `RateLimit.credit_reserve_le` |
| `RateLimit.allowAll` | spec | used only in statements |

## `Lanes/Lib/Time/Civil.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Civil.isLeap` | proved | through `Civil.Date.toDays`, `Civil.DateTime` and 1 more: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 7 more |
| `Civil.daysInMonth` | proved | through `Civil.Date.toDays`, `Civil.DateTime` and 1 more: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 7 more |
| `Civil.Valid` | spec | a predicate |
| `Civil.instDecidableValid` | proved | its type, `Decidable` |
| `Civil.Date.mk?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean`, `Tests/S3Upload.lean` |
| `Civil.marchMonth` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.ofMarchMonth` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.daysBefore` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.marchLength` | spec | used only in statements |
| `Civil.dayOfEra` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.daysFrom` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.Date.toDays` | proved | `Civil.ofDays_toDays`, `Civil.toDays_ofDays` |
| `Civil.yearOfEra` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.civilOf` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.civil` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and 4 more |
| `Civil.LongYear` | spec | a predicate |
| `Civil.Date.ofDays` | proved | `Civil.ofDays_toDays`, `Civil.toDays_ofDays` |
| `Civil.Date.weekday` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Civil.TimeOfDay.seconds` | proved | through `Civil.DateTime.toUnix`: `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` and 2 more |
| `Civil.TimeOfDay.ofSeconds` | proved | through `Civil.DateTime.ofUnix`: `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` and 2 more |
| `Civil.DateTime.toUnix` | proved | `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix`, `S3.Post.admitted_bounded` and 1 more |
| `Civil.DateTime.ofUnix` | proved | `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix`, `S3.Post.admitted_bounded` and 1 more |

## `Lanes/Lib/Time/Format.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `TimeFormat.isDigit` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and 1 more |
| `TimeFormat.num?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and 1 more |
| `TimeFormat.Timestamp.toUnix` | proved | `S3.Post.expiration_parse` |
| `TimeFormat.d2` | proved | through `TimeFormat.printHttpDate?`, `TimeFormat.printRfc3339?`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.d4` | proved | through `TimeFormat.printHttpDate?`, `TimeFormat.printRfc3339?`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.clock` | proved | through `TimeFormat.printHttpDate?`, `TimeFormat.printRfc3339?`: `TimeFormat.parseHttpDate_print`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.trimZeros` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.fractionChars` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.offsetChars` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.rfc3339Chars` | proved | through `TimeFormat.printRfc3339?`: `TimeFormat.parseRfc3339_print` |
| `TimeFormat.InRange` | spec | a predicate |
| `TimeFormat.instDecidableInRange` | proved | its type, `Decidable` |
| `TimeFormat.printRfc3339?` | proved | `TimeFormat.parseRfc3339_print` |
| `TimeFormat.clock?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and 1 more |
| `TimeFormat.fraction?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and 1 more |
| `TimeFormat.offset?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and 1 more |
| `TimeFormat.parseRfc3339` | proved | `S3.Post.expiration_parse`, `TimeFormat.parseRfc3339_print` |
| `TimeFormat.dayNames` | proved | through `TimeFormat.printHttpDate?`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.longDayNames` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.monthNames` | proved | through `TimeFormat.printHttpDate?`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.nameOf?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.imfChars` | proved | through `TimeFormat.printHttpDate?`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.printHttpDate?` | proved | `TimeFormat.parseHttpDate_print` |
| `TimeFormat.checked` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.imf?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.fullYear` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.rfc850?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.asctime?` | proved | through `TimeFormat.parseHttpDate`: `TimeFormat.parseHttpDate_print` |
| `TimeFormat.parseHttpDate` | proved | `TimeFormat.parseHttpDate_print` |

## `Lanes/Net/Courier.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Courier.wire` | proved | `Peers.Courier.Reachable.queue_le`, `Peers.Courier.Reachable.write_not_busy` |
| `Peers.Courier.setWire` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.dial` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.enqueue` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.next` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and 6 more |
| `Peers.Courier.step` | proved | `Peers.Courier.Reachable.write_not_busy` |

## `Lanes/Net/CourierSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Line.conn?` | none |  |
| `Peers.Line.until?` | spec | used only in statements |
| `Peers.Courier.exec` | spec | used only in statements |
| `Peers.Courier.Reachable` | spec | a predicate |
| `Peers.Courier.Status.close` | spec | used only in statements |
| `Peers.Courier.Status.written` | spec | used only in statements |
| `Peers.Courier.Status.next` | spec | used only in statements |
| `Peers.Courier.status` | spec | used only in statements |
| `Peers.Courier.Status.isOpen` | spec | used only in statements |
| `Peers.Courier.Stopped.next` | spec | used only in statements |
| `Peers.Courier.Watch.ready` | spec | used only in statements |
| `Peers.Courier.Watch.told` | spec | used only in statements |
| `Peers.Courier.Watch.next` | spec | used only in statements |
| `Peers.Courier.Watch.Holds` | spec | a predicate |
| `Peers.Courier.sentTo` | spec | used only in statements |
| `Peers.Courier.writtenTo` | spec | used only in statements |
| `Peers.Courier.Order.told` | spec | used only in statements |
| `Peers.Courier.Order.next` | spec | used only in statements |
| `Peers.Courier.Order.Holds` | spec | a predicate |
| `Peers.Courier.readPieces` | spec | used only in statements |
| `Peers.Event.receives` | spec | used only in statements |
| `Peers.Entry.closes` | spec | used only in statements |
| `Peers.Courier.receivedOn` | spec | used only in statements |
| `Peers.Courier.deliveredFrom` | spec | used only in statements |
| `Peers.Action.parcel?` | spec | used only in statements |
| `Peers.Courier.leftover` | spec | used only in statements |

## `Lanes/Net/IO/Node.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.serveShard` | trusted | TRUSTED.md: A process with a front and peers |

## `Lanes/Net/IO/Peers.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.start` | trusted | TRUSTED.md: The transport between processes |
| `Peers.send` | trusted | TRUSTED.md: The transport between processes |
| `Peers.stop` | trusted | TRUSTED.md: The transport between processes |
| `Peers.shard` | trusted | TRUSTED.md: The transport between processes |

## `Lanes/Outside/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Outside.any` | tested | `Tests/Jobs.lean`, `Tests/S3.lean` |
| `Outside.driver` | checked | `Tests/Cache.lean`, `Tests/Clock.lean`, `Tests/HttpClient.lean` and 9 more |
| `Outside.see` | proved | `Outside.Beside.keeps`, `Outside.run_induction` |
| `Outside.after` | proved | `Cache.read_sent`, `Clock.wall_back_le`, `Clock.wall_latest_le` and 21 more |
| `Outside.allows` | checked | `Tests/Outside.lean`, `Tests/Queue.lean`, `Tests/Throttle.lean` and 1 more |
| `Outside.both` | proved | `Outside.after_both` |
| `Outside.mine` | spec | used only in statements |

## `Lanes/Outside/Cache.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cache.Request.key` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.Request.leaves` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.Core.possible` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.Core.receive` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.Core.settle` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.Core.answer` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.readOf` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.sentOf` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.mayRead` | proved | through `Cache.server`: `Cache.fill_unleased`, `Cache.read_sent` |
| `Cache.server` | proved | `Cache.fill_unleased`, `Cache.read_sent` |

## `Lanes/Outside/Clock.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Clock.outside` | proved | `Clock.outside_ge` |
| `Clock.wall` | proved | `Clock.wall_back_le`, `Clock.wall_latest_le` |

## `Lanes/Outside/Effects/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Effects.Phase.codec` | proved | its type, `Codec` |
| `Effects.instCodablePhase` | proved | its type, `Codable` |
| `Effects.instEnumPhase` | proved | its type, `Enum` |
| `Effects.Phase.final` | spec | used only in statements |
| `Effects.Lifecycle.Final` | spec | a predicate |
| `Effects.Lifecycle.reachable` | proved | through `Effects.Lifecycle.reaches`, `Effects.outside`: `Effects.Lifecycle.reaches_terminal`, `Effects.Sound.allow` and 7 more |
| `Effects.Lifecycle.reachable.go` | proved | through `Effects.Lifecycle.reaches`, `Effects.outside`: `Effects.Lifecycle.reaches_terminal`, `Effects.Sound.allow` and 7 more |
| `Effects.Lifecycle.reaches` | proved | `Effects.Lifecycle.reaches_terminal` |
| `Effects.Lifecycle.seen` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.Answer.codec` | proved | its type, `Codec` |
| `Effects.instCodableAnswer` | proved | its type, `Codable` |
| `Effects.Answer.isRefused` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.Report.codec` | proved | its type, `Codec` |
| `Effects.instCodableReport` | proved | its type, `Codable` |
| `Effects.Thing.codec` | proved | its type, `Codec` |
| `Effects.instCodableThing` | proved | its type, `Codable` |
| `Effects.ids` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.answered` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.moved` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.reported` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.server` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.service` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and 6 more |
| `Effects.outside` | proved | `Effects.Sound.allow`, `Effects.Sound.observe`, `Effects.Sound.shows_reply` and 5 more |
| `Effects.Lifecycle.Terminal` | spec | a predicate |
| `Effects.Shows` | spec | a predicate |
| `Effects.Keeps` | spec | a predicate |

## `Lanes/Outside/Effects/Email.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Email.Status.codec` | proved | its type, `Codec` |
| `Email.instCodableStatus` | proved | its type, `Codable` |
| `Email.instEnumStatus` | proved | its type, `Enum` |
| `Email.Status.next` | proved | through `Email.lifecycle`: `Email.final` |
| `Email.Status.phase` | proved | through `Email.lifecycle`: `Email.final` |
| `Email.lifecycle` | proved | `Email.final` |
| `Email.outside` | checked | `Tests/Outside.lean` |

## `Lanes/Outside/Effects/Payments.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Payments.Status.codec` | proved | its type, `Codec` |
| `Payments.instCodableStatus` | proved | its type, `Codable` |
| `Payments.instEnumStatus` | proved | its type, `Enum` |
| `Payments.Status.next` | proved | through `Payments.lifecycle`: `Payments.final`, `Payments.succeeded_terminal` |
| `Payments.Status.phase` | proved | through `Payments.lifecycle`: `Payments.final`, `Payments.succeeded_terminal` |
| `Payments.Status.event` | proved | through `Payments.lifecycle`: `Payments.final`, `Payments.succeeded_terminal` |
| `Payments.lifecycle` | proved | `Payments.final`, `Payments.succeeded_terminal` |
| `Payments.outside` | checked | `Tests/Outside.lean` |

## `Lanes/Outside/Events.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Events.count` | proved | `Queue.received_le` |
| `Events.bump` | proved | through `Events.bounded`: `Events.deliveries_le` |
| `Events.bounded` | proved | `Events.deliveries_le` |
| `Events.deliveries` | spec | used only in statements |

## `Lanes/Outside/IO/Clock.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Clock.latest` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.Wall.start` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.Wall.now` | trusted | TRUSTED.md: The clock adapter's handler |
| `Clock.handler` | trusted | TRUSTED.md: The clock adapter's handler |

## `Lanes/Outside/Idempotent.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Idempotent.Keyed.codec` | proved | its type, `Codec` |
| `Idempotent.instCodableKeyed` | proved | its type, `Codable` |
| `Idempotent.Slot.codec` | proved | its type, `Codec` |
| `Idempotent.instCodableSlot` | proved | its type, `Codable` |
| `Idempotent.Route.codec` | proved | its type, `Codec` |
| `Idempotent.instCodableRoute` | proved | its type, `Codable` |
| `Idempotent.requests` | spec | used only in statements |
| `Idempotent.holder` | proved | through `Idempotent.server`: `Idempotent.answer_repeat`, `Idempotent.at_most_once` and 1 more |
| `Idempotent.server` | proved | `Idempotent.answer_repeat`, `Idempotent.at_most_once`, `Idempotent.keys_nodup` |
| `Idempotent.Holds` | spec | a predicate |

## `Lanes/Outside/Multipart.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Multipart.State.matches` | proved | through `Multipart.server`: `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.State.held` | proved | through `Multipart.server`: `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.ordered` | proved | through `Multipart.server`: `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.State.valid` | proved | through `Multipart.server`: `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.State.readable` | proved | through `Multipart.server`: `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.State.done` | proved | through `Multipart.server`: `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.server` | proved | `Multipart.completed_sent`, `Multipart.read_listed` |
| `Multipart.Parts` | spec | a predicate |
| `Multipart.Listed` | spec | a predicate |
| `Multipart.Sent` | spec | a predicate |
| `Multipart.Sound` | spec | a predicate |
| `Multipart.Grows` | spec | a predicate |

## `Lanes/Outside/ObjectStore.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `ObjectStore.Request.key` | proved | through `ObjectStore.server`: `ObjectStore.held_sent`, `ObjectStore.read_sent` |
| `ObjectStore.Request.leaves` | proved | through `ObjectStore.server`: `ObjectStore.held_sent`, `ObjectStore.read_sent` |
| `ObjectStore.insertNew` | proved | through `ObjectStore.server`: `ObjectStore.held_sent`, `ObjectStore.read_sent` |
| `ObjectStore.State.possible` | proved | through `ObjectStore.server`: `ObjectStore.held_sent`, `ObjectStore.read_sent` |
| `ObjectStore.State.settle` | proved | through `ObjectStore.server`: `ObjectStore.held_sent`, `ObjectStore.read_sent` |
| `ObjectStore.server` | proved | `ObjectStore.held_sent`, `ObjectStore.read_sent` |
| `ObjectStore.Sound` | spec | a predicate |
| `ObjectStore.HeldSent` | spec | a predicate |

## `Lanes/Outside/Queue.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Queue.Message.codec` | proved | its type, `Codec` |
| `Queue.instCodableMessage` | proved | its type, `Codable` |
| `Queue.inOrder` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and 1 more |
| `Queue.ready` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and 1 more |
| `Queue.receive` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and 1 more |
| `Queue.delete` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and 1 more |
| `Queue.send` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and 1 more |
| `Queue.outside` | proved | `Queue.deleted_not_received`, `Queue.fifo_received_le`, `Queue.received_le` |
| `Queue.receives` | spec | used only in statements |
| `Queue.OneCopy` | spec | a predicate |

## `Lanes/Outside/Rpc.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Rpc.Call.codec` | proved | its type, `Codec` |
| `Rpc.instCodableCall` | proved | its type, `Codable` |
| `Rpc.Reply.codec` | proved | its type, `Codec` |
| `Rpc.instCodableReply` | proved | its type, `Codable` |
| `Rpc.outside` | proved | `Cache.read_sent`, `Events.deliveries_le`, `Idempotent.at_most_once` and 11 more |
| `Rpc.Port.reported` | proved | `Effects.Sound.shows_report`, `Transcode.done_given`, `Transcode.reports_agree` |
| `Rpc.called` | spec | used only in statements |
| `Rpc.answered` | spec | used only in statements |

## `Lanes/Outside/Store/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Store.Db.get` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.Db.insertSorted` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.Db.set` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.Db.apply` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.Read.holds` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.Txn.own` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.Txn.view` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.txn?` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.setTxn` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.dropTxn` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.stateAt` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.readsAll` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.clashes` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.places` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.commitPlaces` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.placeAt` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.settle` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.answersNow` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.applyCommit` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.expand` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.dedup` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.send` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.answer` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.World.answerCommit` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.outstanding` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.State.allow` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.State.observe` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.State.run` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and 6 more |
| `Store.outside` | checked | `Tests/Store.lean` |
| `Store.samples` | checked | `Tests/Store.lean` |

## `Lanes/Outside/Store/Sound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Store.nat` | spec | used only in statements |
| `Store.ask` | spec | used only in statements |
| `Store.say` | spec | used only in statements |
| `Store.allows` | spec | used only in statements |
| `Store.lostCommit` | spec | used only in statements |
| `Store.writeSkew` | spec | used only in statements |
| `Store.lostUpdate` | spec | used only in statements |
| `Store.earlier` | spec | used only in statements |

## `Lanes/Outside/Throttle.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Throttle.Answer.codec` | proved | its type, `Codec` |
| `Throttle.instCodableAnswer` | proved | its type, `Codable` |
| `Throttle.Event.codec` | proved | its type, `Codec` |
| `Throttle.instCodableEvent` | proved | its type, `Codable` |
| `Throttle.server` | proved | `Throttle.throttled_inner`, `Throttle.wait_le`, `Throttle.within_not_throttled` |

## `Lanes/Outside/Transcode.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Transcode.Job.codec` | proved | its type, `Codec` |
| `Transcode.instCodableJob` | proved | its type, `Codable` |
| `Transcode.Report.codec` | proved | its type, `Codec` |
| `Transcode.instCodableReport` | proved | its type, `Codable` |
| `Transcode.Report.job` | proved | `Transcode.reports_agree` |
| `Transcode.landOne` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.land` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.receive` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.answer` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.finish` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.event` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.server` | proved | through `Transcode.service`: `Transcode.done_given`, `Transcode.reports_agree` |
| `Transcode.service` | proved | `Transcode.done_given`, `Transcode.reports_agree` |

## `Lanes/Proof/Deed.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.deed` | proved | through `deeds`, `handled`: `Http.Gate.answered_le_handled`, `Jobs.answered_le_handled` and 2 more |
| `deeds` | spec | used only in statements |
| `Deed.handles` | spec | used only in statements |
| `handled` | spec | used only in statements |
| `put` | spec | used only in statements |
| `Effect.Avoids` | spec | a predicate |

## `Lanes/Proof/Equiv.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `onLink` | none |  |
| `System.Near` | spec | a predicate |

## `Lanes/Proof/Ghost.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.withGhost` | spec | used only in statements |
| `SysState.erase` | spec | used only in statements |

## `Lanes/Proof/JoinSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Envelope.left?` | proved | through `Event.leftDeed`, `Event.right?` and 5 more: `Obligation.right?_inr`, `SysState.run_left` and 10 more |
| `Envelope.right?` | proved | through `Event.right?`, `Event.rightDeed` and 3 more: `Obligation.Due.of_thinRight`, `Obligation.right?_inr` and 11 more |
| `EnvModel.left` | proved | `SysState.run_left`, `System.Invariant.join_left`, `System.LeadsTo.join_left` and 3 more |
| `EnvModel.right` | proved | `Obligation.Due.of_thinRight`, `SysState.deliverable_of_thinRight`, `SysState.init_thinRight` and 6 more |
| `SysState.left` | proved | `SysState.run_left`, `System.Invariant.join_left`, `System.LeadsTo.join_left` and 1 more |
| `SysState.right` | proved | `System.Invariant.join_right`, `System.LeadsTo.join_right`, `System.Reachable.right` and 2 more |
| `SysState.thinLeft` | proved | `System.LeadsTo.join_left`, `System.Run.Fair.left` |
| `Event.left?` | proved | through `Event.leftDeed`, `Event.right?` and 3 more: `Obligation.right?_inr`, `SysState.run_left` and 7 more |
| `Event.leftDeed` | proved | `SysState.run_left`, `SysState.step_left_state`, `System.Run.Fair.left` and 1 more |
| `Wiring.shown` | proved | `SysState.run_left`, `System.Run.Fair.left` |
| `SysState.thinRight` | proved | `Obligation.Due.of_thinRight`, `SysState.deliverable_of_thinRight`, `SysState.hasMail_of_thinRight` and 3 more |
| `Event.right?` | proved | `Obligation.right?_inr` |
| `Event.rightDeed` | proved | `System.Run.Fair.right`, `System.Run.Fair.routed_left` |
| `Wiring.shownRight` | proved | `SysState.init_thinRight`, `System.Run.Fair.right` |
| `Wiring.wired` | spec | used only in statements |

## `Lanes/Proof/List/Prefix.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `afterFirst` | spec | used only in statements |
| `beforeFirst` | spec | used only in statements |

## `Lanes/Proof/Lossy.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `EnvModel.lossy` | spec | used only in statements |

## `Lanes/Proof/MapIOSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Envelope.over` | spec | used only in statements |
| `Envelope.under` | spec | used only in statements |
| `EnvModel.under` | spec | used only in statements |
| `SysState.over` | spec | used only in statements |
| `Event.Under` | spec | a predicate |
| `Event.AllUnder` | spec | a predicate |

## `Lanes/Proof/Monotone.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `SysState.grow` | proved | `Account.Fires.grow`, `Account.Fires.handle`, `Account.Moves.grow` and 12 more |
| `SysState.Pending` | spec | a predicate |

## `Lanes/Proof/Outputs.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.Emits` | spec | a predicate |

## `Lanes/Proof/Past.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Ghost.past` | spec | used only in statements |
| `System.withPast` | spec | used only in statements |
| `SysState.seen` | spec | used only in statements |

## `Lanes/Runtime/Batch.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Batch.due` | proved | `Batch.due_iff`, `Batch.flush_save` |
| `Batch.put` | proved | `Batch.flush_save` |
| `Batch.workWith` | proved | through `Batch.flush`, `Batch.run` and 1 more: `Batch.flush_save`, `Batch.run_handed` and 6 more |
| `Batch.work` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_kernel` and 5 more |
| `Batch.workAll` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_kernel` and 5 more |
| `Batch.flush` | proved | `Batch.flush_save` |
| `Batch.scan` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_kernel` and 5 more |
| `Batch.finish` | proved | through `Batch.run`: `Batch.run_handed`, `Batch.run_kernel` and 4 more |
| `Batch.group` | proved | `Batch.group_ins` |
| `Batch.Command.ins` | spec | used only in statements |
| `Batch.run` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.run_peek` and 3 more |
| `Batch.Act.ops` | proved | through `Batch.journal`: `Batch.run_handed`, `Batch.run_kernel` and 1 more |
| `Batch.Act.outputs` | proved | through `Batch.handed`: `Batch.run_handed` |
| `Batch.Act.events` | proved | through `Batch.recorded`: `Batch.run_handed` |
| `Batch.journal` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.settle_kernel` |
| `Batch.handed` | proved | `Batch.run_handed` |
| `Batch.recorded` | proved | `Batch.run_handed` |
| `Batch.Act.Sound` | spec | a predicate |
| `Batch.Sound` | spec | a predicate |
| `Batch.Command.idle?` | spec | used only in statements |
| `Batch.settle` | spec | used only in statements |

## `Lanes/Runtime/IO/Park.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `ParkerImpl` | trusted | TRUSTED.md: The C |
| `Parker.new` | trusted | TRUSTED.md: The C |
| `Parker.parkFor` | trusted | TRUSTED.md: The C |
| `Parker.park` | trusted | TRUSTED.md: The C |
| `Parker.parkAtMost` | trusted | TRUSTED.md: The C |
| `Parker.unpark` | trusted | TRUSTED.md: The C |
| `Parker.wait` | trusted | TRUSTED.md: The C |
| `block` | trusted | TRUSTED.md: The C |

## `Lanes/Runtime/IO/Shell.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Runtime.running` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.startWith` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.start` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.input` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.tryInput` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.idle` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.batches` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.trace` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.state` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.stop` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.hasRecovered` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.depth` | trusted | TRUSTED.md: The runtime shell |
| `Runtime.ended` | trusted | TRUSTED.md: The runtime shell |

## `Lanes/Runtime/Kernel.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.cell` | proved | `Batch.run_peek`, `Journal.Upgrade.inv_load`, `Kernel.Plan.fixAll_local` and 12 more |
| `Kernel.setCell` | proved | through `Kernel.apply`, `Kernel.boot` and 8 more: `Batch.run_handed`, `Batch.run_kernel` and 49 more |
| `Kernel.abs` | proved | `Kernel.WellFormed.quiet_iff`, `Kernel.WellFormed.wait_forever`, `Kernel.abs_boot` and 7 more |
| `Kernel.env` | proved | `Kernel.abs_boot`, `Kernel.accept_sound`, `Kernel.exec_reachable` and 4 more |
| `Kernel.unschedule` | proved | through `Kernel.apply`, `Kernel.boot` and 8 more: `Batch.run_handed`, `Batch.run_kernel` and 49 more |
| `Kernel.perform` | proved | through `Kernel.apply`, `Kernel.boot` and 8 more: `Batch.run_handed`, `Batch.run_kernel` and 49 more |
| `Kernel.performAll` | proved | through `Kernel.apply`, `Kernel.boot` and 8 more: `Batch.run_handed`, `Batch.run_kernel` and 49 more |
| `Kernel.down` | proved | through `Kernel.apply`, `Kernel.boot` and 8 more: `Batch.run_handed`, `Batch.run_kernel` and 49 more |
| `Kernel.settle` | proved | `Kernel.setState_settle` |
| `Kernel.rest` | proved | through `Kernel.apply`, `Kernel.exec` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 40 more |
| `Kernel.takeState` | proved | through `Kernel.apply`, `Kernel.exec` and 5 more: `Batch.run_handed`, `Batch.run_kernel` and 40 more |
| `Kernel.handle` | proved | `Kernel.frame_handle`, `Kernel.handleAhead_eq`, `Kernel.handle_setState` |
| `Kernel.startActor` | proved | `Kernel.frame_startActor` |
| `Kernel.boot` | proved | `Http.kernel_fronted_answered_le_arrived`, `Http.kernel_served_answered_le_arrived`, `Journal.Disk.torn_nil` and 13 more |
| `Kernel.accept` | proved | `Kernel.accept_sound` |
| `Kernel.run1` | proved | `Kernel.run1Ahead_eq`, `Kernel.run1_sound` |
| `Kernel.fire` | proved | `Kernel.fire_sound`, `Kernel.frame_fire` |
| `Kernel.advance` | proved | through `Kernel.apply`, `Kernel.exec`: `Batch.run_handed`, `Batch.run_kernel` and 20 more |
| `Kernel.timerNext` | proved | through `Kernel.apply`, `Kernel.exec` and 2 more: `Batch.run_handed`, `Batch.run_kernel` and 33 more |
| `Kernel.step` | proved | `Kernel.WellFormed.runBatch_of_due`, `Kernel.WellFormed.step_events_ne_nil`, `Kernel.WellFormed.step_of_due` and 2 more |
| `Kernel.wait` | proved | `Kernel.WellFormed.step_events_ne_nil`, `Kernel.WellFormed.wait_for_ms`, `Kernel.WellFormed.wait_forever` and 1 more |
| `Kernel.runBatch` | proved | `Kernel.WellFormed.runBatch`, `Kernel.WellFormed.runBatch_of_due`, `Kernel.runBatchAhead_eq` and 6 more |
| `Kernel.quiet` | proved | `Batch.run_resolved`, `Kernel.WellFormed.quiet_iff` |
| `Kernel.image` | proved | `Batch.flush_save`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and 8 more |
| `Kernel.Image.kernel` | proved | `Batch.flush_save`, `Journal.Begun.resume_upgraded`, `Journal.Upgrade.begin_crash` and 3 more |
| `Kernel.apply` | proved | `Kernel.WellFormed.apply` |
| `Kernel.exec` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.settle_kernel` and 18 more |

## `Lanes/Runtime/KernelSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.outputs` | spec | used only in statements |

## `Lanes/Runtime/KernelTimers.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.Serves` | spec | a predicate |
| `Kernel.Fires` | spec | a predicate |

## `Lanes/Runtime/Mailbox.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Mailbox.offer` | proved | `Mailbox.Reachable.offer_full_iff` |
| `Mailbox.offerOrWait` | proved | through `Mailbox.Op.apply`, `Mailbox.boundedIn` and 2 more: `Mailbox.after_close`, `Mailbox.batch_since_take` and 3 more |
| `Mailbox.take` | proved | `Mailbox.Reachable.asleep_empty`, `Mailbox.batch_since_take`, `Mailbox.close_since_take` and 2 more |
| `Mailbox.rest` | proved | `Mailbox.rest_eq_false`, `Mailbox.woken_after_rest` |
| `Mailbox.close` | proved | `Mailbox.after_close`, `Mailbox.close_since_take` |

## `Lanes/Runtime/MailboxSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Mailbox.Op.apply` | spec | used only in statements |
| `Mailbox.exec` | spec | used only in statements |
| `Mailbox.Reachable` | spec | a predicate |
| `Mailbox.Reply.admitted` | spec | used only in statements |
| `Mailbox.Reply.woken` | spec | used only in statements |
| `Mailbox.Op.boundedIn` | spec | used only in statements |
| `Mailbox.Op.waitedIn` | spec | used only in statements |
| `Mailbox.Op.resetsSleeper` | spec | used only in statements |
| `Mailbox.boundedIn` | spec | used only in statements |
| `Mailbox.waitedIn` | spec | used only in statements |

## `Lanes/Runtime/Pace.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Pace.Rate.add` | tested | `Tests/Pace.lean` |
| `Pace.Rate.perUnit` | tested | `Tests/Pace.lean` |
| `Pace.unit_ns` | tested | `Tests/Pace.lean` |
| `Pace.busy` | tested | `Tests/Pace.lean` |
| `Pace.worth` | tested | `Tests/Pace.lean` |
| `Pace.cycles` | tested | `Tests/Pace.lean` |
| `Pace.prefer` | tested | `Tests/Pace.lean` |
| `Pace.probeAfter` | tested | `Tests/Pace.lean` |
| `Pace.choose` | tested | `Tests/Pace.lean` |
| `Pace.spread` | tested | `Tests/Pace.lean` |
| `Pace.cycleOf` | tested | `Tests/Pace.lean` |
| `Pace.record` | tested | `Tests/Pace.lean` |
| `Pace.observe` | tested | `Tests/Pace.lean` |
| `Pace.work` | tested | `Tests/Pace.lean` |

## `Lanes/Runtime/Release.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Event.awake` | spec | used only in statements |
| `SysState.Same` | spec | a predicate |
| `SysState.release` | spec | used only in statements |
| `SysState.Leads` | spec | a predicate |

## `Lanes/Runtime/Shard.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `shardSig` | proved | through `Event.merged?`, `Event.unsharded?`: `Shards.AtHome.step`, `SysState.AtHome.step` |
| `shardEffect` | tested | `Tests/Fronted.lean`, `Tests/Peers.lean` |
| `System.shard` | tested | `Tests/Fronted.lean`, `Tests/Peers.lean` |
| `Parcel.payload` | proved | `Parcel.receive_send` |
| `Parcel.ofPayload` | proved | through `Parcel.receive`: `Parcel.receive_send` |
| `Parcel.fits` | proved | `Parcel.receive_send` |
| `Parcel.send` | proved | `Parcel.receive_send` |
| `Parcel.receive` | proved | `Parcel.receive_send` |

## `Lanes/Runtime/ShardSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `instHashableSigma_lanes` | tested | `Tests/Split.lean` |
| `Signature.Inspect.shard` | tested | `Tests/Split.lean` |
| `System.Inspect.shard` | tested | `Tests/Split.lean` |
| `splitSig` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and 5 more |
| `shardWiring` | proved | through `System.split`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `System.split` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and 5 more |
| `Signature.Inspect.split` | tested | `Tests/Split.lean` |
| `System.Inspect.split` | tested | `Tests/Split.lean` |
| `Split.actorOf` | proved | through `EnvModel.split`, `Event.merged?` and 1 more: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Split.home` | spec | used only in statements |
| `Split.atHome` | proved | through `EnvModel.split`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 1 more |
| `Split.route` | tested | `Tests/Split.lean` |
| `Split.output?` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Split.msgOf` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Envelope.merged` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and 6 more |
| `Envelope.atHome` | tested | `Tests/Split.lean` |
| `Event.merged?` | spec | used only in statements |
| `Event.routed` | proved | `SysState.AtHome.step` |
| `EnvModel.split` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.SplitReachable.merged_of_init` |
| `SysState.merged` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and 5 more |
| `System.SteadyBoot` | spec | a predicate |

## `Lanes/Runtime/ShardsSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `joinAllSig` | proved | through `shardsSig`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `joinAllEffect` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `System.joinAll` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `shardsSig` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and 4 more |
| `shardsRoute` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `System.shards` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and 4 more |
| `Signature.Inspect.joinAll` | tested | `Tests/Split.lean` |
| `System.Inspect.joinAll` | tested | `Tests/Split.lean` |
| `Signature.Inspect.shards` | tested | `Tests/Split.lean` |
| `System.Inspect.shards` | tested | `Tests/Split.lean` |
| `Shards.atHome` | proved | through `EnvModel.shards`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 1 more |
| `Shards.route` | tested | `Tests/Split.lean` |
| `Shards.output?` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `Shards.routed` | proved | `Shards.AtHome.step` |
| `Envelope.unsharded` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and 5 more |
| `Envelope.atHomeAll` | tested | `Tests/Split.lean` |
| `Event.unsharded?` | spec | used only in statements |
| `EnvModel.shards` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.ShardsReachable.unsharded_of_init` |
| `SysState.unsharded` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and 4 more |
| `Shards.effect` | spec | used only in statements |

## `Lanes/Runtime/Wave.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.replay` | proved | through `Kernel.Plan.fixAll`, `Kernel.Plan.real` and 6 more: `Kernel.Plan.fixAll_local`, `Kernel.good_plan` and 7 more |
| `Kernel.ahead` | proved | through `Kernel.plan`, `Kernel.runWaves` and 1 more: `Kernel.good_plan`, `Kernel.runWaves_eq` and 2 more |
| `Kernel.Fits` | spec | a predicate |
| `Kernel.setState` | proved | `Kernel.Plan.fixAll_local`, `Kernel.handle_setState`, `Kernel.setState_settle` |
| `Kernel.restAs` | proved | through `Kernel.handleAhead`, `Kernel.run1Ahead` and 4 more: `Kernel.handleAhead_eq`, `Kernel.run1Ahead_eq` and 5 more |
| `Kernel.Plan.set` | proved | through `Kernel.handleAhead`, `Kernel.plan` and 5 more: `Kernel.good_plan`, `Kernel.handleAhead_eq` and 6 more |
| `Kernel.Plan.drop` | proved | through `Kernel.Plan.fixAll`, `Kernel.Plan.real` and 5 more: `Kernel.Plan.fixAll_local`, `Kernel.good_plan` and 7 more |
| `Kernel.Plan.reset` | proved | through `Kernel.run1Ahead`, `Kernel.runBatchAhead` and 3 more: `Kernel.run1Ahead_eq`, `Kernel.runBatchAhead_eq` and 4 more |
| `Kernel.Plan.fixAt` | proved | through `Kernel.Plan.fixAll`, `Kernel.Plan.real` and 5 more: `Kernel.Plan.fixAll_local`, `Kernel.good_plan` and 7 more |
| `Kernel.Plan.fixAll` | proved | `Kernel.Plan.fixAll_local` |
| `Kernel.Plan.real` | proved | `Kernel.good_plan`, `Kernel.handleAhead_eq`, `Kernel.run1Ahead_eq` and 3 more |
| `Kernel.Plan.Good` | spec | a predicate |
| `Kernel.handleAhead` | proved | `Kernel.handleAhead_eq` |
| `Kernel.run1Ahead` | proved | `Kernel.run1Ahead_eq` |
| `Kernel.stepAhead` | proved | `Kernel.stepAhead_eq` |
| `Kernel.runBatchAhead` | proved | `Kernel.runBatchAhead_eq`, `Kernel.wave_eq` |
| `Kernel.mail` | proved | through `Kernel.plan`, `Kernel.runWaves` and 1 more: `Kernel.good_plan`, `Kernel.runWaves_eq` and 2 more |
| `Kernel.Job.run` | proved | through `Kernel.plan`, `Kernel.runWaves` and 1 more: `Kernel.good_plan`, `Kernel.runWaves_eq` and 2 more |
| `Kernel.jobs` | proved | through `Kernel.plan`, `Kernel.runWaves` and 1 more: `Kernel.good_plan`, `Kernel.runWaves_eq` and 2 more |
| `Kernel.chunks` | proved | through `Kernel.plan`, `Kernel.runWaves` and 1 more: `Kernel.good_plan`, `Kernel.runWaves_eq` and 2 more |
| `Kernel.Plan.add` | proved | through `Kernel.plan`, `Kernel.runWaves` and 1 more: `Kernel.good_plan`, `Kernel.runWaves_eq` and 2 more |
| `Kernel.plan` | proved | `Kernel.good_plan`, `Kernel.wave_eq` |
| `Kernel.Frame` | spec | a predicate |
| `Kernel.waves` | proved | `Kernel.waves_eq` |
| `Kernel.runWaves` | proved | `Kernel.runWaves_eq` |
| `Kernel.acceptAll` | proved | `Kernel.exec_inputs` |

## `Lanes/Semantics/Account.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.run` | spec | used only in statements |
| `Account.pending` | proved | `Account.Moves.of_le` |
| `Account.owed` | proved | `Account.Moves.of_le` |
| `Account.Sim` | spec | a predicate |
| `Account.Moves` | spec | a predicate |
| `Account.Fires` | spec | a predicate |
| `Account.Passes` | spec | a predicate |
| `Account.Handles` | spec | a predicate |
| `Account.HandlesFire` | spec | a predicate |

## `Lanes/Semantics/FairJoin.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Obligation.inl` | spec | used only in statements |
| `Wiring.leftView` | spec | used only in statements |
| `Obligation.inr` | spec | used only in statements |
| `Wiring.rightView` | spec | used only in statements |
| `SysState.unhidden` | spec | used only in statements |
| `SysState.hidden` | spec | used only in statements |
| `System.underView` | spec | used only in statements |

## `Lanes/Semantics/FairRuns.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Obligation.instDecidableDue` | proved | its type, `Decidable` |
| `FairScheduler.Complete` | spec | a predicate |
| `System.fairChoice` | spec | used only in statements |
| `System.fairSchedule` | spec | used only in statements |
| `System.Run.fairAfter` | spec | used only in statements |

## `Lanes/Semantics/History.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.act` | proved | `System.Implements.produced` |
| `Service.play` | proved | `System.Implements.produced` |
| `Service.Produces` | spec | a predicate |

## `Lanes/Semantics/Link.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Envelope.on` | spec | used only in statements |
| `linkMsgs` | spec | used only in statements |

## `Lanes/Semantics/Liveness.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Spec.stutter` | proved | through `System.Run`, `System.Run.event` and 2 more: `Http.Gate.pending_answered`, `Http.fronted_arrival_answered` and 23 more |
| `Obligation.event` | proved | `Obligation.right?_inr`, `System.LeadsTo.ensures_of_invariant` |
| `Obligation.Due` | spec | a predicate |
| `Obligation.Restarted` | spec | a predicate |
| `System.Run.idle` | none |  |
| `System.Run.Restarts` | spec | a predicate |
| `System.Run.WeakFair` | spec | a predicate |
| `System.Run.Fair` | spec | a predicate |
| `System.Run.Impatient` | spec | a predicate |
| `System.LeadsTo` | spec | a predicate |

## `Lanes/Semantics/Monitor.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.State.toAbs` | proved | `Check.Monitor.complete`, `Check.Monitor.sound` |
| `Check.Monitor.observe` | spec | used only in statements |
| `Check.Monitor.after` | spec | used only in statements |

## `Lanes/Semantics/MonitorSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Monitor.abs` | spec | used only in statements |

## `Lanes/Semantics/Once.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.Once.take` | spec | used only in statements |
| `Service.once` | spec | used only in statements |
| `System.ImplementsOnce` | spec | a predicate |
| `Once.Server.Covered` | spec | a predicate |
| `Spec.showing` | spec | used only in statements |

## `Lanes/Semantics/Projection.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.Run.blockStart` | spec | used only in statements |
| `System.Run.blockOf` | spec | used only in statements |
| `System.Run.ofBlocks` | spec | used only in statements |
| `SysState.RestartsAlong` | spec | a predicate |

## `Lanes/Semantics/Refinement.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Spec.lts` | proved | `Account.Holds.passes`, `Check.Monitor.complete`, `Check.Monitor.ok_iff` and 10 more |
| `Spec.Reachable` | spec | a predicate |
| `Spec.Invariant` | spec | a predicate |
| `Refines` | spec | a predicate |

## `Lanes/Semantics/Schedule.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Schedule.Nearer` | spec | a predicate |

## `Lanes/Semantics/Service.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Service.spec` | proved | `Account.Holds.passes`, `Account.implements`, `Account.implements_timed` and 10 more |
| `Service.Stable` | spec | a predicate |
| `Service.Only` | spec | a predicate |
| `Service.Took` | spec | a predicate |
| `System.Implements` | spec | a predicate |
| `Server.abs` | spec | used only in statements |

## `Lanes/Semantics/Simulation.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.Stops` | spec | a predicate |

## `Lanes/Semantics/System.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `System.sem` | proved | `Account.implements`, `Account.implements_timed`, `Once.server_implements` and 14 more |
| `System.Refines` | spec | a predicate |

## `Lanes/Testing/Browser.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.Browser.new` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Browser.at` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.Kept.parse` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Kept.covers` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Browser.cookie` | tested | `Tests/OAuth.lean` |
| `Testing.Browser.keep` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Browser.forget` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean` |
| `Testing.Browser.record` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Browser.call` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Browser.get` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.Browser.post` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.Browser.submit` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |

## `Lanes/Testing/Http.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.listen` | tested | `Tests/Testing.lean` |
| `Testing.json` | tested | `Tests/Testing.lean` |
| `Testing.text` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.shows` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.status` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 4 more |
| `Testing.location` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean` |
| `Testing.entity?` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.unescape` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.between` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.field` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.Tag.attr?` | tested | `Tests/Testing.lean` |
| `Testing.Tag.nameChar` | tested | `Tests/Testing.lean` |
| `Testing.Tag.lower` | tested | `Tests/Testing.lean` |
| `Testing.Tag.Lexer.close` | tested | `Tests/Testing.lean` |
| `Testing.Tag.Lexer.step` | tested | `Tests/Testing.lean` |
| `Testing.tags` | tested | `Tests/Testing.lean` |
| `Testing.form?` | tested | `Tests/Testing.lean` |
| `Testing.setCookie` | tested | `Tests/Testing.lean` |
| `Testing.queryOf` | checked | `Tests/OAuth.lean` |
| `Testing.segments` | tested | `Tests/Testing.lean` |

## `Lanes/Testing/OAuth.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.OAuth.hasOpenssl` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.openssl` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.at` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.authorization` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.oidc` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.str` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.OAuth.Fake.discovery` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.yes` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.OAuth.readUser` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.OAuth.Fake.userApi` | tested | `Tests/OAuth.lean` |
| `Testing.OAuth.Fake.client` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.b64s` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.nowSeconds` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.mint` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.userJson` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.OAuth.emailsJson` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and 1 more |
| `Testing.OAuth.Fake.take` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.user?` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.handle` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.makeKeys` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.start` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.stop` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.approve` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.signIn` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |

## `Lanes/Testing/S3.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.S3.raw?` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.answer` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.failure` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.time?` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.decodePair` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.splitTarget` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.authField` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.verified` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.escapeKey` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.listXml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.range?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.serve` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.find?` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.split` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.quoted` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.formParts` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.formBody` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and 3 more |
| `Testing.S3.etag` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.servePost` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 5 more |
| `Testing.S3.unquote` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.multipartEtag` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.xmlAnswer` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.listPartsXml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.completedXml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.manifest?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.complete` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.serveMultipart` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.serveAll` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.Fake.start` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.Fake.object?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` |
| `Testing.S3.Fake.holds` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` |
| `Testing.S3.Fake.keys` | tested | `Tests/S3.lean` |
| `Testing.S3.Fake.refuse` | tested | `Tests/S3.lean` |
| `Testing.S3.Fake.refusing` | tested | `Tests/S3.lean` |
| `Testing.S3.Fake.stop` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 2 more |
| `Testing.S3.follow` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and 4 more |
| `Testing.S3.code` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and 2 more |
| `Testing.S3.postForm` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and 2 more |

## `Lanes/Testing/Transcode.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.Transcode.take` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.rendition` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.thumbnail` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.start` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.reportTo` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.fail` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.taken` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.post` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.render` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.work` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.forge` | tested | `Tests/Testing.lean` |
| `Testing.Transcode.Fake.stop` | tested | `Tests/Testing.lean` |

## `Lanes/Web/Auth/IdToken.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `OAuth.DisplayName.maxChars` | proved | `OAuth.DisplayName.length_le` |
| `OAuth.DisplayName.allowed` | proved | through `OAuth.DisplayName.val`, `OAuth.Identity` and 1 more: `OAuth.DisplayName.length_le`, `OAuth.IdToken.check_ok_iff` and 4 more |
| `OAuth.DisplayName.Valid` | spec | a predicate |
| `OAuth.DisplayName.instDecidableValid` | proved | its type, `Decidable` |
| `OAuth.DisplayName.of?` | proved | through `OAuth.IdToken.Claims.identity`: `OAuth.IdToken.check_ok_iff`, `OAuth.IdToken.verify_accepted` |
| `OAuth.DisplayName.clean` | proved | through `OAuth.IdToken.Claims.identity`: `OAuth.IdToken.check_ok_iff`, `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.Claims.identity` | proved | `OAuth.IdToken.check_ok_iff`, `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.optional` | proved | through `OAuth.IdToken.verify`: `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.string?` | proved | through `OAuth.IdToken.verify`: `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.nat?` | proved | through `OAuth.IdToken.verify`: `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.audience?` | proved | through `OAuth.IdToken.verify`: `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.Claims.read` | proved | `OAuth.IdToken.verify_accepted` |
| `OAuth.IdToken.check` | proved | `OAuth.IdToken.check_ok_iff` |
| `OAuth.IdToken.verify` | proved | `OAuth.IdToken.verify_accepted` |

## `Lanes/Web/Auth/Jose.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Jose.Alg.name` | spec | used only in statements |
| `Jose.Alg.parse?` | proved | `Jose.Alg.parse?_eq_some` |
| `Jose.Jwk.fits` | proved | `Jose.verify_ok`, `OAuth.IdToken.verify_accepted` |
| `Jose.str?` | proved | through `Jose.Compact.read`, `Jose.readHeader`: `Jose.Compact.read_alg`, `Jose.readHeader_alg` and 2 more |
| `Jose.bytes?` | proved | through `Jose.Compact.read`: `Jose.Compact.read_alg`, `Jose.verify_ok` and 1 more |
| `Jose.Jwk.read?` | proved | through `Jose.Compact.read`: `Jose.Compact.read_alg`, `Jose.verify_ok` and 1 more |
| `Jose.readKeys` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Signature.lean` |
| `Jose.readHeader` | proved | `Jose.readHeader_alg` |
| `Jose.Compact.read` | proved | `Jose.Compact.read_alg`, `Jose.verify_ok`, `OAuth.IdToken.verify_accepted` |
| `Jose.candidates` | proved | through `Jose.verify`: `Jose.verify_ok` |
| `Jose.verify` | proved | `Jose.verify_ok` |

## `Lanes/Web/Auth/Login.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Auth.instDecidableEqDigest` | proved | its type, `Decidable` |
| `Auth.instHashableDigest` | tested | `Tests/Auth.lean` |
| `Auth.instReprDigest` | tested | `Tests/Auth.lean` |
| `Auth.Digest.codec` | proved | its type, `Codec` |
| `Auth.instCodableDigest` | proved | its type, `Codable` |
| `Auth.Digest.hex` | tested | `Tests/Auth.lean` |
| `Auth.Digest.ofHex?` | tested | `Tests/Auth.lean` |
| `Auth.Password.salt` | tested | `Tests/Auth.lean` |
| `Auth.Password.digest` | tested | `Tests/Auth.lean` |
| `Auth.Attempts.codec` | proved | its type, `Codec` |
| `Auth.instCodableAttempts` | proved | its type, `Codable` |
| `Auth.Attempts.fail` | proved | `Auth.Attempts.bounded_fail`, `Auth.Attempts.fail_repeat`, `Auth.Attempts.locked_stays` and 1 more |
| `Auth.Attempts.succeed` | proved | `Auth.Attempts.bounded_succeed`, `Auth.Attempts.locked_stays` |
| `Auth.Attempts.unlock` | spec | used only in statements |
| `Auth.Attempts.Bounded` | spec | a predicate |
| `Auth.Session.codec` | proved | its type, `Codec` |
| `Auth.instCodableSession` | proved | its type, `Codable` |
| `Auth.Session.expired` | proved | `Auth.Session.expired_mono`, `Auth.Sessions.accepts_iff` |
| `Auth.Sessions.codec` | proved | its type, `Codec` |
| `Auth.instCodableSessions` | proved | its type, `Codable` |
| `Auth.Sessions.ids` | proved | `Auth.Sessions.ids_starts`, `Auth.Sessions.length_close_le`, `Auth.Sessions.length_start_le` and 1 more |
| `Auth.Sessions.at_s` | proved | through `Auth.Sessions.accepts`, `Auth.Sessions.start` and 1 more: `Auth.Sessions.Ended.run`, `Auth.Sessions.accepts_iff` and 5 more |
| `Auth.Sessions.sweep` | proved | `Auth.Sessions.sweep_ended` |
| `Auth.Sessions.start` | proved | `Auth.Sessions.ids_starts`, `Auth.Sessions.length_start_le`, `Auth.Sessions.live_open` and 1 more |
| `Auth.Sessions.close` | proved | `Auth.Sessions.length_close_le`, `Auth.Sessions.live_close` |
| `Auth.Sessions.live` | proved | `Auth.Sessions.live_close`, `Auth.Sessions.live_open` |
| `Auth.Sessions.accepts` | proved | `Auth.Sessions.Ended.run`, `Auth.Sessions.accepts_iff`, `Auth.Sessions.sweep_ended` |
| `Auth.Sessions.touch` | proved | through `Auth.Sessions.Op.apply`: `Auth.Sessions.Ended.run` |
| `Auth.Sessions.Ended` | spec | a predicate |
| `Auth.Sessions.Op.apply` | spec | used only in statements |
| `Auth.Sessions.Op.opens` | spec | used only in statements |

## `Lanes/Web/Auth/OAuth.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `OAuth.instReprSecret` | tested | `Tests/OAuth.lean` |
| `OAuth.instToStringSecret` | tested | `Tests/OAuth.lean` |
| `OAuth.b64` | checked | `Tests/OAuth.lean` |
| `OAuth.challenge` | checked | `Tests/OAuth.lean` |
| `OAuth.same` | proved | `OAuth.same_iff` |
| `OAuth.Ticket.payload` | checked | `Tests/OAuth.lean` |
| `OAuth.Ticket.read` | proved | through `OAuth.check`: `OAuth.check_ok` |
| `OAuth.Ticket.toCookie` | checked | `Tests/OAuth.lean` |
| `OAuth.Ticket.ofCookie` | proved | `OAuth.check_ok` |
| `OAuth.Ticket.derive` | checked | `Tests/OAuth.lean` |
| `OAuth.Ticket.grant` | checked | `Tests/OAuth.lean` |
| `OAuth.check` | proved | `OAuth.check_ok` |
| `OAuth.Used.claim` | proved | `OAuth.Used.claim_holds`, `OAuth.Used.claim_ok`, `OAuth.Used.claim_ok_holds` and 1 more |
| `OAuth.Used.Holds` | spec | a predicate |
| `OAuth.Used.run` | proved | `OAuth.Used.accepted_later`, `OAuth.Used.accepted_once` |
| `OAuth.authorizeUrl` | checked | `Tests/OAuth.lean` |
| `OAuth.Discovery.read` | checked | `Tests/OAuth.lean` |
| `OAuth.Discovery.provider` | checked | `Tests/OAuth.lean` |
| `OAuth.begin` | checked | `Tests/OAuth.lean` |
| `OAuth.Identity.under` | proved | `OAuth.Identity.under_cons` |
| `OAuth.Answer.state` | checked | `Tests/OAuth.lean` |
| `OAuth.Answer.read` | checked | `Tests/OAuth.lean` |
| `OAuth.tokenForm` | checked | `Tests/OAuth.lean` |
| `OAuth.Tokens.read` | checked | `Tests/OAuth.lean` |
| `OAuth.tokenAnswer` | checked | `Tests/OAuth.lean` |
| `OAuth.userAnswer` | checked | `Tests/OAuth.lean` |
| `OAuth.keysAnswer` | tested | `Tests/OAuth.lean` |
| `OAuth.Keys.lookup` | proved | `OAuth.Keys.lookup_fetch`, `OAuth.Keys.no_fetch_within` |
| `OAuth.Keys.fetched` | proved | `OAuth.Keys.no_fetch_within` |
| `OAuth.route` | tested | `Tests/OAuth.lean` |
| `OAuth.identityHeaders` | proved | through `OAuth.strip`: `OAuth.identity?_strip`, `OAuth.identity?_withIdentity` |
| `OAuth.strip` | proved | `OAuth.identity?_strip`, `OAuth.identity?_withIdentity` |
| `OAuth.withIdentity` | proved | `OAuth.identity?_withIdentity` |
| `OAuth.identity?` | proved | `OAuth.identity?_strip`, `OAuth.identity?_withIdentity` |
| `OAuth.beginResponse` | tested | `Tests/OAuth.lean` |
| `OAuth.Refusal.describe` | checked | `Tests/OAuth.lean` |
| `OAuth.refusedResponse` | checked | `Tests/OAuth.lean` |
| `OAuth.Endpoint.parse` | tested | `Tests/OAuth.lean` |

## `Lanes/Web/Auth/Token.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hmac.Key.of` | checked | `Tests/OAuth.lean` |
| `Hmac.Key.mac` | proved | `Auth.checkForm_other`, `Auth.verify_sign_other` |
| `Auth.message` | proved | `Auth.checkForm_other`, `Auth.message_inj`, `Auth.verify_sign_other` |
| `Auth.tag` | proved | through `Auth.checkForm`, `Auth.sign`: `Auth.checkForm_formToken`, `Auth.checkForm_iff` and 4 more |
| `Auth.sign` | proved | `Auth.verify_eq_some`, `Auth.verify_sign`, `Auth.verify_sign_other` |
| `Auth.verify` | proved | `Auth.verify_eq_some`, `Auth.verify_sign`, `Auth.verify_sign_other` |
| `Auth.formToken` | proved | `Auth.checkForm_formToken`, `Auth.checkForm_iff`, `Auth.checkForm_other` |
| `Auth.checkForm` | proved | `Auth.checkForm_formToken`, `Auth.checkForm_iff`, `Auth.checkForm_other` |

## `Lanes/Web/Html/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Html.empty` | tested | `Tests/Html.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and 1 more |
| `Html.instInhabited` | tested | `Tests/Html.lean` |
| `Html.escapeChar` | proved | through `Html.escape`, `Html.render`: `Html.escape_safe`, `Html.lex_render` and 1 more |
| `Html.escape` | proved | `Html.escape_safe` |
| `Html.nameChar` | proved | `Html.mem_safeName`, `Html.nameChar_safe` |
| `Html.safeName` | proved | `Html.mem_safeName`, `Html.render_void` |
| `Html.voidTags` | proved | `Html.render_void` |
| `Html.rawTextTags` | proved | through `Html.render`, `Html.tokens`: `Html.lex_render`, `Html.render_void` |
| `Html.urlAttrs` | proved | through `Html.render`, `Html.tokens`: `Html.lex_render`, `Html.render_void` |
| `Html.allowedSchemes` | proved | `Html.safeUrl_scheme` |
| `Html.blockedUrl` | proved | `Html.safeUrl_eq`, `Html.safeUrl_scheme` |
| `Html.urlBlank` | proved | `Html.safeUrl_scheme` |
| `Html.safeUrl` | proved | `Html.safeUrl_eq`, `Html.safeUrl_scheme` |
| `Html.Attr.shown` | proved | through `Html.render`, `Html.tokens`: `Html.lex_render`, `Html.render_void` |
| `Html.Attr.render` | proved | `Html.render_void` |
| `Html.isTagName` | proved | through `Html.render`, `Html.tokens`: `Html.lex_render`, `Html.render_void` |
| `Html.startTag` | proved | `Html.render_void` |
| `Html.endTag` | proved | through `Html.render`: `Html.lex_render`, `Html.render_void` |
| `Html.render` | proved | `Html.lex_render`, `Html.render_void` |
| `Html.renderAll` | proved | through `Html.render`: `Html.lex_render`, `Html.render_void` |
| `Html.classes` | tested | `Tests/Html.lean` |
| `Html.document` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `instToHtmlHtml` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `instToHtmlString` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `instToHtmlNat` | tested | `Tests/Html.lean` |
| `instToHtmlInt` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 2 more |
| `instToHtmlList` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `instToHtmlArray` | tested | `Tests/Html.lean` |
| `instToHtmlOption` | tested | `Tests/Html.lean` |
| `instToAttrString` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `instToAttrListString` | tested | `Tests/Html.lean` |
| `instToAttrNat` | tested | `Tests/Html.lean` |
| `instToAttrInt` | tested | `Tests/Html.lean` |
| `instToAttrBool` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `instToAttrOption` | tested | `Tests/Html.lean` |

## `Lanes/Web/Html/BasicSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Html.Attr.token` | spec | used only in statements |
| `Html.tokens` | spec | used only in statements |
| `Html.tokensAll` | spec | used only in statements |
| `Html.charRef` | spec | used only in statements |
| `Html.Lexer.step` | spec | used only in statements |
| `Html.lex` | spec | used only in statements |
| `Html.schemeChar` | spec | used only in statements |
| `Html.scheme?` | spec | used only in statements |

## `Lanes/Web/Html/Htmx.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hx.methodAttr` | proved | `Hx.methodAttr_inj`, `Hx.request_match?` |
| `Hx.request` | proved | `Hx.request_match?` |
| `Hx.target` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 2 more |
| `Hx.Swap.name` | tested | `Tests/Html.lean` |
| `Hx.swap` | tested | `Tests/Html.lean` |
| `Hx.eventName` | proved | `Hx.eventName_plain`, `Hx.mem_eventName` |
| `Hx.Trigger.render` | proved | `Hx.render_plain` |
| `Hx.trigger` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 2 more |
| `Hx.confirm` | tested | `Tests/Html.lean` |
| `Hx.boost` | tested | `Tests/Html.lean` |
| `Hx.pushUrl` | tested | `Tests/Html.lean` |
| `Hx.indicator` | tested | `Tests/Html.lean` |
| `Hx.events` | tested | `Tests/Html.lean` |
| `Http.Request.isHtmx` | tested | `Tests/Html.lean` |
| `Http.Response.trigger` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 2 more |
| `Http.Response.hxRedirect` | tested | `Tests/Html.lean` |

## `Lanes/Web/Http/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.reprBody` | proved | through `Http.Request.field?`, `Http.Request.form`: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` |
| `Http.Method.codec` | proved | its type, `Codec` |
| `Http.Request.codec` | proved | its type, `Codec` |
| `Http.hexValue?` | proved | through `Http.Request.field?`, `Http.Request.form` and 4 more: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` and 4 more |
| `Http.percentDecodeBytes` | proved | through `Http.Request.field?`, `Http.Request.form` and 3 more: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` and 3 more |
| `Http.percentDecode` | proved | `Http.percentDecode_percentEncode` |
| `Http.hexDigit` | proved | through `Http.encodeForm`, `Http.percentEncode`: `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` and 2 more |
| `Http.unreserved` | proved | through `Http.encodeForm`, `Http.percentEncode`: `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` and 2 more |
| `Http.percentEncodeByte` | proved | through `Http.encodeForm`, `Http.percentEncode`: `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` and 2 more |
| `Http.percentEncode` | proved | `Http.percentDecode_percentEncode`, `Http.percentEncode_plain` |
| `Http.parseForm` | proved | `Http.parseForm_encodeForm` |
| `Http.encodeForm` | proved | `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` |
| `Http.Request.param?` | spec | used only in statements |
| `Http.Request.header?` | proved | `Http.Conn.respond_opens`, `Http.Request.header?_eq_lookup`, `Http.Request.sameOrigin_iff` and 1 more |
| `Http.Request.text?` | proved | through `Http.Request.field?`, `Http.Request.form`: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` |
| `Http.Request.form` | proved | `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` |
| `Http.Request.field?` | proved | `Http.Request.field?_eq_lookup` |
| `Http.Response.ofText` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean`, `Tests/HttpConn.lean` and 3 more |
| `Http.Response.text` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean`, `Tests/HttpConn.lean` and 3 more |
| `Http.Response.html` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Response.json` | tested | `Tests/Html.lean` |
| `Http.Response.empty` | tested | `Tests/Auth.lean`, `Tests/Html.lean` |
| `Http.Response.redirect` | checked | `Tests/SharedCache.lean` |
| `Http.Response.withHeader` | checked | `Tests/SharedCache.lean` |

## `Lanes/Web/Http/Conn.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Conn.closing` | proved | through `Http.Conn.answer`, `Http.Conn.encode` and 8 more: `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` and 20 more |
| `Http.Conn.nosniff` | proved | through `Http.Conn.answer`, `Http.Conn.encode` and 7 more: `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` and 19 more |
| `Http.Conn.sendable` | proved | `Http.Conn.read_encode`, `Http.Conn.sendable_writable` |
| `Http.Conn.encode` | proved | `Http.Conn.answer_waiting`, `Http.Conn.read_encode` |
| `Http.Conn.refusal` | proved | through `Http.Conn.pump`, `Http.Conn.run` and 1 more: `Http.Conn.pump_piece`, `Http.Conn.run_buffer` and 8 more |
| `Http.Conn.timeout` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.continueWire` | proved | through `Http.Conn.pump`, `Http.Conn.run` and 1 more: `Http.Conn.pump_piece`, `Http.Conn.run_buffer` and 8 more |
| `Http.Conn.streamed` | proved | `Http.Conn.read_streamed` |
| `Http.Conn.streamable` | proved | `Http.Conn.read_streamed`, `Http.Conn.respond_opens` |
| `Http.Conn.streamHead` | proved | `Http.Conn.read_streamed`, `Http.Conn.respond_opens` |
| `Http.Conn.lastChunk` | proved | `Http.Conn.flushStream_ended`, `Http.Conn.read_streamed` |
| `Http.Conn.heartbeatChunk` | proved | `Http.Conn.flushStream_going` |
| `Http.Conn.next` | proved | `Http.Conn.run_submits` |
| `Http.Conn.room` | proved | `Http.Conn.wantsInput_room` |
| `Http.Conn.wantsInput` | proved | `Http.Conn.wantsInput_room` |
| `Http.Conn.deadline` | proved | `Http.Conn.step_tick` |
| `Http.Conn.settle` | proved | through `Http.Conn.pump`, `Http.Conn.run` and 1 more: `Http.Conn.pump_piece`, `Http.Conn.run_buffer` and 8 more |
| `Http.Conn.waitMore` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.streamHead?` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.Inflow.start` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.begin` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.take` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.flushSlots` | proved | through `Http.Conn.flushStream`, `Http.Conn.run` and 1 more: `Http.Conn.flushStream_ended`, `Http.Conn.flushStream_going` and 9 more |
| `Http.Conn.flush` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.finish` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.Inflow.next` | proved | through `Http.Conn.Inflow.gather`, `Http.Conn.run` and 1 more: `Http.Conn.gather_length`, `Http.Conn.pump_piece` and 9 more |
| `Http.Conn.Inflow.gather` | proved | `Http.Conn.gather_length`, `Http.Conn.pump_piece` |
| `Http.Conn.Slot.isOpened` | proved | through `Http.Conn.answer`, `Http.Conn.flushStream` and 5 more: `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` and 17 more |
| `Http.Conn.pump` | proved | `Http.Conn.pump_piece` |
| `Http.Conn.took` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.respond` | proved | `Http.Conn.respond_ignored`, `Http.Conn.respond_opens` |
| `Http.Conn.Outflow.accept` | proved | through `Http.Conn.flushStream`, `Http.Conn.pulled` and 2 more: `Http.Conn.flushStream_ended`, `Http.Conn.flushStream_going` and 12 more |
| `Http.Conn.pulled` | proved | `Http.Conn.pulled_ignored`, `Http.Conn.pulled_large`, `Http.Conn.pulled_part` |
| `Http.Conn.flushStream` | proved | `Http.Conn.flushStream_ended`, `Http.Conn.flushStream_going` |
| `Http.Conn.earlier` | tested | `Tests/Loopback.lean` |
| `Http.Conn.wakeAt` | tested | `Tests/Loopback.lean` |
| `Http.Conn.drain` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.advance` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.Slot.stop` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.quiet` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.answer` | proved | `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` |
| `Http.Conn.receive` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.expire` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and 7 more |
| `Http.Conn.step` | proved | `Http.Conn.step_closed`, `Http.Conn.step_notReading`, `Http.Conn.step_reading` and 2 more |
| `Http.Conn.run` | proved | `Http.Conn.run_buffer`, `Http.Conn.run_slots`, `Http.Conn.run_submits` and 1 more |
| `Http.Conn.Count.admit` | proved | `Http.Conn.Count.admit_le`, `Http.Conn.Count.admit_stopping` |
| `Http.Conn.Count.leave` | tested | `Tests/HttpConn.lean` |

## `Lanes/Web/Http/ConnSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Conn.Action.wrote` | spec | used only in statements |
| `Http.Conn.Action.submitted` | spec | used only in statements |
| `Http.Conn.Frame` | spec | a predicate |
| `Http.Conn.Calm` | spec | a predicate |
| `Http.Conn.Writes` | spec | a predicate |
| `Http.Conn.Submits` | spec | a predicate |
| `Http.Conn.Keeps` | spec | a predicate |
| `Http.Conn.Bounded` | spec | a predicate |
| `Http.Conn.Reads` | spec | a predicate |

## `Lanes/Web/Http/Cookie.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.SameSite.name` | proved | through `Http.Cookie.header`, `Http.Response.setCookie`: `Http.readSetCookie_header`, `Http.setCookie_read` |
| `Http.cookieOctet` | proved | `Http.parseCookies_cookieHeader` |
| `Http.Cookie.valid` | proved | `Http.readSetCookie_header` |
| `Http.Cookie.attributes` | proved | `Http.readSetCookie_header`, `Http.setCookie_read` |
| `Http.Cookie.header` | proved | `Http.readSetCookie_header` |
| `Http.Cookie.expired` | tested | `Tests/Auth.lean` |
| `Http.trimBlank` | proved | through `Http.parseCookies`, `Http.readSetCookie`: `Http.parseCookies_cookieHeader`, `Http.readSetCookie_header` and 1 more |
| `Http.parseCookie` | proved | through `Http.parseCookies`: `Http.parseCookies_cookieHeader` |
| `Http.parseCookies` | proved | `Http.parseCookies_cookieHeader` |
| `Http.Request.cookies` | tested | `Tests/Auth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and 1 more |
| `Http.Request.cookie?` | tested | `Tests/Auth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and 1 more |
| `Http.Request.sameOrigin` | proved | `Http.Request.sameOrigin_iff` |
| `Http.Request.bodyWithin` | spec | used only in statements |
| `Http.hostCookie` | tested | `Tests/Auth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and 1 more |
| `Http.Response.setCookie` | proved | `Http.setCookie_read` |
| `Http.Response.clearCookie` | tested | `Tests/Auth.lean` |
| `Http.Response.noStore` | checked | `Tests/SharedCache.lean` |
| `Http.Response.noFraming` | tested | `Tests/Html.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and 1 more |

## `Lanes/Web/Http/CookieSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.readSetCookie` | spec | used only in statements |
| `Http.cookieHeader` | spec | used only in statements |

## `Lanes/Web/Http/Front.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.gateSig` | proved | `Http.Gate.always_up`, `Http.Gate.answered_le_handled`, `Http.Gate.answered_of_leaves` and 19 more |
| `Http.gateActor` | proved | `Http.gateActor_bounded` |
| `Http.gateSystem` | proved | `Http.Gate.always_up`, `Http.Gate.answered_le_handled`, `Http.Gate.answered_of_leaves` and 4 more |
| `Http.frontWiring` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and 16 more |
| `Http.frontedSig` | proved | `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup`, `Http.fronted_arrival_answered` and 6 more |
| `Http.frontedInput` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and 16 more |
| `Http.frontedOutput` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and 16 more |
| `Http.fronted` | proved | `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup`, `Http.fronted_arrival_answered` and 6 more |
| `Http.servedSig` | proved | `Http.kernel_served_answered_le_arrived`, `Http.served_answered_le_arrived`, `Http.served_answered_nodup` and 6 more |
| `Http.served` | proved | `Http.kernel_served_answered_le_arrived`, `Http.served_answered_le_arrived`, `Http.served_answered_nodup` and 6 more |
| `Signature.Inspect.gate` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `System.Inspect.gate` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `Signature.Inspect.fronted` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `System.Inspect.fronted` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean` |
| `Signature.Inspect.served` | checked | `Tests/Gate.lean` |
| `System.Inspect.served` | checked | `Tests/Gate.lean` |
| `Http.Bridge.shard` | tested | `Tests/Fronted.lean` |
| `Http.frontedActors` | tested | `Tests/Fronted.lean` |
| `Http.servedActors` | none |  |
| `Http.frontedOutside` | tested | `Tests/Fronted.lean`, `Tests/Web.lean` |
| `Http.servedOutside` | tested | `Tests/Web.lean` |

## `Lanes/Web/Http/FrontSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Gate.answered` | spec | used only in statements |
| `Http.Gate.handled` | spec | used only in statements |
| `Http.Gate.Armed` | spec | a predicate |
| `Http.Fronted.arrived` | spec | used only in statements |
| `Http.Fronted.answered` | spec | used only in statements |
| `Http.Fronted.Armed` | spec | a predicate |
| `Http.Served.arrived` | spec | used only in statements |
| `Http.Served.answered` | spec | used only in statements |
| `Http.Served.Armed` | spec | a predicate |

## `Lanes/Web/Http/Gate.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.instHashableGateMsgOfOut` | proved | through `Http.Gate.step`: `Http.Gate.step_arrive`, `Http.Gate.step_bounded` |
| `Http.instReprGateMsgOfOut` | none |  |
| `Http.busy` | proved | through `Http.Gate.step`: `Http.Gate.step_arrive`, `Http.Gate.step_bounded` |
| `Http.timedOut` | proved | through `Http.Gate.step`: `Http.Gate.step_arrive`, `Http.Gate.step_bounded` |
| `Http.Gate.step` | proved | `Http.Gate.step_arrive`, `Http.Gate.step_bounded` |

## `Lanes/Web/Http/Grammar.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.tokenChar` | proved | `Http.visible_of_tokenChar` |
| `Http.token` | proved | `Http.Request.fields_token`, `Http.parseCookies_cookieHeader` |
| `Http.plain` | proved | `Http.Request.headOnly_plain`, `Http.Request.head_plain`, `Http.plain_of_visible` |
| `Http.visible` | proved | `Http.Request.target_visible`, `Http.plain_of_visible`, `Http.visible_of_tokenChar` |
| `Http.ows` | proved | `Http.Request.read_blankInName` |
| `Http.trimOws` | proved | through `Http.Request.fieldName`: `Http.Request.read_lengthAndCoding`, `Http.Request.read_twoLengths` |
| `Http.isQdtext` | proved | `MediaType.isQdtext_of` |
| `Http.isQuotable` | proved | `MediaType.isQdtext_of`, `MediaType.quoted_esc` |
| `Http.quoted` | proved | `MediaType.quoted_esc` |

## `Lanes/Web/Http/Loopback.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Loopback.start` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.submit` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.told` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.perform` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.tell` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.settle` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.converse` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.send` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.get` | tested | `Tests/Loopback.lean` |
| `Http.Loopback.post` | tested | `Tests/Loopback.lean` |

## `Lanes/Web/Http/Ops.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.LogSink.isOn` | tested | `Tests/Ops.lean` |
| `Http.OpsConfig.counting` | tested | `Tests/Ops.lean` |
| `Http.OpsConfig.active` | tested | `Tests/Ops.lean` |
| `Http.Ops.pathText` | proved | `Http.Ops.route?_hidden`, `Http.Ops.route?_some` |
| `Http.Ops.fromLoopback` | proved | `Http.Ops.allows_eq_true`, `Http.Ops.route?_metrics`, `Http.Ops.route?_metrics_loopback` |
| `Http.Ops.bearer?` | proved | `Http.Ops.allows_eq_true`, `Http.Ops.route?_metrics` |
| `Http.Ops.allows` | proved | `Http.Ops.allows_eq_true`, `Http.Ops.route?_hidden` |
| `Http.Ops.route?` | proved | `Http.Ops.route?_default`, `Http.Ops.route?_hidden`, `Http.Ops.route?_metrics` and 3 more |
| `Http.Ops.Health.ready` | proved | `Http.Ops.answer_ready` |
| `Http.Ops.answer` | proved | `Http.Ops.answer_ready` |
| `Http.Ops.methodName` | proved | through `Http.Ops.Access.json`: `Http.Ops.Access.parse_line` |
| `Http.Ops.statusClass` | tested | `Tests/Ops.lean` |
| `Http.Ops.bumpKey` | proved | `Http.Ops.lookup_bumpKey` |
| `Http.Ops.Stats.answered` | tested | `Tests/Ops.lean` |
| `Http.Ops.Stats.refuse` | tested | `Tests/Ops.lean` |
| `Http.Ops.Stats.appended` | tested | `Tests/Ops.lean` |
| `Http.Ops.Stats.saved` | tested | `Tests/Ops.lean` |
| `Http.Ops.families` | tested | `Tests/Ops.lean` |
| `Http.Ops.RequestId.allowed` | proved | `Http.Ops.RequestId.accept?_eq_some` |
| `Http.Ops.RequestId.accept?` | proved | `Http.Ops.RequestId.accept?_eq_some`, `Http.Ops.RequestId.accept?_ofBytes` |
| `Http.Ops.RequestId.ofBytes` | proved | `Http.Ops.RequestId.accept?_ofBytes` |
| `Http.Ops.RequestId.tag` | proved | `Http.Ops.RequestId.header_tag` |
| `Http.Ops.Access.time` | proved | through `Http.Ops.Access.json`: `Http.Ops.Access.parse_line` |
| `Http.Ops.Access.json` | proved | `Http.Ops.Access.parse_line` |
| `Http.Ops.Access.line` | proved | `Http.Ops.Access.parse_line` |

## `Lanes/Web/Http/ReadRequest.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Refusal.status` | tested | `Tests/ReadRequest.lean` |
| `Http.matchAt` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.find` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.pieces` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.Limits.message_max` | proved | `Http.Request.read_done`, `Http.Request.read_more` |
| `Http.Request.elements` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.version?` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.method?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.pchar` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.targetChar` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.hostChar` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.segments?` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.queryPart?` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.pair?` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.query?` | proved | through `Http.Request.read`, `Http.Request.readHead` and 1 more: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 17 more |
| `Http.Request.target?` | proved | `Http.Route.link_target`, `Http.Route.match?_target`, `Http.dispatch_link` and 1 more |
| `Http.Request.fieldLine?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.host?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.tabbedFraming` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.framing?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and 13 more |
| `Http.Request.parseHead` | proved | `Http.Request.readHead_headWire` |
| `Http.Request.readHead` | proved | `Http.Request.readHead_headWire`, `Http.Request.read_badChunkSize` |
| `Http.Request.chunkSize` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and 12 more |
| `Http.Request.chunks` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and 12 more |
| `Http.Request.Head.close` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and 12 more |
| `Http.Request.Head.expectsContinue` | tested | `Tests/ReadRequest.lean` |
| `Http.Request.Head.incoming` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and 12 more |
| `Http.Request.read` | proved | `Http.Conn.step_submit_read`, `Http.Request.read_append`, `Http.Request.read_badChunkSize` and 11 more |

## `Lanes/Web/Http/ReadRequestSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Request.fits` | proved | `Http.Request.read_wire`, `Http.Request.read_wire_extract` |
| `Http.Request.sent` | proved | `Http.Request.read_wire` |
| `Http.Request.headWire` | spec | used only in statements |
| `Http.findL` | spec | used only in statements |
| `Http.encodedChar` | spec | used only in statements |
| `Http.Request.fieldName` | spec | used only in statements |
| `Http.Request.hexByte` | spec | used only in statements |

## `Lanes/Web/Http/Route.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Segment.Clean` | spec | a predicate |
| `Http.instDecidableClean` | proved | its type, `Decidable` |
| `Http.Slug.ofString?` | proved | `Http.Slug.ofString?_eq_some`, `Http.Slug.ofString?_text` |
| `Http.Slug.instToString` | tested | `Tests/Html.lean` |
| `Http.Slug.instDecidableEq` | proved | its type, `Decidable` |
| `Http.Path.seg` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Path.slug` | tested | `Tests/Html.lean`, `Tests/Loopback.lean`, `Tests/TutorialWeb.lean` and 3 more |
| `Http.Path.nat` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Path.root` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Path.append` | tested | `Tests/Html.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and 1 more |
| `Http.Path.pre` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Route.get` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Route.post` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and 5 more |
| `Http.Route.put` | tested | `Tests/Html.lean` |
| `Http.Route.patch` | tested | `Tests/Html.lean` |
| `Http.Route.delete` | tested | `Tests/Html.lean` |
| `Http.Route.match?` | proved | `Http.Route.match?_link`, `Http.Route.match?_target`, `Hx.request_match?` |
| `Http.Route.link` | proved | `Http.Route.link_target`, `Http.Route.match?_target`, `Http.dispatch_link` |
| `Http.Route.handle` | proved | `Http.dispatch_link` |
| `Http.dispatch` | proved | `Http.dispatch_eq_none`, `Http.dispatch_eq_some`, `Http.dispatch_link` |

## `Lanes/Web/Http/SharedCache.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.SharedCache.directives` | proved | through `Http.SharedCache.leaks`, `Http.SharedCache.outside` and 1 more: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_reuses` and 1 more |
| `Http.SharedCache.says` | proved | `Http.SharedCache.serve_storable` |
| `Http.SharedCache.vary` | proved | `Http.SharedCache.serve_reuses` |
| `Http.SharedCache.explicitlyFresh` | proved | through `Http.SharedCache.leaks`, `Http.SharedCache.outside`: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_storable` |
| `Http.SharedCache.heuristic` | proved | through `Http.SharedCache.leaks`, `Http.SharedCache.outside`: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_storable` |
| `Http.SharedCache.storable` | proved | `Http.SharedCache.serve_storable` |
| `Http.SharedCache.reuses` | proved | through `Http.SharedCache.Store.serve?`, `Http.SharedCache.leaks`: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_reuses` and 1 more |
| `Http.SharedCache.Store.observe` | proved | through `Http.SharedCache.outside`: `Http.SharedCache.serve_storable` |
| `Http.SharedCache.Store.serve?` | proved | `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_reuses`, `Http.SharedCache.serve_storable` |
| `Http.SharedCache.outside` | proved | `Http.SharedCache.serve_storable` |
| `Http.SharedCache.Store.Sound` | spec | a predicate |
| `Http.SharedCache.leaks` | proved | `Http.SharedCache.serve_of_leaks` |

## `Lanes/Web/Http/SigV4.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `SigV4.instReprSecret` | tested | `Tests/SigV4.lean` |
| `SigV4.instToStringSecret` | tested | `Tests/SigV4.lean` |
| `SigV4.stamp` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.day` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.credentialScope` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.encode` | proved | `SigV4.encode_chunks` |
| `SigV4.segments` | proved | `SigV4.decodePath_canonicalPath` |
| `SigV4.canonicalPath` | proved | `SigV4.decodePath_canonicalPath`, `SigV4.target_sign` |
| `SigV4.encodePair` | proved | `SigV4.sortQuery_sorted` |
| `SigV4.pairLe` | proved | `SigV4.sortQuery_sorted` |
| `SigV4.sortQuery` | proved | `SigV4.canonicalQuery_sortQuery`, `SigV4.sortQuery_perm`, `SigV4.sortQuery_sorted` |
| `SigV4.canonicalQuery` | proved | `SigV4.canonicalQuery_sortQuery`, `SigV4.target_sign` |
| `SigV4.blank` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and 2 more |
| `SigV4.squeeze` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and 2 more |
| `SigV4.trimValue` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and 2 more |
| `SigV4.insertHeader` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and 2 more |
| `SigV4.canonicalHeaders` | proved | `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted`, `SigV4.mem_canonicalHeaders` |
| `SigV4.signedHeaders` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.canonicalRequest` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.algorithm` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.unsignedPayload` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/SigV4.lean`, `Tests/S3.lean` and 1 more |
| `SigV4.payloadHash` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean` and 6 more |
| `SigV4.stringToSign` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.signingKey` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.signature` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.authorization` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.verb` | tested | `Tests/SigV4.lean` |
| `SigV4.signedFields` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.sign` | proved | `SigV4.target_sign` |
| `SigV4.presign` | tested | `Tests/S3.lean`, `Tests/SigV4.lean` |

## `Lanes/Web/Http/SigV4Sound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `SigV4.upperHex` | spec | used only in statements |
| `SigV4.unreservedChar` | spec | used only in statements |
| `SigV4.chunk` | spec | used only in statements |
| `SigV4.decodePath` | spec | used only in statements |

## `Lanes/Web/Http/Sse.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Sse.Event.lines` | proved | through `Http.Sse.written`: `Http.Sse.parse_written` |
| `Http.Sse.Event.chars` | proved | through `Http.Sse.written`: `Http.Sse.parse_written` |
| `Http.Sse.Event.encode` | tested | `Tests/Loopback.lean` |
| `Http.Sse.Event.valid` | spec | used only in statements |
| `Http.Sse.Event.lf` | proved | through `Http.Sse.Event.ofResponse`, `Http.Sse.parse`: `Http.Sse.Event.ofResponse_valid`, `Http.Sse.parse_written` |
| `Http.Sse.Event.oneLine` | proved | through `Http.Sse.Event.ofResponse`: `Http.Sse.Event.ofResponse_valid` |
| `Http.Sse.Event.header?` | proved | through `Http.Sse.Event.ofResponse`: `Http.Sse.Event.ofResponse_valid` |
| `Http.Sse.Event.ofResponse` | proved | `Http.Sse.Event.ofResponse_valid` |
| `Http.Sse.Event.response` | checked | `Tests/HttpStream.lean` |
| `Http.Sse.heartbeat` | tested | `Tests/Loopback.lean` |
| `Http.Sse.Reader.field` | proved | through `Http.Sse.parse`: `Http.Sse.parse_written` |
| `Http.Sse.Reader.lines` | proved | through `Http.Sse.parse`: `Http.Sse.parse_written` |
| `Http.Sse.splitLf` | proved | through `Http.Sse.parse`: `Http.Sse.parse_written` |
| `Http.Sse.parse` | proved | `Http.Sse.parse_written` |
| `Http.Sse.chunksFrom` | tested | `Tests/Loopback.lean` |
| `Http.Sse.received` | tested | `Tests/Loopback.lean` |

## `Lanes/Web/Http/SseSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Sse.written` | spec | used only in statements |

## `Lanes/Web/Http/Stream.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Stream.kindName` | proved | through `Http.Stream.piece`, `Http.Stream.pull`: `Http.Conn.flushStream_going`, `Http.Conn.pump_piece` |
| `Http.Stream.indexName` | proved | through `Http.Stream.piece`, `Http.Stream.pull`: `Http.Conn.flushStream_going`, `Http.Conn.pump_piece` |
| `Http.Stream.afterName` | proved | through `Http.Stream.pull`: `Http.Conn.flushStream_going` |
| `Http.Stream.headName` | tested | `Tests/Fixtures/Upload.lean`, `Tests/Loopback.lean`, `Tests/Web.lean` |
| `Http.Stream.piece` | proved | `Http.Conn.pump_piece` |
| `Http.Stream.pull` | proved | `Http.Conn.flushStream_going` |
| `Http.Stream.tag` | tested | `Tests/Loopback.lean` |
| `Http.Stream.msg?` | tested | `Tests/Fixtures/Upload.lean`, `Tests/Loopback.lean`, `Tests/Web.lean` |
| `Http.Stream.part` | proved | `Http.Conn.pulled_large`, `Http.Conn.pulled_part` |
| `Http.Stream.mode?` | proved | `Http.Conn.respond_opens` |
| `Http.Response.stream` | checked | `Tests/HttpStream.lean` |
| `Http.Response.events` | checked | `Tests/HttpStream.lean` |
| `Http.Response.part` | checked | `Tests/HttpStream.lean` |
| `Http.Response.nothing` | checked | `Tests/HttpStream.lean` |
| `Http.Response.finished` | checked | `Tests/HttpStream.lean` |
| `Http.Response.taken` | checked | `Tests/HttpStream.lean` |

## `Lanes/Web/Http/Waiting.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Waiting.start` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.wait` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.releases` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.release` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.answer` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.drain` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and 3 more |
| `Http.Waiting.Trace.apply` | spec | used only in statements |
| `Http.Waiting.exec` | spec | used only in statements |

## `Lanes/Web/Http/Wire.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.frames` | proved | `Http.Request.fields_framing` |
| `Http.Request.target` | proved | `Http.Request.target_visible`, `SigV4.target_sign` |
| `Http.Request.kept` | proved | through `Http.Request.fields`, `Http.Request.wire` and 1 more: `Http.Request.fields_framing`, `Http.Request.fields_token` and 4 more |
| `Http.Request.fields` | proved | `Http.Request.fields_framing`, `Http.Request.fields_token` |
| `Http.Request.head` | proved | `Http.Request.head_plain` |
| `Http.Request.wire` | proved | `Http.Request.head_plain`, `Http.Request.read_wire`, `Http.Request.read_wire_extract` |
| `Http.Request.headOnly` | proved | `Http.Request.headOnly_plain` |
| `Http.Request.wireHead` | proved | `Http.Request.headOnly_plain` |
| `Http.Reading.map` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.headEnd` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.crlf` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.skip` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.hex` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.chunkSizeDigits_max` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.chunkExtensionBytes_max` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.sizeLineEnd` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.chunkHead` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.dechunk` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.decimal?` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.splitLines` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.statusLine?` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.headerLine?` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.head?` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.framing?` | proved | through `Http.Response.read`, `Http.Response.readHead` and 1 more: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and 13 more |
| `Http.readFrom` | proved | `Http.Response.read_some` |
| `Http.Response.read` | proved | `Http.Conn.read_encode`, `Http.Conn.read_streamed`, `Http.Response.read_append` and 11 more |
| `Http.readHeadFrom` | proved | through `Http.Response.readHead`: `Http.Response.readHead_ended` |
| `Http.Response.readHead` | proved | `Http.Response.readHead_ended` |
| `Http.Response.parse` | trusted | TRUSTED.md: The HTTP wire format |

## `Lanes/Web/Http/WireSpec.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Response.kept` | proved | through `Http.Response.writable`: `Http.Conn.sendable_writable`, `Http.Response.read_wire` and 7 more |
| `Http.Response.lowered` | proved | `Http.Conn.read_encode`, `Http.Conn.read_streamed`, `Http.Response.read_wire` and 3 more |
| `Http.Response.writable` | proved | `Http.Conn.sendable_writable`, `Http.Response.read_wire`, `Http.Response.read_wireAfter` and 6 more |
| `Http.Response.headWire` | proved | through `Http.Response.wire`, `Http.Response.wireAfter` and 2 more: `Http.Response.read_wire`, `Http.Response.read_wireAfter` and 6 more |
| `Http.Response.wire` | proved | `Http.Response.read_wire`, `Http.Response.read_wire_extract` |
| `Http.Response.chunk` | proved | `Http.Conn.pulled_part`, `Http.Conn.read_streamed` |
| `Http.Response.wireChunked` | proved | `Http.Response.read_wireChunked`, `Http.Response.read_wireChunked_extract` |
| `Http.Response.interim` | proved | `Http.Response.read_wireAfter`, `Http.Response.read_wireAfter_extract` |
| `Http.Response.wireAfter` | proved | `Http.Response.read_wireAfter`, `Http.Response.read_wireAfter_extract` |
| `Http.Response.wireToEnd` | proved | `Http.Response.read_wireToEnd`, `Http.Response.read_wireToEnd_open` |

## `Lanes/Web/IO/Client.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Client.Call.authority` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.Call.at` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.outside` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.exchangeExplained` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.exchange` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.fetch` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.events` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.handler` | trusted | TRUSTED.md: The HTTP client adapter's handler |

## `Lanes/Web/IO/Ops.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Ops.new` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.drain` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.journal` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.refused` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.write` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.health` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.page` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.freshId` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.wallMs` | trusted | TRUSTED.md: What the server tells its operators |
| `Http.Ops.front` | trusted | TRUSTED.md: What the server tells its operators |

## `Lanes/Web/IO/S3.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `SigV4.Source.fixed` | trusted | TRUSTED.md: The S3 client's IO |
| `SigV4.instCoeCredentialsSource` | trusted | TRUSTED.md: The S3 client's IO |
| `S3.credentialsFromEnv` | trusted | TRUSTED.md: The S3 client's IO |
| `S3.now` | trusted | TRUSTED.md: The S3 client's IO |
| `S3.exchange` | trusted | TRUSTED.md: The S3 client's IO |
| `S3.upload` | trusted | TRUSTED.md: The S3 client's IO |
| `S3.handler` | trusted | TRUSTED.md: The S3 client's IO |

## `Lanes/Web/IO/Server.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.serveWith` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.serveFronted` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.ServerConfig.journalName` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.serve` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.port` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.stop` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.drain` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.inFlight` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.trace` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.wait` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.stopOnSignal` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.Server.tryInput` | trusted | TRUSTED.md: The HTTP adapter's IO |

## `Lanes/Web/IO/SignIn.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `OAuth.SignIn.start` | trusted | TRUSTED.md: The sign-in's IO |
| `OAuth.SignIn.finish` | trusted | TRUSTED.md: The sign-in's IO |
| `OAuth.SignIn.arrive` | trusted | TRUSTED.md: The sign-in's IO |

## `Lanes/Web/IO/Tls.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Tls.systemFiles` | trusted | TRUSTED.md: The TLS client |
| `Tls.Trust.path` | trusted | TRUSTED.md: The TLS client |
| `Tls.SessionImpl` | trusted | TRUSTED.md: The TLS client |
| `Tls.alpnWire` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.start` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.startChain` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.peer` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.alpn` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.feed` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.take` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.handshake` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.write` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.read` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.closed` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.shutdown` | trusted | TRUSTED.md: The TLS client |
| `Tls.Session.readAll` | trusted | TRUSTED.md: The TLS client |

## `Lanes/Web/S3/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Endpoint.aws` | tested | `Tests/S3.lean` |
| `S3.Key.of?` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Multipart.lean` and 7 more |
| `S3.Range.header` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.PartNumber.of?` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |
| `S3.Manifest.of?` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |
| `S3.Manifest.xml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.method` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.verb` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.segments` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.query` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.headers` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.body` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Bucket.host` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 3 more |
| `S3.Bucket.path` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 3 more |
| `S3.Bucket.scope` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Multipart.lean` and 7 more |
| `S3.call` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.unescapeKey` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.entry?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.page?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.errorCode` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.root?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.started?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.part?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.parts?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.completed` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.info` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.interpret` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean` |
| `S3.Op.modelled` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Post.lean` and 1 more |
| `S3.Answer.modelled` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Post.lean` and 1 more |
| `S3.presign` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and 3 more |
| `S3.presignPart` | tested | `Tests/S3Upload.lean` |

## `Lanes/Web/S3/Multipart.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Multipart.minPart_bytes` | proved | `S3.Multipart.Plan.range_full` |
| `S3.Multipart.maxPart_bytes` | proved | `S3.Multipart.Plan.range_full` |
| `S3.Multipart.maxParts` | proved | `S3.Multipart.Plan.count_le` |
| `S3.Multipart.maxObject_bytes` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |
| `S3.Multipart.Plan.count` | proved | `S3.Multipart.Plan.count_le`, `S3.Multipart.Plan.range_full`, `S3.Multipart.Plan.range_last` and 1 more |
| `S3.Multipart.Plan.range` | proved | `S3.Multipart.Plan.range_full`, `S3.Multipart.Plan.range_last`, `S3.Multipart.Plan.range_next` |
| `S3.Multipart.Plan.of?` | tested | `Tests/S3Upload.lean` |
| `S3.Multipart.Plan.auto` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |
| `S3.Multipart.Flow.next` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.op` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |
| `S3.Multipart.Flow.retry` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.moveTo` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.transient` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.uploaded` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.onComplete` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.onComplete.markLost` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.answer` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.start` | checked | `Tests/Multipart.lean` |
| `S3.Multipart.Flow.bound` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |

## `Lanes/Web/S3/Post.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Post.Condition.json` | proved | through `S3.Post.Condition.holds`, `S3.Post.Document.encode` and 1 more: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and 2 more |
| `S3.Post.field?` | proved | through `S3.Post.decode?`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and 1 more |
| `S3.Post.Condition.read?` | proved | through `S3.Post.decode?`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and 1 more |
| `S3.Post.Document.json` | proved | through `S3.Post.Document.encode`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and 1 more |
| `S3.Post.Document.read?` | proved | through `S3.Post.decode?`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and 1 more |
| `S3.Post.Document.encode` | proved | `S3.Post.decode?_encode` |
| `S3.Post.decode?` | proved | `S3.Post.admitted_bounded`, `S3.Post.decode?_encode`, `S3.Post.form_policy` |
| `S3.Post.signature` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.lookup` | proved | through `S3.Post.Condition.holds`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and 1 more |
| `S3.Post.Condition.holds` | proved | `S3.Post.check_holds` |
| `S3.Post.Condition.field?` | proved | through `S3.Post.check`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and 1 more |
| `S3.Post.exempt` | proved | through `S3.Post.check`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and 1 more |
| `S3.Post.check` | proved | `S3.Post.admitted_bounded`, `S3.Post.check_holds` |
| `S3.Post.KeyRule.condition` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.KeyRule.field` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.maxObject_bytes` | proved | through `S3.Post.Length.max`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.expiration` | proved | `S3.Post.expiration_parse` |
| `S3.Post.credential` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.typed` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.signer` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.eqs` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.conditions` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.document` | proved | `S3.Post.form_policy` |
| `S3.Post.Form.fields` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and 4 more |
| `S3.Bucket.url` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.form` | proved | `S3.Post.admitted_bounded`, `S3.Post.form_policy` |

## `Lanes/Web/S3/PostSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Post.Condition.Small` | spec | a predicate |

## `Lanes/Web/S3/Xml.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Xml.nameChar` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.nameStart` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.isName` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.xmlChar` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.space` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.after` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.skipAttributes` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.hexValue?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.codePoint?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.charRef?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.entity?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.unescape` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.escape` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.tokens` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.push` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.parse` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Xml.lean`, `Tests/S3.lean` |
| `S3.Xml.Node.name` | tested | `Tests/S3.lean` |
| `S3.Xml.Node.children` | tested | `Tests/S3.lean` |
| `S3.Xml.Node.content` | tested | `Tests/S3.lean` |
| `S3.Xml.Node.all` | tested | `Tests/S3.lean` |
| `S3.Xml.Node.child?` | tested | `Tests/S3.lean` |
| `S3.Xml.Node.text?` | tested | `Tests/S3.lean` |

## `Lanes/Web/Transcode.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Transcode.signatureHeader` | tested | `Tests/Testing.lean` |
| `Transcode.Report.status` | tested | `Tests/Testing.lean` |
| `Transcode.signed` | proved | through `Transcode.verify`: `Transcode.verify_iff` |
| `Transcode.signature` | proved | `Transcode.verify_iff` |
| `Transcode.verify` | proved | `Transcode.verify_iff` |
| `Transcode.jobJson` | tested | `Tests/Testing.lean` |
| `Transcode.jobBody` | tested | `Tests/Testing.lean` |
| `Transcode.jobSignature` | tested | `Tests/Testing.lean` |
| `Transcode.jobRequest` | tested | `Tests/Testing.lean` |
| `Transcode.field?` | tested | `Tests/Testing.lean` |
| `Transcode.readJob?` | tested | `Tests/Testing.lean` |
| `Transcode.reportJson` | tested | `Tests/Testing.lean` |
| `Transcode.reportBody` | tested | `Tests/Testing.lean` |
| `Transcode.readReport?` | tested | `Tests/Testing.lean` |
| `Transcode.reportRequest` | tested | `Tests/Testing.lean` |

## `LanesCli/Docstrings.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Docstrings.Kind.label` | none |  |
| `Cli.Docstrings.Kind.all` | none |  |
| `Cli.Docstrings.instances` | none |  |
| `Cli.Docstrings.kindOf` | none |  |
| `Cli.Docstrings.shown` | none |  |
| `Cli.Docstrings.read` | none |  |
| `Cli.Docstrings.ratio` | none |  |
| `Cli.Docstrings.row` | none |  |
| `Cli.Docstrings.table` | none |  |
| `Cli.Docstrings.run` | none |  |

## `LanesCli/Generated.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Generated.instAppendPlan` | none |  |
| `Cli.Generated.lineCount` | none |  |
| `Cli.Generated.readIfExists` | none |  |
| `Cli.Generated.sortStrings` | none |  |
| `Cli.Generated.charsFrom` | none |  |
| `Cli.Generated.occursIn` | tested | `Tests/Lint.lean` |
| `Cli.Generated.replaceName` | tested | `Tests/Lint.lean` |
| `Cli.Generated.writeIfChanged` | none |  |
| `Cli.Generated.stale` | none |  |
| `Cli.Generated.markdownIn` | none |  |
| `Cli.Generated.parseCount` | tested | `Tests/Lint.lean` |
| `Cli.Generated.isTrustedSource` | tested | `Tests/Lint.lean` |
| `Cli.Generated.trustedSizes` | tested | `Tests/Lint.lean` |
| `Cli.Generated.rewriteSizes` | none |  |
| `Cli.Generated.withCommas` | tested | `Tests/Lint.lean` |
| `Cli.Generated.roundedTotal` | tested | `Tests/Lint.lean` |
| `Cli.Generated.rewriteTotal` | none |  |
| `Cli.Generated.countless` | tested | `Tests/Lint.lean` |
| `Cli.Generated.trustedPlan` | none |  |
| `Cli.Generated.decisionsDir` | none |  |
| `Cli.Generated.parseDecisionName` | none |  |
| `Cli.Generated.parseHeading` | none |  |
| `Cli.Generated.readDecisions` | none |  |
| `Cli.Generated.indexLine` | none |  |
| `Cli.Generated.indexText` | none |  |
| `Cli.Generated.textFiles` | none |  |
| `Cli.Generated.numberPlan` | none |  |
| `Cli.Generated.decisionsPlan` | none |  |
| `Cli.Generated.statusDir` | none |  |
| `Cli.Generated.rowsMarker?` | none |  |
| `Cli.Generated.limitsMarker` | none |  |
| `Cli.Generated.generatedNote` | tested | `Tests/Lint.lean` |
| `Cli.Generated.splitFragment` | none |  |
| `Cli.Generated.statusPlan` | none |  |
| `Cli.Generated.plan` | none |  |
| `Cli.Generated.Edit.describe` | none |  |
| `Cli.Generated.apply` | none |  |
| `Cli.Generated.fix` | none |  |

## `LanesCli/Inventory.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Inventory.Status.label` | none |  |
| `Cli.Inventory.Status.all` | none |  |
| `Cli.Inventory.inventoryFile` | none |  |
| `Cli.Inventory.noneFile` | none |  |
| `Cli.Inventory.sortStrings` | none |  |
| `Cli.Inventory.moduleOfPath` | none |  |
| `Cli.Inventory.pathOfModule` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.modulesIn` | none |  |
| `Cli.Inventory.imports` | none |  |
| `Cli.Inventory.gates` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.trustedRows` | none |  |
| `Cli.Inventory.owner` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.shapeOf` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.specTypes` | none |  |
| `Cli.Inventory.reportTypes` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.libraryRoots` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isLibrary` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.ranges` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.inDeriving` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.generatedParsers` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.ofTheorem` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.readFacts` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isProp` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isType` | none |  |
| `Cli.Inventory.usersOf` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.specs` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.covers` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.statement` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.provedBy` | tested | `Tests/Inventory.lean` |
| `Cli.Inventory.isOutside` | none |  |
| `Cli.Inventory.reach` | none |  |
| `Cli.Inventory.exercised` | none |  |
| `Cli.Inventory.display` | none |  |
| `Cli.Inventory.listOf` | none |  |
| `Cli.Inventory.entries` | none |  |
| `Cli.Inventory.area` | none |  |
| `Cli.Inventory.cell` | none |  |
| `Cli.Inventory.summary` | none |  |
| `Cli.Inventory.render` | none |  |
| `Cli.Inventory.allowed` | none |  |
| `Cli.Inventory.check` | none |  |
| `Cli.Inventory.load` | none |  |
| `Cli.Inventory.counts` | none |  |
| `Cli.Inventory.run` | none |  |

## `LanesCli/Lint.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Lint.stripCommentsAndStrings` | tested | `Tests/Lint.lean` |
| `Cli.Lint.isWordChar` | tested | `Tests/Lint.lean` |
| `Cli.Lint.hasWord` | tested | `Tests/Lint.lean` |
| `Cli.Lint.trustedWords` | tested | `Tests/Lint.lean` |
| `Cli.Lint.proofDirs` | tested | `Tests/Lint.lean` |
| `Cli.Lint.isProofFile` | tested | `Tests/Lint.lean` |
| `Cli.Lint.importsProofModule` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkFile` | tested | `Tests/Lint.lean` |
| `Cli.Lint.sourceFiles` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkC` | tested | `Tests/Lint.lean` |
| `Cli.Lint.codeSpans` | tested | `Tests/Lint.lean` |
| `Cli.Lint.firstBraces` | tested | `Tests/Lint.lean` |
| `Cli.Lint.expandBraces` | tested | `Tests/Lint.lean` |
| `Cli.Lint.citedPaths` | tested | `Tests/Lint.lean` |
| `Cli.Lint.citingDocs` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkLinks` | tested | `Tests/Lint.lean` |
| `Cli.Lint.cells` | tested | `Tests/Lint.lean` |
| `Cli.Lint.tableRows` | tested | `Tests/Lint.lean` |
| `Cli.Lint.spans` | tested | `Tests/Lint.lean` |
| `Cli.Lint.inScope` | tested | `Tests/Lint.lean` |
| `Cli.Lint.checkOracles` | tested | `Tests/Lint.lean` |
| `Cli.Lint.parseFinding` | tested | `Tests/Lint.lean` |
| `Cli.Lint.inventory` | tested | `Tests/Lint.lean` |
| `Cli.Lint.lint` | tested | `Tests/Lint.lean` |
| `Cli.Lint.run` | none |  |

## `LanesCli/Main.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `usage` | none |  |
| `flag?` | none |  |
| `main` | none |  |

## `LanesCli/New.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.New.Source.toToml` | tested | `Tests/New.lean` |
| `Cli.New.moduleName` | tested | `Tests/New.lean` |
| `Cli.New.validName` | none |  |
| `Cli.New.files` | tested | `Tests/New.lean` |
| `Cli.New.fill` | tested | `Tests/New.lean` |
| `Cli.New.run` | none |  |
