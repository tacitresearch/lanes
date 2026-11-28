# Inventory

Every public definition of `Lanes` and `LanesCli`, with its status and the evidence for it.
Generated from the built modules by `lake exe lanes lint --fix` (`LanesCli/Inventory.lean`);
do not edit. What each status means, and what is not listed, is in
`docs/decisions/D47-the-inventory-is-computed.md`. The definitions of `Lanes/` with status
none are on `docs/inventory-none.md`, which only shrinks. `lake exe lanes stats` counts
them by area.

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
| `Jobs.Config.slots` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.Config.cap` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.Config.backoff` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.keys` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.attach_active_leaves` |
| `Jobs.entry` | proved | `Jobs.answer_of_leaves`, `Jobs.entry_step`, `Jobs.not_arms` and others |
| `Jobs.put` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.remove` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.Within` | spec | a predicate |
| `Jobs.Attempts` | spec | a predicate |
| `Jobs.sig` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.actor_attempts` and others |
| `Jobs.timer` | proved | `Jobs.not_arms` |
| `Jobs.fail` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.step` | proved | `Jobs.answer_of_leaves`, `Jobs.dispatch_active`, `Jobs.entry_step` and others |
| `Jobs.rearm` | proved | through `Jobs.actor`, `Jobs.attach` and others: `Jobs.active_answered`, `Jobs.active_leaves` and others |
| `Jobs.actor` | proved | `Jobs.actor_attempts`, `Jobs.actor_within` |
| `Jobs.system` | proved | `Jobs.active_answered`, `Jobs.active_leaves`, `Jobs.answered_le_handled` and others |
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
| `Check.sameSet` | proved | through `Check.OnceState.equiv`: `Check.OnceMonitor.withinFrom_eq` |
| `Check.setHash` | checked | `Tests/KV.lean` |
| `Check.OnceState.equiv` | proved | `Check.OnceMonitor.withinFrom_eq` |
| `Check.OnceState.take` | checked | `Tests/KV.lean` |
| `Check.OnceState.hash` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.insertAll` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.expand` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.close` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.ok` | checked | `Tests/KV.lean` |
| `Check.OnceMonitor.withinFrom` | proved | `Check.OnceMonitor.withinFrom_eq` |
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
| `Schedule.Config.cap` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.Config.backoff` | proved | `Schedule.retry_waits` |
| `Schedule.Config.wait` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.keys` | proved | `Schedule.attach_held_leaves`, `Schedule.every_noticed`, `Schedule.held_leaves` |
| `Schedule.entry` | proved | `Schedule.attach_answer_handled`, `Schedule.attach_end_handled`, `Schedule.attach_held_leaves` and others |
| `Schedule.put` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.remove` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.set` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.sig` | proved | `Schedule.actor_attempts`, `Schedule.actor_within`, `Schedule.armed` and others |
| `Schedule.timer` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.fail` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.over` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.run` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.answerOf` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.onJob` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.touch` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.enroll` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.step` | proved | `Schedule.attempt_ends`, `Schedule.dispatch_due`, `Schedule.leaves_answered` and others |
| `Schedule.rearm` | proved | through `Schedule.actor`, `Schedule.attach` and others: `Schedule.actor_attempts`, `Schedule.actor_within` and others |
| `Schedule.actor` | proved | `Schedule.actor_attempts`, `Schedule.actor_within` |
| `Schedule.system` | proved | `Schedule.armed`, `Schedule.attempts`, `Schedule.calls_le_scheduled` and others |
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
| `Check.Fingerprint.Search.add` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and others: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.start` | proved | `Check.fingerprint_tasks` |
| `Check.Fingerprint.Search.successors` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and others: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.visit` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and others: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.expandWith` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and others: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.expand` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and others: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.advance` | proved | through `Check.Fingerprint.Search.run`, `Check.Fingerprint.Search.runParallel` and others: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.run` | proved | `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_tasks` |
| `Check.Fingerprint.Search.batchSize` | proved | through `Check.Fingerprint.Search.runParallel`, `Check.fingerprint`: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.expandInTasks` | proved | through `Check.Fingerprint.Search.runParallel`, `Check.fingerprint`: `Check.Fingerprint.Search.runParallel_eq`, `Check.fingerprint_deadlock` and others |
| `Check.Fingerprint.Search.runParallel` | proved | `Check.Fingerprint.Search.runParallel_eq` |
| `Check.Fingerprint.Search.choicesTo` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and others |
| `Check.Fingerprint.replaySteps` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and others |
| `Check.Fingerprint.replay` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and others |
| `Check.Fingerprint.recheck` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and others |
| `Check.Fingerprint.Found.record` | proved | through `Check.fingerprint`: `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted` and others |
| `Check.Fingerprint.Search.report` | proved | `Check.fingerprint_tasks` |
| `Check.fingerprint` | proved | `Check.fingerprint_deadlock`, `Check.fingerprint_fingerprinted`, `Check.fingerprint_tasks` and others |

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
| `Check.Monitor.insertAll` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.expand` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.freshFrom` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.closeStep` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.rounds` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.close` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.ok` | proved | `Check.Monitor.ok_iff`, `Check.refines_sound` |
| `Check.Monitor.withinFrom` | proved | `Check.Monitor.withinFrom_eq` |
| `Check.Monitor.instBEq` | proved | `Check.Monitor.beq_iff_abs_eq`, `Check.refines_sound`, `Check.refines_traces` and others |
| `Check.Monitor.instHashable` | proved | `Check.refines_sound`, `Check.refines_traces` |
| `Check.Monitor.start` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.input` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.output` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Check.Monitor.fire` | proved | through `Check.Monitor.after`, `Service.monitored`: `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
| `Service.monitored` | proved | `Check.refines_sound`, `Check.refines_traces`, `Service.monitored_respects` |
| `Check.refines` | proved | `Check.refines_sound`, `Check.refines_traces` |

## `Lanes/Check/MonitorEquiv.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Monitor.Within` | spec | a predicate |

## `Lanes/Check/Reduce.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Model.reduce` | proved | `Check.Model.Reduction.of_reduced`, `Check.Model.Reduction.reachable`, `Check.search_reduce_deadlock` and others |
| `Check.systemReduced` | proved | `Check.systemReduced_sound` |

## `Lanes/Check/ReduceSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.World.SameUpTo` | spec | a predicate |

## `Lanes/Check/Search.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Check.Property.name` | proved | `Check.search_unreached` |
| `Check.Property.holds` | proved | `Check.World.Reduction.ofDriver`, `Check.refines_sound`, `Check.refines_traces` and others |
| `Check.Trace.last` | proved | `Check.fingerprint_deadlock`, `Check.fingerprint_violated`, `Check.fingerprint_witness` and others |
| `Check.Trace.labels` | proved | `Check.systemFingerprinted_violated`, `Check.system_violated` |
| `Check.Verdict.exitCode` | checked | `Tests/Testing.lean` |
| `Check.Report.verdict` | proved | through `Check.Report.ok`: `Check.Report.ok_iff` |
| `Check.Report.ok` | proved | `Check.Report.ok_iff` |
| `Check.Report.passed` | checked | `Tests/Election.lean`, `Tests/Engine.lean`, `Tests/Fronted.lean` and others |
| `Check.Path.last` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Path.toTraceAux` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Path.toTrace` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.violation` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.witnessFor` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.witness` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.unwitnessed` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and others |
| `Check.Hashed.of` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Hashed.instBEq` | proved | through `Check.Search`, `Check.search`: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Hashed.instHashable` | proved | through `Check.Search`, `Check.search`: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.add` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.contains` | checked | `Tests/Join.lean` |
| `Check.Search.addInit` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and others |
| `Check.Search.start` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and others |
| `Check.Search.visit` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.successors` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.expandWith` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.expand` | proved | through `Check.Search.run`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.run` | proved | `Check.Search.explore_eq`, `Check.Search.runBatches_eq` |
| `Check.Search.expandAll` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.mapInTasks` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.taskSize` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.batchSize` | proved | through `Check.Search.explore`, `Check.Search.runBatches` and others: `Check.Search.explore_eq`, `Check.Search.runBatches_eq` and others |
| `Check.Search.runBatches` | proved | `Check.Search.runBatches_eq` |
| `Check.Search.explore` | proved | `Check.Search.explore_eq` |
| `Check.Search.report` | proved | through `Check.search`: `Check.search_deadlock`, `Check.search_deadlock_free` and others |
| `Check.search` | proved | `Check.search_deadlock`, `Check.search_deadlock_free`, `Check.search_reached` and others |

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
| `Check.Node.tagged` | proved | through `Check.Node.trafficHash`, `Check.system` and others: `Check.Node.trafficHash_eq`, `Check.refines_sound` and others |
| `Check.Node.trafficHash` | proved | `Check.Node.trafficHash_eq` |
| `Check.instHashableNodeOfInspect` | proved | through `Check.system`, `Check.systemFingerprinted`: `Check.refines_sound`, `Check.refines_traces` and others |
| `Check.Trace.map` | proved | through `Check.system`, `Check.systemFingerprinted`: `Check.refines_sound`, `Check.refines_traces` and others |
| `Check.Report.map` | proved | through `Check.system`, `Check.systemFingerprinted`: `Check.refines_sound`, `Check.refines_traces` and others |
| `Check.model` | proved | `Scenario.reachable_iff` |
| `Check.system` | proved | `Check.refines_sound`, `Check.refines_traces`, `Check.system_sound` and others |
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
| `joinSig` | proved | `Jobs.attach_active_leaves`, `Jobs.attach_within`, `Obligation.Due.of_thinRight` and others |
| `Wiring.left` | proved | through `Schedule.attach`, `SysState.over` and others: `Obligation.Due.of_thinRight`, `Schedule.attach_answer_handled` and others |
| `Wiring.right` | proved | through `Schedule.attach`, `System.join` and others: `Obligation.Due.of_thinRight`, `Schedule.attach_answer_handled` and others |
| `System.join` | proved | `Obligation.Due.of_thinRight`, `SysState.deliverable_of_thinRight`, `SysState.exists_block` and others |
| `Signature.withIO` | proved | `SysState.run_filterMapIO`, `System.Invariant.filterMapIO`, `System.LeadsTo.filterMapIO` and others |
| `Effect.filterMapOut` | proved | through `SysState.over`, `System.filterMapIO` and others: `SysState.run_filterMapIO`, `System.Invariant.filterMapIO` and others |
| `System.filterMapIO` | proved | `SysState.run_filterMapIO`, `System.Invariant.filterMapIO`, `System.LeadsTo.filterMapIO` and others |
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
| `Effect.sends` | proved | `Account.Fires.grow`, `Account.Fires.handle`, `Account.Moves.grow` and others |
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
| `Driver.anyOrder` | checked | `Tests/Bank.lean`, `Tests/Batch.lean`, `Tests/Clients.lean` and others |
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
| `Effect.isStop` | proved | `Schedule.attach_answer_handled`, `Schedule.attach_end_handled`, `SysState.mem_net_of_step` and others |
| `Effect.instDecidableEq` | proved | its type, `Decidable` |
| `Envelope.instDecidableEq` | proved | `Account.Fires.handle`, `Account.Moves.handle`, `Account.implements` and others |
| `Envelope.sameLink` | proved | through `SysState.nextOnLink`: `SysState.nextOnLink_spec` |
| `Link.reliable` | proved | through `EnvModel.link`, `EnvModel.lossy` and others: `Account.implements`, `Account.implements_timed` and others |
| `Link.network` | checked | `Tests/Bank.lean`, `Tests/Election.lean`, `Tests/Join.lean` and others |
| `Link.unordered` | checked | `Tests/Election.lean`, `Tests/Jobs.lean`, `Tests/Outside.lean` and others |
| `EnvModel.reliable` | spec | used only in statements |
| `EnvModel.distributed` | none |  |

## `Lanes/Core/World.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `update` | proved | through `SysState.down`, `SysState.handle` and others: `Account.implements`, `Account.implements_timed` and others |
| `Event.timed` | proved | `Account.implements`, `Account.implements_timed`, `Check.refines_traces` and others |
| `Event.visible` | spec | used only in statements |
| `SysState.blank` | proved | `System.Inductive.of_monotone`, `System.Monotone.and`, `System.Monotone.and_net` |
| `SysState.hasMail` | proved | `SysState.hasMail_of_thinRight` |
| `SysState.perform` | proved | through `SysState.handle`, `SysState.init` and others: `Account.implements`, `Account.implements_timed` and others |
| `SysState.performAll` | proved | through `SysState.handle`, `SysState.init` and others: `Account.implements`, `Account.implements_timed` and others |
| `SysState.down` | proved | `Account.implements`, `Account.implements_timed`, `System.Refines.of_events` and others |
| `SysState.settle` | proved | `SysState.Loses.settle` |
| `SysState.handle` | proved | `Http.fronted_handle_arrive`, `Http.served_handle_arrive` |
| `SysState.startActor` | proved | through `SysState.init`, `SysState.run` and others: `Account.implements`, `Account.implements_timed` and others |
| `SysState.deliverable` | proved | `Account.implements`, `Account.implements_timed`, `SysState.deliverable_of_thinRight` and others |
| `SysState.step` | proved | `Http.Gate.answered_of_leaves`, `Http.Gate.deadline_not_restarted`, `Outside.Beside.keeps` and others |
| `SysState.init` | proved | `Account.implements`, `Account.implements_timed`, `Check.systemFingerprinted_violated` and others |
| `SysState.run` | proved | `Check.systemFingerprinted_violated`, `Check.system_violated`, `Http.Gate.answered_le_handled` and others |
| `System.Invariant` | spec | a predicate |

## `Lanes/Data/Body.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Codec.Error.Step.text` | tested | `Tests/Body.lean`, `Tests/Match.lean` |
| `Codec.Error.Problem.text` | tested | `Tests/Body.lean`, `Tests/Match.lean` |
| `Codec.Error.Problem.atByte` | tested | `Tests/Body.lean`, `Tests/Match.lean` |
| `Codec.Error.pathText` | tested | `Tests/Body.lean`, `Tests/Match.lean` |
| `Codec.Error.instToString` | tested | `Tests/Body.lean`, `Tests/Match.lean` |
| `Body.fail` | proved | through `Body.encode`, `Body.write` and others: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.within` | proved | through `Body.encode`, `Body.write` and others: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.writeNat` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.natBytes` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.zigzag` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.unzigzag` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.writeNum` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.writeBlob` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.writeCount` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.readNatFrom` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.readNat` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.readBlob` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.readCount` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.consumes` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.consumesFields` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.Tag.nat` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.Tag.int` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.Tag.string` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.Tag.bytes` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.Tag.list` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.Tag.ctor` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.writeAt` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.writeFields` | spec | used only in statements |
| `Body.writeItems` | spec | used only in statements |
| `Body.writeEntries` | spec | used only in statements |
| `Body.writeTagged` | proved | through `Body.encode`, `Body.write`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Body.writeTaggedItems` | spec | used only in statements |
| `Body.readAt` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.readFields` | spec | used only in statements |
| `Body.readItems` | spec | used only in statements |
| `Body.readEntries` | spec | used only in statements |
| `Body.readTagged` | proved | through `Body.decode`, `Body.read`: `Body.decode_encode`, `Body.encode_decode` and others |
| `Body.readTaggedItems` | spec | used only in statements |
| `Body.write` | proved | `Body.encode_decode`, `Body.read_eq_ok_iff` |
| `Body.read` | proved | `Body.read_eq_ok_iff` |
| `Body.encode` | proved | `Body.decodeWith_encode_self`, `Body.decodeWith_migrate`, `Body.decode_encode` |
| `Body.decode` | proved | `Body.decode_encode`, `Body.encode_decode` |

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
| `Codec.withSchema` | proved | its type, `Codec` |
| `Codec.bool` | proved | its type, `Codec` |
| `Codec.fin` | proved | its type, `Codec` |
| `Codec.int` | proved | its type, `Codec` |
| `Codec.sum` | proved | its type, `Codec` |
| `Codec.option` | proved | its type, `Codec` |
| `Codec.padded` | proved | its type, `Codec` |
| `Codec.hasAtLeast` | tested | `Tests/Body.lean`, `Tests/Codec.lean`, `Tests/Durable.lean` and others |
| `Codec.readMany` | tested | `Tests/Body.lean`, `Tests/Codec.lean`, `Tests/Durable.lean` and others |
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
| `Codec.fieldTuple` | none |  |
| `Codec.product` | none |  |
| `Codec.inject` | none |  |
| `Codec.injectCtor` | none |  |
| `Codec.nameLit` | none |  |
| `Codec.typeName` | none |  |
| `Codec.fieldsTerm` | none |  |
| `Codec.structTerm` | none |  |
| `Codec.sumBytes` | none |  |
| `Codec.sumTerm` | none |  |

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
| `Declare.constantDefaults` | none |  |
| `Declare.ctorArgs` | none |  |
| `Declare.ctorBinder` | none |  |

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

## `Lanes/Data/Match.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Schema.Plan.claim` | proved | through `Schema.Plan.apply`, `Schema.Plan.of`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Schema.Plan.clash` | proved | through `Schema.Plan.apply`, `Schema.Plan.of`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Schema.Plan.unambiguous` | proved | through `Schema.Plan.apply`, `Schema.Plan.of`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Schema.Plan.pick` | proved | through `Schema.Plan.apply`, `Schema.Plan.of`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Schema.Plan.of` | proved | `Body.decodeWith_encode_self`, `Body.decodeWith_migrate`, `Schema.Plan.of_insertIdx` and others |
| `Schema.Plan.ofFields` | proved | through `Schema.Plan.apply`, `Schema.Plan.of`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Schema.Plan.ofCtors` | proved | through `Schema.Plan.apply`, `Schema.Plan.of`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Schema.Plan.apply` | proved | `Schema.Plan.of_insertIdx`, `Schema.Plan.of_rename` |
| `Schema.Plan.applyItems` | spec | used only in statements |
| `Schema.Plan.applyEntries` | spec | used only in statements |
| `Schema.Plan.applyFields` | spec | used only in statements |
| `Schema.Plan.applyCtor` | spec | used only in statements |
| `Schema.Migration.of` | proved | `Body.decodeWith_migrate` |
| `Body.readWith` | proved | through `Body.decodeWith`: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` |
| `Body.decodeWith` | proved | `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` |

## `Lanes/Data/MatchSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Schema.Plan.Known` | spec | a predicate |
| `Schema.Plan.knownPlan` | spec | used only in statements |
| `Schema.Plan.knownValue` | spec | used only in statements |

## `Lanes/Data/Quorum.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Quorum.isMajority` | proved | `Quorum.majority_inter` |

## `Lanes/Data/Schema.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Value.beq` | proved | through `Body.encode`, `Schema` and others: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `Value.beqAll` | proved | through `Body.encode`, `Schema` and others: `Body.decodeWith_encode_self`, `Body.decodeWith_migrate` and others |
| `instBEqValue` | tested | `Tests/Body.lean`, `Tests/Schema.lean` |
| `Schema.beq` | tested | `Tests/Schema.lean` |
| `Schema.beqAll` | tested | `Tests/Schema.lean` |
| `Schema.beqFields` | tested | `Tests/Schema.lean` |
| `Schema.beqCtors` | tested | `Tests/Schema.lean` |
| `instBEqSchema` | tested | `Tests/Schema.lean` |
| `Schema.Fields.nil` | proved | its type, `Schema.Fields` |
| `Schema.Fields.cons` | proved | its type, `Schema.Fields` |
| `Schema.Ctors.nil` | proved | its type, `Schema.Ctors` |
| `Schema.Ctors.cons` | proved | its type, `Schema.Ctors` |
| `Schema.Of.nat` | proved | its type, `Schema.Of` |
| `Schema.Of.int` | proved | its type, `Schema.Of` |
| `Schema.Of.string` | proved | its type, `Schema.Of` |
| `Schema.Of.bytes` | proved | its type, `Schema.Of` |
| `Schema.Of.unit` | proved | its type, `Schema.Of` |
| `Schema.Of.map` | proved | its type, `Schema.Of` |
| `Schema.Of.record` | proved | its type, `Schema.Of` |
| `Schema.Of.variants` | proved | its type, `Schema.Of` |
| `Schema.Of.list` | proved | its type, `Schema.Of` |
| `Schema.Of.bool` | proved | its type, `Schema.Of` |
| `Schema.Of.pair` | proved | its type, `Schema.Of` |
| `Schema.Of.sum` | proved | its type, `Schema.Of` |
| `Schema.Of.option` | proved | its type, `Schema.Of` |
| `Schema.Of.sigma` | proved | its type, `Schema.Of` |
| `Schema.paren` | tested | `Tests/Schema.lean` |
| `Schema.name` | tested | `Tests/Schema.lean` |
| `Schema.names` | tested | `Tests/Schema.lean` |
| `Schema.named` | tested | `Tests/Schema.lean` |
| `Schema.namedAll` | tested | `Tests/Schema.lean` |
| `Schema.namedFields` | tested | `Tests/Schema.lean` |
| `Schema.namedCtors` | tested | `Tests/Schema.lean` |
| `Schema.argument` | tested | `Tests/Schema.lean` |
| `Schema.display` | tested | `Tests/Schema.lean` |
| `Schema.displayFields` | tested | `Tests/Schema.lean` |
| `Schema.displayArgs` | tested | `Tests/Schema.lean` |
| `Schema.displayCtor` | tested | `Tests/Schema.lean` |
| `Schema.was` | tested | `Tests/Schema.lean` |
| `Schema.Field.text` | tested | `Tests/Schema.lean` |
| `Schema.declaration` | tested | `Tests/Schema.lean` |
| `Schema.text` | tested | `Tests/Schema.lean` |

## `Lanes/Durable/Disk.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Disk.apply` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.save`, `Journal.Disk.Torn.mend` and others |
| `Journal.Disk.crash` | proved | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash` and others |
| `Journal.Disk.Found.index` | proved | `Journal.Disk.Torn.read` |
| `Journal.Disk.read` | proved | `Journal.Disk.Torn.mend`, `Journal.Disk.Torn.mend_crash`, `Journal.Disk.Torn.read` and others |
| `Journal.Disk.start` | proved | `Journal.Disk.read_of_start`, `Journal.Disk.start_foreign` |
| `Journal.Disk.mend` | proved | `Journal.Disk.Torn.mend`, `Journal.Disk.Torn.mend_crash` |
| `Journal.Disk.load` | proved | `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Torn.load` and others |
| `Journal.appendWrites` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` |
| `Journal.saveWrites` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` and others |
| `Journal.memo` | spec | used only in statements |
| `Journal.Disk.Holds` | spec | a predicate |
| `Journal.Disk.Torn` | spec | a predicate |

## `Lanes/Durable/Frame.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Frame.fits` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` and others |
| `Frame.checksum` | proved | `Frame.decode_checksum_ne` |
| `Frame.stamped` | proved | `Frame.decode_checksum_ne` |
| `Frame.one` | proved | through `Frame.encode`: `Frame.decode_checksum_ne`, `Frame.decode_encode` and others |
| `Frame.encode` | proved | `Frame.decode_checksum_ne`, `Frame.decode_encode`, `Frame.decode_take` and others |
| `Frame.decode` | proved | `Frame.decode_checksum_ne`, `Frame.decode_encode`, `Frame.decode_extract_prefix` and others |
| `Frame.whole` | proved | `Frame.decode_take_eq`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and others |
| `Frame.span` | proved | `Journal.open?_cut`, `Parcel.receive_send` |
| `Frame.unfinished` | none |  |

## `Lanes/Durable/IO/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.fsync` | trusted | TRUSTED.md: The journal's files |
| `Journal.Store.open` | trusted | TRUSTED.md: The journal's files |
| `Journal.Store.restore` | trusted | TRUSTED.md: The journal's files |

## `Lanes/Durable/IO/Ship.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Ship.Shipper.tell` | trusted | TRUSTED.md: The journal's shipper |
| `Journal.Ship.Shipper.start` | trusted | TRUSTED.md: The journal's shipper |
| `Journal.Ship.Shipper.close` | trusted | TRUSTED.md: The journal's shipper |
| `Journal.Ship.Shipper.counts` | trusted | TRUSTED.md: The journal's shipper |

## `Lanes/Durable/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Entry.codec` | proved | its type, `Codec` |
| `Journal.Entry.bytes` | proved | through `Journal.Entry.fits`, `Journal.encode`: `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash` and others |
| `Journal.Entry.ofBytes` | proved | through `Journal.open?`: `Journal.Disk.open?_of_read`, `Journal.open?_cut` and others |
| `Journal.Entry.fits` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and others |
| `Journal.write` | proved | `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.load_cut` and others |
| `Journal.read` | proved | through `Journal.open?`: `Journal.Disk.open?_of_read`, `Journal.open?_cut` and others |
| `Journal.encode` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save_crash` |
| `Journal.header` | proved | `Journal.Disk.load_cut`, `Journal.Disk.start_foreign`, `Journal.Disk.torn_nil` and others |
| `Journal.label` | proved | `Journal.label_zero` |
| `Journal.named?` | proved | `Journal.Disk.start_foreign` |
| `Journal.file` | proved | `Journal.Disk.load_cut`, `Journal.Restore.piece?_file`, `Journal.open?_cut` and others |
| `Journal.open?` | proved | `Journal.Disk.open?_of_read`, `Journal.open?_cut`, `Journal.open?_file` |
| `Journal.Entry.op?` | proved | through `Batch.flush`, `Batch.grown` and others: `Batch.flush_save`, `Batch.grown_eq` and others |
| `Journal.Entry.marks` | proved | `Journal.recoverIds_handed`, `Journal.recover_handed` |
| `Journal.ops` | proved | `Journal.recover_handed`, `Journal.recover_kernel`, `Journal.recover_outputs` and others |
| `Journal.replay1` | proved | through `Journal.Begun.toFound`, `Journal.Restore.saved` and others: `Journal.Begun.resume_upgraded`, `Journal.Disk.Holds.load_append_crash` and others |
| `Journal.recover` | proved | `Journal.Disk.load_cut`, `Journal.Restore.journal_restores`, `Journal.Upgrade.begin_crash` and others |
| `Journal.replay` | proved | `Journal.Disk.Holds.load_append_crash`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and others |
| `Journal.Entry.savedAt` | proved | `Journal.Disk.Holds.append`, `Journal.Disk.Holds.append_crash`, `Journal.Disk.Holds.load_append_crash` and others |
| `Journal.since` | proved | through `Journal.Begun.load`, `Journal.Begun.toFound` and others: `Journal.Begun.resume_upgraded`, `Journal.Upgrade.begin_crash` and others |
| `Journal.resume` | proved | `Journal.Begun.resume_upgraded`, `Journal.resumeIds_erase`, `Journal.resume_eq_recover` and others |
| `Journal.turn` | proved | `Journal.turn_placed` |
| `Journal.turnAll` | proved | `Journal.turnAll_eq_exec`, `Journal.turnAll_placed`, `Journal.turnAll_spread` |
| `Journal.turns` | spec | used only in statements |

## `Lanes/Durable/Migration.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Migration.cell` | proved | `Migration.cell_kernel` |
| `Migration.envelope` | proved | through `Migration.kernel`: `Journal.Upgrade.begin_crash`, `Journal.Upgrade.inv_load` and others |
| `Migration.image` | proved | through `Migration.kernel`: `Journal.Upgrade.begin_crash`, `Journal.Upgrade.inv_load` and others |
| `Migration.kernel` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.inv_load`, `Migration.cell_kernel` and others |

## `Lanes/Durable/OutputId.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Origin.before` | spec | used only in statements |
| `Journal.OutputId.key` | checked | `Tests/HttpClient.lean` |
| `Journal.journalId` | tested | `Tests/Durable.lean` |
| `Journal.tag` | proved | `Journal.turnAll_placed`, `Journal.turn_placed` |
| `Journal.apply?` | proved | through `Journal.ids`, `Journal.placed` and others: `Batch.run_ids`, `Journal.Restore.journal_restores` and others |
| `Journal.steps` | spec | used only in statements |
| `Journal.placed` | spec | used only in statements |
| `Journal.replayIds1` | proved | through `Journal.recoverIds`, `Journal.resumeIds`: `Journal.Restore.journal_restores`, `Journal.Restore.journal_resumeIds` and others |
| `Journal.ids` | spec | used only in statements |
| `Journal.recoverIds` | proved | `Journal.Restore.journal_resumeIds`, `Journal.recoverIds_erase`, `Journal.recoverIds_handed` and others |
| `Journal.resumeIds` | proved | `Journal.Restore.journal_restores`, `Journal.Restore.journal_resumeIds`, `Journal.resumeIds_eq_recoverIds` and others |
| `Journal.erase` | spec | used only in statements |

## `Lanes/Durable/Reading.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Reading.OfJournal` | spec | a predicate |
| `Journal.Reading.OfSnapshot` | spec | a predicate |
| `Journal.Disk.ofReadings` | proved | `Journal.Disk.Torn.load_readings`, `Journal.Disk.ofReadings_eq` |

## `Lanes/Durable/Restore.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Restore.Object.parse?` | tested | `Tests/Ship.lean` |
| `Journal.Restore.listed?` | tested | `Tests/Ship.lean` |
| `Journal.Restore.newest` | tested | `Tests/Ship.lean` |
| `Journal.Restore.best` | tested | `Tests/Ship.lean` |
| `Journal.Restore.chain` | tested | `Tests/Ship.lean` |
| `Journal.Restore.plan` | tested | `Tests/Ship.lean` |
| `Journal.Restore.piece?` | proved | `Journal.Restore.piece?_file` |
| `Journal.Restore.stitch` | proved | `Journal.Restore.stitch_slice` |
| `Journal.Restore.journal` | proved | `Journal.Restore.journal_restores`, `Journal.Restore.journal_resumeIds` |
| `Journal.Restore.saved` | spec | used only in statements |

## `Lanes/Durable/Ship.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Ship.digits` | tested | `Tests/Ship.lean` |
| `Journal.Ship.sum` | tested | `Tests/Ship.lean` |
| `Journal.Ship.Upload.object` | tested | `Tests/Ship.lean` |
| `Journal.Ship.snapshotOf?` | proved | `Journal.Ship.snapshotOf?_saveWrites` |
| `Journal.Ship.start` | proved | `Journal.Ship.Holds.start` |
| `Journal.Ship.shed` | proved | through `Journal.Ship.step`, `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.step` and others |
| `Journal.Ship.enqueue` | proved | through `Journal.Ship.step`, `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.step` and others |
| `Journal.Ship.Upload.isSnapshot` | proved | through `Journal.Ship.step`: `Journal.Ship.Holds.step` |
| `Journal.Ship.supersede` | proved | through `Journal.Ship.step`: `Journal.Ship.Holds.step` |
| `Journal.Ship.sealWaiting` | proved | through `Journal.Ship.step`, `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.step` and others |
| `Journal.Ship.wrote` | proved | through `Journal.Ship.step`: `Journal.Ship.Holds.step` |
| `Journal.Ship.backoff` | proved | through `Journal.Ship.step`: `Journal.Ship.Holds.step` |
| `Journal.Ship.answer` | proved | through `Journal.Ship.step`: `Journal.Ship.Holds.step` |
| `Journal.Ship.step` | proved | `Journal.Ship.Holds.step` |
| `Journal.Ship.soonest` | proved | through `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.take` |
| `Journal.Ship.sealAt` | proved | through `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.take` |
| `Journal.Ship.ripen` | proved | through `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.take` |
| `Journal.Ship.choose` | proved | through `Journal.Ship.take`: `Journal.Ship.Holds.put`, `Journal.Ship.Holds.take` |
| `Journal.Ship.take` | proved | `Journal.Ship.Holds.put`, `Journal.Ship.Holds.take` |
| `Journal.Ship.State.idle` | tested | `Tests/Ship.lean` |
| `Journal.Ship.Slice` | spec | a predicate |

## `Lanes/Durable/Snapshot.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.Due.codec` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.cell` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.envelope` | proved | its type, `Codec` |
| `Kernel.Image.Codecs.image` | proved | its type, `Codec` |
| `Journal.savedHeader` | proved | `Journal.savedHeader_inj` |
| `Journal.savedRecords` | proved | `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save`, `Journal.Disk.Holds.save_crash` and others |
| `Journal.saved` | proved | `Journal.Ship.snapshotOf?_saveWrites`, `Journal.saved?_other`, `Journal.saved?_saved` |
| `Journal.saved?` | proved | `Journal.saved?_other`, `Journal.saved?_saved` |

## `Lanes/Durable/Upgrade.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Journal.Upgrade.reads` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn` |
| `Journal.Upgrade.writes` | proved | `Journal.Upgrade.holds` |
| `Journal.Upgrade.upgraded` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn`, `Journal.Upgrade.start_torn` |
| `Journal.Upgrade.start` | proved | `Journal.Upgrade.start_torn` |
| `Journal.Disk.begin` | proved | `Journal.Upgrade.begin_crash`, `Journal.Upgrade.begin_torn` |
| `Journal.Upgrade.owed` | tested | `Tests/Durable.lean` |
| `Journal.Upgrade.label` | proved | `Journal.Upgrade.label_snd` |
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

## `Lanes/Lib/Crypto/Native.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Sha256.hash` | trusted | TRUSTED.md: The C |
| `hmac` | trusted | TRUSTED.md: The C |
| `Bytes.same` | proved of its reference, C trusted | `Bytes.same_iff`; the C: TRUSTED.md: The C |
| `randomBytes` | trusted | TRUSTED.md: The C |
| `Argon2id.derive` | proved | `Auth.Password.verify_phc` |
| `Argon2id.hash` | trusted | TRUSTED.md: The C |

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
| `PublicKey.rsaSize` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and others |
| `PublicKey.valid` | proved | through `PublicKey.ofSpki?`: `PublicKey.ofSpki?_spki` |
| `PublicKey.spki` | proved | `PublicKey.ofSpki?_spki` |
| `PublicKey.derSignature` | tested | `Tests/Sign.lean`, `Tests/Signature.lean` |
| `PublicKey.ofSpki?` | proved | `PublicKey.ofSpki?_spki` |
| `PublicKey.lines` | tested | `Tests/Sign.lean` |
| `PublicKey.pem` | tested | `Tests/Sign.lean` |
| `Rsa.powMod` | proved | `Rsa.powMod_eq` |
| `Rsa.digestInfo` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and others |
| `Rsa.encode` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and others |
| `Rsa.verifyReference` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Sign.lean` and others |

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

## `Lanes/Lib/Crypto/Verify.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `PublicKey.verifies` | proved | `Jose.verify_ok`, `OAuth.IdToken.verify_accepted` |

## `Lanes/Lib/Encoding/Base64.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Base64.Alphabet.last` | proved | through `Base64.decode`, `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and others |
| `Base64.Alphabet.code` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and others |
| `Base64.Alphabet.char` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and others |
| `Base64.Alphabet.valueOf` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.Alphabet.value?` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.Encoding.std` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Scram.respond_binds` |
| `Base64.Encoding.rawStd` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.url` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean` |
| `Base64.Encoding.rawUrl` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Base64.lean`, `Tests/Oracle/Jose.lean` and others |
| `Base64.sextet` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and others |
| `Base64.byte` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.pad` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and others |
| `Base64.encodeList` | proved | through `Base64.encode`: `Base64.allowed_of_mem_encode`, `Base64.decode_encode` and others |
| `Base64.full` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.tail1` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.tail2` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.decodeList` | proved | through `Base64.decode`: `Base64.decode_encode`, `Base64.decode_eq_none_of_length` and others |
| `Base64.encode` | proved | `Base64.allowed_of_mem_encode`, `Base64.decode_encode`, `Base64.decode_eq_some_iff` and others |
| `Base64.decode` | proved | `Base64.decode_encode`, `Base64.decode_eq_none_of_length`, `Base64.decode_eq_none_of_not_allowed` and others |
| `Base64.Encoding.Allowed` | spec | a predicate |
| `Base64.encodedLength` | spec | used only in statements |

## `Lanes/Lib/Encoding/Digits.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Digits.join` | proved | `Digits.join_split` |
| `Digits.split` | proved | `Digits.join_split` |
| `Digits.digits` | proved | through `Digits.toChars`: `Digits.head_toChars`, `Digits.ofChars?_toChars` |
| `Digits.char` | proved | through `Digits.fixed`, `Digits.toChars`: `Digits.head_toChars`, `Digits.ofChars?_fixed` and others |
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
| `JsonNumber.ofDecimal` | proved | through `JsonNumber.fromInt`, `JsonNumber.fromNat` and others: `Json.getInt?_eq_ok`, `Json.getNat?_eq_ok` and others |
| `JsonNumber.fromInt` | proved | `Json.getInt?_eq_ok` |
| `JsonNumber.fromNat` | proved | `Json.getNat?_eq_ok` |
| `JsonNumber.ofScientific` | proved | `Json.ofScientific_mantissa` |
| `JsonNumber.instCoeNat` | none |  |
| `JsonNumber.instCoeInt` | none |  |
| `JsonNumber.instOfNat` | tested | `Tests/Json.lean`, `Tests/Ops.lean`, `Tests/Oracle/All.lean` and others |
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
| `Json.sortFields` | proved | through `Json.depth`, `Json.mkObj` and others: `Http.Ops.Access.parse_line`, `Json.getObjVal?_mkObj` and others |
| `Json.dedupFields` | proved | through `Json.depth`, `Json.mkObj` and others: `Http.Ops.Access.parse_line`, `Json.getObjVal?_mkObj` and others |
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
| `Json.getObjVal?` | proved | `Jose.Compact.read_alg`, `Jose.readHeader_alg`, `Jose.verify_ok` and others |
| `Json.getArrVal?` | proved | `Json.getArrVal?_eq_ok` |
| `Json.getObjValD` | tested | `Tests/Json.lean`, `Tests/Oracle/All.lean`, `Tests/Oracle/Basic.lean` and others |

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
| `Json.Parser.fail` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.next?` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.accept` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.skipWsFrom` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.skipWs` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.acceptAll` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.hexDigit?` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.hexDigit` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.hex4` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.lowSurrogate` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.escape` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.strFrom` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.str` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.digitsFrom` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.whole` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.fraction` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.exponentDigits` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.exponent` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.unsigned` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.num` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.literal` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.key` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.value` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.Parser.elements` | spec | used only in statements |
| `Json.Parser.fields` | spec | used only in statements |
| `Json.Parser.document` | proved | through `Json.parse`: `Http.Ops.Access.parse_line`, `Json.parse_complete` and others |
| `Json.parse` | proved | `Http.Ops.Access.parse_line`, `Json.parse_complete`, `Json.parse_compress` and others |

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
| `Json.needsEscape` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and others |
| `Json.escapeChar` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and others |
| `Json.escape` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and others |
| `Json.renderString` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and others |
| `Json.separate` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and others |
| `Json.compressTo` | proved | through `Json.compress`, `Json.pretty`: `Json.fromUTF8?_compress`, `Json.fromUTF8?_pretty` and others |
| `Json.compress` | proved | `Json.fromUTF8?_compress`, `Json.parse_compress`, `Json.text_compress` |
| `Json.newline` | proved | through `Json.pretty`: `Json.fromUTF8?_pretty`, `Json.parse_pretty` and others |
| `Json.prettyTo` | proved | through `Json.pretty`: `Json.fromUTF8?_pretty`, `Json.parse_pretty` and others |
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
| `MediaType.token` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.skipWs` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.value` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.parseParams` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.parseRaw` | proved | through `MediaType.parse`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.isToken` | proved | through `MediaType.format`, `MediaType.valid`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.names` | proved | through `MediaType.format`, `MediaType.lower`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.valid` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq` |
| `MediaType.lower` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq` |
| `MediaType.parse` | proved | `MediaType.parse_format`, `MediaType.parse_format_eq`, `MediaType.parse_print` |
| `MediaType.quote` | proved | through `MediaType.format`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.valueChars` | proved | through `MediaType.format`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
| `MediaType.chars` | proved | through `MediaType.format`: `MediaType.parse_format`, `MediaType.parse_format_eq` and others |
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
| `Ip.octet?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.parse4` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.print4` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.hexGroup?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.groups?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.expand` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.fields?` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.parse6` | proved | through `Ip.Prefix.parse`, `Ip.parse`: `Ip.Prefix.parse_print`, `Ip.parse_print` |
| `Ip.parse` | proved | `Ip.parse_print` |
| `Ip.zeroRun` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.runAt` | proved | `Ip.longestZeroRun_none`, `Ip.longestZeroRun_some` |
| `Ip.longestZeroRun` | proved | `Ip.longestZeroRun_none`, `Ip.longestZeroRun_some` |
| `Ip.withEllipsis` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.hexFields` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.fields` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.mappedPrefix` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.print6` | proved | through `Ip.Addr.isLoopback`, `Ip.Prefix.bits` and others: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.print` | proved | `Ip.parse_print` |
| `Ip.Found` | spec | a predicate |
| `Ip.Addr.width` | proved | `Ip.Prefix.contains_iff` |
| `Ip.Addr.toNat` | spec | used only in statements |
| `Ip.mask` | proved | through `Ip.Prefix.contains`, `Ip.Prefix.masked`: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.Addr.masked` | proved | through `Ip.Prefix.contains`, `Ip.Prefix.masked`: `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` and others |
| `Ip.Prefix.masked` | proved | `Ip.Prefix.contains_masked`, `Ip.Prefix.masked_masked` |
| `Ip.Prefix.contains` | proved | `Ip.Prefix.contains_iff`, `Ip.Prefix.contains_masked` |
| `Ip.Prefix.print` | proved | `Ip.Prefix.parse_print` |
| `Ip.decimal?` | proved | through `Ip.Prefix.parse`: `Ip.Prefix.parse_print` |
| `Ip.Prefix.parse` | proved | `Ip.Prefix.parse_print` |
| `Ip.Addr.isLoopback` | proved | `Ip.isLoopback_v4`, `Ip.isLoopback_v6` |

## `Lanes/Lib/Net/Url.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Url.isAlpha` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.isDigit` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.isHex` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.isUnreserved` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.isSubDelim` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.isPchar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.isPathChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.isQueryChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.isUserChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.isNameChar` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.isSchemeChar` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.encoded` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.lowerChar` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.lower` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.schemeOk` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.Host.chars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.Authority.chars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.pathChars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.chars` | proved | through `Url.print`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.print` | proved | `Url.parse_print`, `Url.parse_print_of_valid` |
| `Url.cut` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.breakSlash` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.schemeEnd` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.parseHost` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.parseAuthority` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.parseRaw` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.Host.valid` | proved | through `Url.normalize`, `Url.parse` and others: `Tests.Oracle.Url.resolve_examples`, `Url.normalize_normalize` and others |
| `Url.Authority.valid` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.pathFits` | proved | through `Url.parse`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.parse_print` and others |
| `Url.valid` | proved | `Url.parse_print_of_valid` |
| `Url.parse` | proved | `Url.parse_print`, `Url.parse_print_of_valid` |
| `Url.dots` | proved | through `Url.normalize`, `Url.removeDots` and others: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and others |
| `Url.piece` | proved | through `Url.normalize`, `Url.removeDots` and others: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and others |
| `Url.join` | proved | through `Url.normalize`, `Url.removeDots` and others: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and others |
| `Url.removeDotsChars` | proved | through `Url.normalize`, `Url.removeDots` and others: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_removeDots` and others |
| `Url.removeDots` | proved | `Url.dotFree_removeDots`, `Url.removeDots_of_dotFree`, `Url.removeDots_removeDots` and others |
| `Url.directory` | proved | through `Url.resolve`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_resolve` and others |
| `Url.merge` | proved | through `Url.resolve`, `Url.resolveText`: `Tests.Oracle.Url.resolve_examples`, `Url.dotFree_resolve` and others |
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
| `Postgres.Isolation.sql` | proved | through `Postgres.Conn.Request.encode`, `Postgres.Conn.Request.messages` and others: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.Request.kind` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.instDecidableNamed` | proved | its type, `Decidable` |
| `Postgres.Conn.instDecidablePredOptionByteArrayValueOk` | proved | its type, `Decidable` |
| `Postgres.Conn.instDecidablePredFrontendOk` | proved | its type, `Decidable` |
| `Postgres.Conn.fits` | proved | through `Postgres.Conn.run`, `Postgres.Conn.start` and others: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.Request.messages` | proved | `Postgres.Conn.valid_decode` |
| `Postgres.Conn.Request.encode` | proved | `Postgres.Conn.step_query` |
| `Postgres.Conn.valid` | proved | `Postgres.Conn.step_query`, `Postgres.Conn.valid_decode` |
| `Postgres.Conn.room` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.fail` | proved | `Postgres.Conn.onMessage_sasl_authOk`, `Postgres.Conn.step_refusedTls` |
| `Postgres.Conn.outcome` | proved | `Postgres.Conn.outcome_committed` |
| `Postgres.Conn.texts` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and others: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and others |
| `Postgres.Conn.onReply` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and others: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and others |
| `Postgres.Conn.nonceOk` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and others: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and others |
| `Postgres.Conn.Config.scramOnly` | proved | `Postgres.Conn.onMessage_requireScram` |
| `Postgres.Conn.unbound` | proved | through `Postgres.Conn.choose`, `Postgres.Conn.onMessage` and others: `Postgres.Conn.choose_endPoint`, `Postgres.Conn.choose_require` and others |
| `Postgres.Conn.choose` | proved | `Postgres.Conn.choose_endPoint`, `Postgres.Conn.choose_require` |
| `Postgres.Conn.onAuth` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and others: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and others |
| `Postgres.Conn.onSasl` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and others: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and others |
| `Postgres.Conn.onSaslFinal` | proved | through `Postgres.Conn.onMessage`, `Postgres.Conn.run` and others: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened` and others |
| `Postgres.Conn.onMessage` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Conn.onMessage_opened`, `Postgres.Conn.onMessage_requireScram` and others |
| `Postgres.Conn.drain` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.receive` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.submit` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.startup` | proved | `Postgres.Conn.step_secured` |
| `Postgres.Conn.sslRequest` | proved | `Postgres.Conn.tls_first` |
| `Postgres.Conn.alpn` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.start` | proved | `Postgres.Conn.run_bound`, `Postgres.Conn.start_queue`, `Postgres.Conn.tls_first` |
| `Postgres.Conn.beforeTls` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.alpnOk` | proved | `Postgres.Conn.step_secured` |
| `Postgres.Conn.secure` | proved | through `Postgres.Conn.run`, `Postgres.Conn.step`: `Postgres.Conn.run_beforeTls`, `Postgres.Conn.run_bound` and others |
| `Postgres.Conn.Phase.beforeTls` | proved | `Postgres.Conn.run_beforeTls`, `Postgres.Conn.step_beforeTls` |
| `Postgres.Conn.reusable` | tested | `Tests/Postgres.lean` |
| `Postgres.Conn.step` | proved | `Postgres.Conn.step_beforeTls`, `Postgres.Conn.step_buffer`, `Postgres.Conn.step_closed` and others |
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
| `Postgres.Client.Config.ofSettings` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Env.io` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.Client.fromEnv` | trusted | TRUSTED.md: The PostgreSQL client's IO |
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
| `Postgres.socketAddress` | trusted | TRUSTED.md: The PostgreSQL client's IO |
| `Postgres.resolve` | trusted | TRUSTED.md: The PostgreSQL client's IO |
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
| `Postgres.protocol30` | proved | through `Postgres.Frontend.decode`, `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and others |
| `Postgres.Column.put` | proved | through `Postgres.Backend.body`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Column.get` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody` and others: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and others |
| `Postgres.Column.Ok` | spec | a predicate |
| `Postgres.Field.put` | proved | through `Postgres.Backend.body`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Field.get` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Field.Ok` | spec | a predicate |
| `Postgres.getFields` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.getNames` | proved | through `Postgres.Backend.decodeBody`, `Postgres.Frame.read`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and others |
| `Postgres.Named` | spec | a predicate |
| `Postgres.putParam` | proved | through `Postgres.Frontend.body`, `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and others |
| `Postgres.getParam` | proved | through `Postgres.Backend.decode`, `Postgres.Backend.decodeBody` and others: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and others |
| `Postgres.Backend.tag` | proved | `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Backend.body` | proved | `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` |
| `Postgres.Backend.Ok` | spec | a predicate |
| `Postgres.Backend.decodeAuth` | proved | through `Postgres.Backend.decodeBody`, `Postgres.Frame.read`: `Postgres.Backend.decodeBody_body`, `Postgres.Backend.read_encode` and others |
| `Postgres.Backend.decodeBody` | proved | `Postgres.Backend.decodeBody_body` |
| `Postgres.Backend.decode` | proved | `Postgres.Backend.read_encode` |
| `Postgres.Frontend.expect` | spec | used only in statements |
| `Postgres.Frontend.tag` | proved | through `Postgres.Frontend.body`, `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and others |
| `Postgres.Frontend.body` | proved | `Postgres.Frontend.decode_encode` |
| `Postgres.Frontend.Ok` | spec | a predicate |
| `Postgres.Frontend.wire` | proved | through `Postgres.Frontend.encode`: `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured` and others |
| `Postgres.Frontend.encode` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Conn.step_secured`, `Postgres.Conn.valid_decode` and others |
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
| `Postgres.Pool.refill` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.hand` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.onCheckout` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.onOpened` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.onFailed` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.onCheckin` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.onExpire` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.step` | proved | through `Postgres.Pool.run`: `Postgres.Pool.never_again`, `Postgres.Pool.run_size` and others |
| `Postgres.Pool.run` | spec | used only in statements |
| `Postgres.Pool.Out` | spec | a predicate |

## `Lanes/Lib/Postgres/Scram.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.md5Answer` | checked | `Tests/PostgresConn.lean` |
| `Postgres.Scram.mechanism` | proved | through `Postgres.Scram.Binding.data`, `Postgres.Scram.respond`: `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint` and others |
| `Postgres.Scram.mechanismPlus` | proved | `Postgres.Conn.choose_endPoint` |
| `Postgres.Scram.Binding.header` | proved | through `Postgres.Scram.Binding.data`, `Postgres.Scram.respond`: `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint` and others |
| `Postgres.Scram.Binding.mechanism` | proved | through `Postgres.Scram.Binding.data`, `Postgres.Scram.respond`: `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint` and others |
| `Postgres.Scram.Binding.data` | proved | `Postgres.Conn.onMessage_binds`, `Postgres.Scram.Binding.data_endPoint`, `Postgres.Scram.respond_binds` |
| `Postgres.Scram.saslName` | proved | through `Postgres.Scram.respond`: `Postgres.Scram.respond_binds`, `Postgres.Scram.respond_iterations` and others |
| `Postgres.Scram.firstBare` | proved | through `Postgres.Scram.respond`: `Postgres.Scram.respond_binds`, `Postgres.Scram.respond_iterations` and others |
| `Postgres.Scram.first` | tested | `Tests/Postgres.lean` |
| `Postgres.Scram.field` | proved | through `Postgres.Scram.respond`, `Postgres.Scram.verify`: `Postgres.Conn.onMessage_requireScram`, `Postgres.Conn.onMessage_saslFinal` and others |
| `Postgres.Scram.parseServerFirst` | proved | `Postgres.Scram.respond_iterations`, `Postgres.Scram.respond_nonce` |
| `Postgres.Scram.respond` | proved | `Postgres.Scram.respond_binds`, `Postgres.Scram.respond_iterations`, `Postgres.Scram.respond_nonce` |
| `Postgres.Scram.verify` | proved | `Postgres.Conn.onMessage_requireScram`, `Postgres.Conn.onMessage_saslFinal` |

## `Lanes/Lib/Postgres/Settings.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Address.localhost` | proved | through `Postgres.SslMode.defaultFor`: `Postgres.Client.Config.sslmode_default`, `Postgres.SslMode.defaultFor_disable` and others |
| `Postgres.Address.of` | proved | `Postgres.SslMode.defaultFor_disable`, `Postgres.SslMode.defaultFor_loopback`, `Postgres.SslMode.defaultFor_remote` |
| `Postgres.Address.preferred` | proved | `Postgres.Address.preferred_isSome`, `Postgres.Address.preferred_spec` |
| `Postgres.Address.loopback` | proved | `Postgres.Address.name_remote`, `Postgres.SslMode.defaultFor_disable`, `Postgres.SslMode.defaultFor_loopback` and others |
| `Postgres.SslMode.defaultFor` | proved | `Postgres.Client.Config.sslmode_default`, `Postgres.SslMode.defaultFor_disable`, `Postgres.SslMode.defaultFor_loopback` and others |
| `Postgres.SslMode.ofLibpq` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.channelBindingOfLibpq` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.PassFile.split` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.PassFile.split.go` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.PassFile.fits` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.PassFile.find` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.deployCa` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.first` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.get` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.portOf` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.hostOf` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.passwordOf` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.rootCertOf` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |
| `Postgres.Settings.read` | tested | `Tests/PostgresLive.lean`, `Tests/PostgresSettings.lean` |

## `Lanes/Lib/Postgres/Table.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Postgres.Table.create` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/Postgres.lean`, `Tests/Postgres.lean` and others |
| `Postgres.Table.Isolation.ofStore` | tested | `Tests/Postgres.lean` |
| `Postgres.Table.request` | tested | `Tests/Postgres.lean` |
| `Postgres.scanRows` | tested | `Tests/Postgres.lean` |
| `Postgres.Table.answer` | tested | `Tests/Postgres.lean` |
| `Postgres.Table.over` | tested | `Tests/Postgres.lean` |

## `Lanes/Lib/RateLimit.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `RateLimit.Config.cap` | proved | `RateLimit.allowed_le`, `RateLimit.credit_allowAll_le`, `RateLimit.credit_allow_le` and others |
| `RateLimit.full` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/RateLimit.lean` |
| `RateLimit.refill` | proved | through `RateLimit.allow`, `RateLimit.allowAll` and others: `RateLimit.allow_after_reserve`, `RateLimit.allowed_le` and others |
| `RateLimit.allow` | proved | `RateLimit.allow_after_reserve`, `RateLimit.credit_allow_le` |
| `RateLimit.wait` | proved | through `RateLimit.reserve`: `RateLimit.allow_after_reserve`, `RateLimit.credit_reserve_le` |
| `RateLimit.reserve` | proved | `RateLimit.allow_after_reserve`, `RateLimit.credit_reserve_le` |
| `RateLimit.allowAll` | spec | used only in statements |

## `Lanes/Lib/Time/Civil.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Civil.isLeap` | proved | through `Civil.Date.toDays`, `Civil.DateTime` and others: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.daysInMonth` | proved | through `Civil.Date.toDays`, `Civil.DateTime` and others: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.Valid` | spec | a predicate |
| `Civil.instDecidableValid` | proved | its type, `Decidable` |
| `Civil.Date.mk?` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean`, `Tests/S3Upload.lean` |
| `Civil.marchMonth` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.ofMarchMonth` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.daysBefore` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.marchLength` | spec | used only in statements |
| `Civil.dayOfEra` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.daysFrom` | proved | through `Civil.Date.toDays`, `Civil.DateTime.toUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.Date.toDays` | proved | `Civil.ofDays_toDays`, `Civil.toDays_ofDays` |
| `Civil.yearOfEra` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.civilOf` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.civil` | proved | through `Civil.Date.ofDays`, `Civil.DateTime.ofUnix`: `Civil.ofDays_toDays`, `Civil.ofUnix_toUnix` and others |
| `Civil.LongYear` | spec | a predicate |
| `Civil.Date.ofDays` | proved | `Civil.ofDays_toDays`, `Civil.toDays_ofDays` |
| `Civil.Date.weekday` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Time.lean` |
| `Civil.TimeOfDay.seconds` | proved | through `Civil.DateTime.toUnix`: `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` and others |
| `Civil.TimeOfDay.ofSeconds` | proved | through `Civil.DateTime.ofUnix`: `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix` and others |
| `Civil.DateTime.toUnix` | proved | `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix`, `S3.Post.admitted_bounded` and others |
| `Civil.DateTime.ofUnix` | proved | `Civil.ofUnix_toUnix`, `Civil.toUnix_ofUnix`, `S3.Post.admitted_bounded` and others |

## `Lanes/Lib/Time/Format.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `TimeFormat.isDigit` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and others |
| `TimeFormat.num?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and others |
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
| `TimeFormat.clock?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and others |
| `TimeFormat.fraction?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and others |
| `TimeFormat.offset?` | proved | through `TimeFormat.parseHttpDate`, `TimeFormat.parseRfc3339`: `S3.Post.expiration_parse`, `TimeFormat.parseHttpDate_print` and others |
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
| `Peers.Courier.setWire` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and others |
| `Peers.Courier.dial` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and others |
| `Peers.Courier.enqueue` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and others |
| `Peers.Courier.next` | proved | through `Peers.Courier.exec`, `Peers.Courier.step`: `Peers.Courier.Reachable.write_not_busy`, `Peers.Courier.after_stop` and others |
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

## `Lanes/Net/Handshake.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Handshake.magic` | proved | through `Peers.Handshake.Hello.read`, `Peers.Handshake.Hello.write` and others: `Peers.Handshake.Hello.read_write_append`, `Peers.Handshake.Reachable.ready_proved` and others |
| `Peers.Handshake.version` | proved | `Peers.Handshake.Hello.read_write_append` |
| `Peers.Handshake.proofSize` | proved | `Peers.Handshake.Reachable.ready_proved` |
| `Peers.Handshake.Hello.records` | proved | `Peers.Handshake.Hello.read_write_append` |
| `Peers.Handshake.Hello.write` | proved | `Peers.Handshake.Hello.read_write_append` |
| `Peers.Handshake.Hello.read` | proved | `Peers.Handshake.Hello.read_write_append`, `Peers.Handshake.Reachable.ready_proved`, `Peers.Handshake.hear_differs` |
| `Peers.Handshake.Role.other` | proved | `Peers.Handshake.Reachable.ready_proved` |
| `Peers.Handshake.Role.label` | proved | through `Peers.Handshake.hear`, `Peers.Handshake.step`: `Peers.Handshake.Reachable.ready_proved`, `Peers.Handshake.hear_differs` |
| `Peers.Handshake.Refusal.message` | tested | `Tests/Fronted.lean`, `Tests/Peers.lean` |
| `Peers.Handshake.Refusal.quiet` | tested | `Tests/Fronted.lean`, `Tests/Peers.lean` |
| `Peers.Handshake.transcript` | proved | `Peers.Handshake.Reachable.ready_proved` |
| `Peers.Handshake.proofOf` | proved | `Peers.Handshake.Reachable.ready_proved` |
| `Peers.Handshake.differs` | proved | `Peers.Handshake.Reachable.ready_proved`, `Peers.Handshake.hear_differs` |
| `Peers.Handshake.refuse` | proved | through `Peers.Handshake.hear`, `Peers.Handshake.step`: `Peers.Handshake.Reachable.ready_proved`, `Peers.Handshake.hear_differs` |
| `Peers.Handshake.check` | proved | through `Peers.Handshake.hear`, `Peers.Handshake.step`: `Peers.Handshake.Reachable.ready_proved`, `Peers.Handshake.hear_differs` |
| `Peers.Handshake.hear` | proved | `Peers.Handshake.hear_differs` |
| `Peers.Handshake.start` | tested | `Tests/Peers.lean` |
| `Peers.Handshake.step` | proved | `Peers.Handshake.Reachable.ready_proved` |

## `Lanes/Net/HandshakeSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Handshake.Heard` | spec | a predicate |

## `Lanes/Net/IO/Node.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.serveShard` | trusted | TRUSTED.md: A process with a front and peers |

## `Lanes/Net/IO/Peers.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Peers.Config.minKeyBytes` | trusted | TRUSTED.md: The transport between processes |
| `Peers.start` | trusted | TRUSTED.md: The transport between processes |
| `Peers.send` | trusted | TRUSTED.md: The transport between processes |
| `Peers.stop` | trusted | TRUSTED.md: The transport between processes |
| `Peers.shard` | trusted | TRUSTED.md: The transport between processes |

## `Lanes/Outside/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Outside.any` | tested | `Tests/Jobs.lean`, `Tests/S3.lean` |
| `Outside.driver` | checked | `Tests/Cache.lean`, `Tests/Clock.lean`, `Tests/HttpClient.lean` and others |
| `Outside.see` | proved | `Outside.Beside.keeps`, `Outside.run_induction` |
| `Outside.after` | proved | `Cache.read_sent`, `Clock.wall_back_le`, `Clock.wall_latest_le` and others |
| `Outside.allows` | checked | `Tests/Outside.lean`, `Tests/Queue.lean`, `Tests/Throttle.lean` and others |
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
| `Effects.Lifecycle.reachable` | proved | through `Effects.Lifecycle.reaches`, `Effects.outside`: `Effects.Lifecycle.reaches_terminal`, `Effects.Sound.allow` and others |
| `Effects.Lifecycle.reachable.go` | proved | through `Effects.Lifecycle.reaches`, `Effects.outside`: `Effects.Lifecycle.reaches_terminal`, `Effects.Sound.allow` and others |
| `Effects.Lifecycle.reaches` | proved | `Effects.Lifecycle.reaches_terminal` |
| `Effects.Lifecycle.seen` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.Answer.codec` | proved | its type, `Codec` |
| `Effects.instCodableAnswer` | proved | its type, `Codable` |
| `Effects.Answer.isRefused` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.Report.codec` | proved | its type, `Codec` |
| `Effects.instCodableReport` | proved | its type, `Codable` |
| `Effects.Thing.codec` | proved | its type, `Codec` |
| `Effects.instCodableThing` | proved | its type, `Codable` |
| `Effects.ids` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.answered` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.moved` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.reported` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.server` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.service` | proved | through `Effects.outside`: `Effects.Sound.allow`, `Effects.Sound.observe` and others |
| `Effects.outside` | proved | `Effects.Sound.allow`, `Effects.Sound.observe`, `Effects.Sound.shows_reply` and others |
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
| `Idempotent.holder` | proved | through `Idempotent.server`: `Idempotent.answer_repeat`, `Idempotent.at_most_once` and others |
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
| `Queue.inOrder` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and others |
| `Queue.ready` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and others |
| `Queue.receive` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and others |
| `Queue.delete` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and others |
| `Queue.send` | proved | through `Queue.outside`: `Queue.deleted_not_received`, `Queue.fifo_received_le` and others |
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
| `Rpc.outside` | proved | `Cache.read_sent`, `Events.deliveries_le`, `Idempotent.at_most_once` and others |
| `Rpc.Port.reported` | proved | `Effects.Sound.shows_report`, `Transcode.done_given`, `Transcode.reports_agree` |
| `Rpc.called` | spec | used only in statements |
| `Rpc.answered` | spec | used only in statements |

## `Lanes/Outside/Store/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Store.Db.get` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.Db.insertSorted` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.Db.set` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.Db.apply` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.Read.holds` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.Txn.own` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.Txn.view` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.txn?` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.setTxn` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.dropTxn` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.stateAt` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.readsAll` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.clashes` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.places` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.commitPlaces` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.placeAt` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.settle` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.answersNow` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.applyCommit` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.expand` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.dedup` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.send` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.answer` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.World.answerCommit` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.outstanding` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.State.allow` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.State.observe` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
| `Store.State.run` | proved | through `Store.allows`: `Store.failed_never_committed`, `Store.insert_unique` and others |
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
| `Event.deed` | proved | through `deeds`, `handled`: `Http.Gate.answered_le_handled`, `Jobs.answered_le_handled` and others |
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
| `Envelope.left?` | proved | through `Event.leftDeed`, `Event.right?` and others: `Obligation.right?_inr`, `SysState.run_left` and others |
| `Envelope.right?` | proved | through `Event.right?`, `Event.rightDeed` and others: `Obligation.Due.of_thinRight`, `Obligation.right?_inr` and others |
| `EnvModel.left` | proved | `SysState.run_left`, `System.Invariant.join_left`, `System.LeadsTo.join_left` and others |
| `EnvModel.right` | proved | `Obligation.Due.of_thinRight`, `SysState.deliverable_of_thinRight`, `SysState.init_thinRight` and others |
| `SysState.left` | proved | `SysState.run_left`, `System.Invariant.join_left`, `System.LeadsTo.join_left` and others |
| `SysState.right` | proved | `System.Invariant.join_right`, `System.LeadsTo.join_right`, `System.Reachable.right` and others |
| `SysState.thinLeft` | proved | `System.LeadsTo.join_left`, `System.Run.Fair.left` |
| `Event.left?` | proved | through `Event.leftDeed`, `Event.right?` and others: `Obligation.right?_inr`, `SysState.run_left` and others |
| `Event.leftDeed` | proved | `SysState.run_left`, `SysState.step_left_state`, `System.Run.Fair.left` and others |
| `Wiring.shown` | proved | `SysState.run_left`, `System.Run.Fair.left` |
| `SysState.thinRight` | proved | `Obligation.Due.of_thinRight`, `SysState.deliverable_of_thinRight`, `SysState.hasMail_of_thinRight` and others |
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
| `SysState.grow` | proved | `Account.Fires.grow`, `Account.Fires.handle`, `Account.Moves.grow` and others |
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
| `Batch.Act.steps` | spec | used only in statements |
| `Batch.history` | spec | used only in statements |
| `Batch.Act.grows` | proved | through `Batch.flush`, `Batch.grown` and others: `Batch.flush_save`, `Batch.grown_eq` and others |
| `Batch.grown` | proved | `Batch.grown_eq` |
| `Batch.workWith` | proved | through `Batch.flush`, `Batch.run` and others: `Batch.flush_save`, `Batch.run_handed` and others |
| `Batch.work` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_ids` and others |
| `Batch.workAll` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_ids` and others |
| `Batch.flush` | proved | `Batch.flush_save` |
| `Batch.scan` | proved | through `Batch.run`, `Batch.settle`: `Batch.run_handed`, `Batch.run_ids` and others |
| `Batch.finish` | proved | through `Batch.run`: `Batch.run_handed`, `Batch.run_ids` and others |
| `Batch.group` | proved | `Batch.group_ins` |
| `Batch.Command.ins` | spec | used only in statements |
| `Batch.run` | proved | `Batch.run_handed`, `Batch.run_ids`, `Batch.run_ids_spread` and others |
| `Batch.Act.ops` | proved | through `Batch.journal`: `Batch.history_ops`, `Batch.run_handed` and others |
| `Batch.Act.outputs` | proved | through `Batch.handed`, `Batch.handedIds`: `Batch.run_handed`, `Batch.run_ids` and others |
| `Batch.Act.placed` | spec | used only in statements |
| `Batch.Act.events` | proved | through `Batch.recorded`: `Batch.run_handed` |
| `Batch.journal` | proved | `Batch.history_ops`, `Batch.run_handed`, `Batch.run_kernel` and others |
| `Batch.handed` | proved | `Batch.run_handed` |
| `Batch.handedIds` | spec | used only in statements |
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
| `Kernel.cell` | proved | `Batch.run_peek`, `Journal.Upgrade.inv_load`, `Kernel.Plan.fixAll_local` and others |
| `Kernel.setCell` | proved | through `Journal.ids`, `Kernel.apply` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.abs` | proved | `Kernel.WellFormed.quiet_iff`, `Kernel.WellFormed.wait_forever`, `Kernel.abs_boot` and others |
| `Kernel.env` | proved | `Kernel.abs_boot`, `Kernel.accept_sound`, `Kernel.exec_reachable` and others |
| `Kernel.unschedule` | proved | through `Journal.ids`, `Kernel.apply` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.perform` | proved | through `Journal.ids`, `Kernel.apply` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.performAll` | proved | through `Journal.ids`, `Kernel.apply` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.down` | proved | through `Journal.ids`, `Kernel.apply` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.settle` | proved | `Kernel.setState_settle` |
| `Kernel.rest` | proved | through `Kernel.apply`, `Kernel.exec` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.takeState` | proved | through `Kernel.apply`, `Kernel.exec` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.handle` | proved | `Kernel.frame_handle`, `Kernel.handleAhead_eq`, `Kernel.handle_setState` |
| `Kernel.startActor` | proved | `Kernel.frame_startActor` |
| `Kernel.boot` | proved | `Http.kernel_fronted_answered_le_arrived`, `Http.kernel_served_answered_le_arrived`, `Journal.Disk.torn_nil` and others |
| `Kernel.accept` | proved | `Kernel.accept_sound` |
| `Kernel.run1` | proved | `Kernel.run1Ahead_eq`, `Kernel.run1_sound` |
| `Kernel.fire` | proved | `Kernel.fire_sound`, `Kernel.frame_fire` |
| `Kernel.advance` | proved | through `Kernel.apply`, `Kernel.exec`: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.timerNext` | proved | through `Kernel.apply`, `Kernel.exec` and others: `Batch.run_handed`, `Batch.run_kernel` and others |
| `Kernel.step` | proved | `Kernel.WellFormed.runBatch_of_due`, `Kernel.WellFormed.step_events_ne_nil`, `Kernel.WellFormed.step_of_due` and others |
| `Kernel.wait` | proved | `Kernel.WellFormed.step_events_ne_nil`, `Kernel.WellFormed.wait_for_ms`, `Kernel.WellFormed.wait_forever` and others |
| `Kernel.runBatch` | proved | `Kernel.WellFormed.runBatch`, `Kernel.WellFormed.runBatch_of_due`, `Kernel.runBatchAhead_eq` and others |
| `Kernel.quiet` | proved | `Batch.run_resolved`, `Kernel.WellFormed.quiet_iff` |
| `Kernel.image` | proved | `Batch.flush_save`, `Journal.Disk.Holds.load_save_crash`, `Journal.Disk.Holds.save` and others |
| `Kernel.Image.kernel` | proved | `Batch.flush_save`, `Journal.Begun.resume_upgraded`, `Journal.Upgrade.begin_crash` and others |
| `Kernel.apply` | proved | `Kernel.WellFormed.apply` |
| `Kernel.exec` | proved | `Batch.run_handed`, `Batch.run_kernel`, `Batch.settle_kernel` and others |

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
| `Mailbox.offerOrWait` | proved | through `Mailbox.Op.apply`, `Mailbox.boundedIn` and others: `Mailbox.after_close`, `Mailbox.batch_since_take` and others |
| `Mailbox.take` | proved | `Mailbox.Reachable.asleep_empty`, `Mailbox.batch_since_take`, `Mailbox.close_since_take` and others |
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
| `splitSig` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and others |
| `shardWiring` | proved | through `System.split`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and others |
| `System.split` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and others |
| `Signature.Inspect.split` | tested | `Tests/Split.lean` |
| `System.Inspect.split` | tested | `Tests/Split.lean` |
| `Split.actorOf` | proved | through `EnvModel.split`, `Event.merged?` and others: `SysState.AtHome.step`, `SysState.init_merged_equiv` and others |
| `Split.home` | spec | used only in statements |
| `Split.atHome` | proved | through `EnvModel.split`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and others |
| `Split.route` | tested | `Tests/Split.lean` |
| `Split.output?` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and others |
| `Split.msgOf` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and others |
| `Envelope.merged` | proved | through `Event.merged?`, `SysState.merged`: `SysState.AtHome.step`, `SysState.init_merged_equiv` and others |
| `Envelope.atHome` | tested | `Tests/Split.lean` |
| `Event.merged?` | spec | used only in statements |
| `Event.routed` | proved | `SysState.AtHome.step` |
| `EnvModel.split` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.SplitReachable.merged_of_init` |
| `SysState.merged` | proved | `SysState.AtHome.step`, `SysState.init_merged_equiv`, `System.Invariant.split` and others |
| `System.SteadyBoot` | spec | a predicate |

## `Lanes/Runtime/ShardsSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `joinAllSig` | proved | through `shardsSig`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `joinAllEffect` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `System.joinAll` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `shardsSig` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and others |
| `shardsRoute` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `System.shards` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and others |
| `Signature.Inspect.joinAll` | tested | `Tests/Split.lean` |
| `System.Inspect.joinAll` | tested | `Tests/Split.lean` |
| `Signature.Inspect.shards` | tested | `Tests/Split.lean` |
| `System.Inspect.shards` | tested | `Tests/Split.lean` |
| `Shards.atHome` | proved | through `EnvModel.shards`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `Shards.route` | tested | `Tests/Split.lean` |
| `Shards.output?` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `Shards.routed` | proved | `Shards.AtHome.step` |
| `Envelope.unsharded` | proved | through `SysState.unsharded`: `Shards.AtHome.step`, `SysState.init_unsharded_equiv` and others |
| `Envelope.atHomeAll` | tested | `Tests/Split.lean` |
| `Event.unsharded?` | spec | used only in statements |
| `EnvModel.shards` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.ShardsReachable.unsharded_of_init` |
| `SysState.unsharded` | proved | `Shards.AtHome.step`, `SysState.init_unsharded_equiv`, `System.Invariant.shards` and others |
| `Shards.effect` | spec | used only in statements |

## `Lanes/Runtime/Wave.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Kernel.replay` | proved | through `Kernel.Plan.fixAll`, `Kernel.Plan.real` and others: `Kernel.Plan.fixAll_local`, `Kernel.good_plan` and others |
| `Kernel.ahead` | proved | through `Kernel.plan`, `Kernel.runWaves` and others: `Kernel.good_plan`, `Kernel.runWaves_eq` and others |
| `Kernel.Fits` | spec | a predicate |
| `Kernel.setState` | proved | `Kernel.Plan.fixAll_local`, `Kernel.handle_setState`, `Kernel.setState_settle` |
| `Kernel.restAs` | proved | through `Kernel.handleAhead`, `Kernel.run1Ahead` and others: `Kernel.handleAhead_eq`, `Kernel.run1Ahead_eq` and others |
| `Kernel.Plan.set` | proved | through `Kernel.handleAhead`, `Kernel.plan` and others: `Kernel.good_plan`, `Kernel.handleAhead_eq` and others |
| `Kernel.Plan.drop` | proved | through `Kernel.Plan.fixAll`, `Kernel.Plan.real` and others: `Kernel.Plan.fixAll_local`, `Kernel.good_plan` and others |
| `Kernel.Plan.reset` | proved | through `Kernel.run1Ahead`, `Kernel.runBatchAhead` and others: `Kernel.run1Ahead_eq`, `Kernel.runBatchAhead_eq` and others |
| `Kernel.Plan.fixAt` | proved | through `Kernel.Plan.fixAll`, `Kernel.Plan.real` and others: `Kernel.Plan.fixAll_local`, `Kernel.good_plan` and others |
| `Kernel.Plan.fixAll` | proved | `Kernel.Plan.fixAll_local` |
| `Kernel.Plan.real` | proved | `Kernel.good_plan`, `Kernel.handleAhead_eq`, `Kernel.run1Ahead_eq` and others |
| `Kernel.Plan.Good` | spec | a predicate |
| `Kernel.handleAhead` | proved | `Kernel.handleAhead_eq` |
| `Kernel.run1Ahead` | proved | `Kernel.run1Ahead_eq` |
| `Kernel.stepAhead` | proved | `Kernel.stepAhead_eq` |
| `Kernel.runBatchAhead` | proved | `Kernel.runBatchAhead_eq`, `Kernel.wave_eq` |
| `Kernel.mail` | proved | through `Kernel.plan`, `Kernel.runWaves` and others: `Kernel.good_plan`, `Kernel.runWaves_eq` and others |
| `Kernel.Job.run` | proved | through `Kernel.plan`, `Kernel.runWaves` and others: `Kernel.good_plan`, `Kernel.runWaves_eq` and others |
| `Kernel.jobs` | proved | through `Kernel.plan`, `Kernel.runWaves` and others: `Kernel.good_plan`, `Kernel.runWaves_eq` and others |
| `Kernel.chunks` | proved | through `Kernel.plan`, `Kernel.runWaves` and others: `Kernel.good_plan`, `Kernel.runWaves_eq` and others |
| `Kernel.Plan.add` | proved | through `Kernel.plan`, `Kernel.runWaves` and others: `Kernel.good_plan`, `Kernel.runWaves_eq` and others |
| `Kernel.plan` | proved | `Kernel.good_plan`, `Kernel.wave_eq` |
| `Kernel.Frame` | spec | a predicate |
| `Kernel.waves` | proved | `Kernel.waves_eq` |
| `Kernel.runWaves` | proved | `Kernel.runWaves_eq` |
| `Kernel.acceptAll` | proved | `Kernel.exec_inputs` |

## `Lanes/Runtime/WavePlan.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `WavePlan.first` | spec | used only in statements |
| `WavePlan.levelsFrom` | spec | used only in statements |
| `WavePlan.levels` | spec | used only in statements |
| `WavePlan.split` | spec | used only in statements |

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
| `Spec.stutter` | proved | through `System.Run`, `System.Run.event` and others: `Http.Gate.pending_answered`, `Http.fronted_arrival_answered` and others |
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
| `Spec.lts` | proved | `Account.Holds.passes`, `Check.Monitor.complete`, `Check.Monitor.ok_iff` and others |
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
| `Service.spec` | proved | `Account.Holds.passes`, `Account.implements`, `Account.implements_timed` and others |
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
| `System.sem` | proved | `Account.implements`, `Account.implements_timed`, `Once.server_implements` and others |
| `System.Refines` | spec | a predicate |

## `Lanes/Testing/Browser.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.Browser.new` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Browser.at` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.Kept.parse` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Kept.covers` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Browser.cookie` | tested | `Tests/OAuth.lean` |
| `Testing.Browser.keep` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Browser.forget` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean` |
| `Testing.Browser.record` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Browser.call` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Browser.get` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.Browser.post` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.Browser.submit` | tested | `Tests/Testing.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |

## `Lanes/Testing/Http.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.listen` | tested | `Tests/Testing.lean` |
| `Testing.json` | tested | `Tests/Testing.lean` |
| `Testing.text` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.shows` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.status` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
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
| `Testing.OAuth.str` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.OAuth.Fake.discovery` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.yes` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.OAuth.readUser` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.OAuth.Fake.userApi` | tested | `Tests/OAuth.lean` |
| `Testing.OAuth.Fake.client` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.b64s` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.nowSeconds` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.mint` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.userJson` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.OAuth.emailsJson` | tested | `Tests/OAuth.lean`, `Tests/Testing.lean`, `Tests/TutorialWeb.lean` and others |
| `Testing.OAuth.Fake.take` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.user?` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.handle` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.makeKeys` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.start` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.stop` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.Fake.approve` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Testing.OAuth.signIn` | tested | `Tests/OAuth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |

## `Lanes/Testing/Run.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.Kind.label` | checked | `Tests/Testing.lean` |
| `Testing.Status.label` | checked | `Tests/Testing.lean` |
| `Testing.Status.ofVerdict` | checked | `Tests/Testing.lean` |
| `Testing.Result.ofBool` | checked | `Tests/Testing.lean` |
| `Testing.Result.tests` | checked | `Tests/Testing.lean` |
| `Testing.Result.check` | checked | `Tests/Testing.lean` |
| `Testing.Result.toJson` | checked | `Tests/Testing.lean` |
| `Testing.count` | checked | `Tests/Testing.lean` |
| `Testing.exitCode` | checked | `Tests/Testing.lean` |
| `Testing.toJson` | checked | `Tests/Testing.lean` |
| `Testing.line` | checked | `Tests/Testing.lean` |
| `Testing.render` | checked | `Tests/Testing.lean` |
| `Testing.wantsJson` | checked | `Tests/Testing.lean` |
| `Testing.report` | checked | `Tests/Testing.lean` |
| `Testing.messages` | checked | `Tests/Testing.lean` |
| `Testing.build` | checked | `Tests/Testing.lean` |

## `Lanes/Testing/S3.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Testing.S3.raw?` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.answer` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.failure` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.time?` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.decodePair` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.splitTarget` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.authField` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.verified` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.escapeKey` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.listXml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.range?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.serve` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.find?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.split` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.quoted` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.formParts` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.formBody` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and others |
| `Testing.S3.etag` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.uploaded` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.servePost` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.unquote` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.multipartEtag` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.xmlAnswer` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.listPartsXml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.completedXml` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.manifest?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.complete` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.serveMultipart` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.serveAll` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.Fake.start` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.Fake.object?` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` |
| `Testing.S3.Fake.holds` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` |
| `Testing.S3.Fake.keys` | tested | `Tests/S3.lean`, `Tests/Ship.lean` |
| `Testing.S3.Fake.refuse` | tested | `Tests/S3.lean`, `Tests/Ship.lean` |
| `Testing.S3.Fake.refusing` | tested | `Tests/S3.lean`, `Tests/Ship.lean` |
| `Testing.S3.Fake.stop` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Ship.lean` and others |
| `Testing.S3.follow` | tested | `Tests/OAuth.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `Testing.S3.code` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and others |
| `Testing.S3.postForm` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and others |

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
| `OAuth.DisplayName.allowed` | proved | through `OAuth.DisplayName.val`, `OAuth.Identity` and others: `OAuth.DisplayName.length_le`, `OAuth.IdToken.check_ok_iff` and others |
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
| `Jose.str?` | proved | through `Jose.Compact.read`, `Jose.readHeader`: `Jose.Compact.read_alg`, `Jose.readHeader_alg` and others |
| `Jose.bytes?` | proved | through `Jose.Compact.read`: `Jose.Compact.read_alg`, `Jose.verify_ok` and others |
| `Jose.Jwk.read?` | proved | through `Jose.Compact.read`: `Jose.Compact.read_alg`, `Jose.verify_ok` and others |
| `Jose.readKeys` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Jose.lean`, `Tests/Signature.lean` |
| `Jose.readHeader` | proved | `Jose.readHeader_alg` |
| `Jose.Compact.read` | proved | `Jose.Compact.read_alg`, `Jose.verify_ok`, `OAuth.IdToken.verify_accepted` |
| `Jose.candidates` | proved | through `Jose.verify`: `Jose.verify_ok` |
| `Jose.verify` | proved | `Jose.verify_ok` |

## `Lanes/Web/Auth/Login.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Auth.Attempts.codec` | proved | its type, `Codec` |
| `Auth.instCodableAttempts` | proved | its type, `Codable` |
| `Auth.Attempts.fail` | proved | `Auth.Attempts.bounded_fail`, `Auth.Attempts.fail_repeat`, `Auth.Attempts.locked_stays` and others |
| `Auth.Attempts.succeed` | proved | `Auth.Attempts.bounded_succeed`, `Auth.Attempts.locked_stays` |
| `Auth.Attempts.unlock` | spec | used only in statements |
| `Auth.Attempts.Bounded` | spec | a predicate |
| `Auth.Session.codec` | proved | its type, `Codec` |
| `Auth.instCodableSession` | proved | its type, `Codable` |
| `Auth.Session.expired` | proved | `Auth.Session.expired_mono`, `Auth.Sessions.accepts_iff` |
| `Auth.Sessions.codec` | proved | its type, `Codec` |
| `Auth.instCodableSessions` | proved | its type, `Codable` |
| `Auth.Sessions.ids` | proved | `Auth.Sessions.ids_starts`, `Auth.Sessions.length_close_le`, `Auth.Sessions.length_start_le` and others |
| `Auth.Sessions.at_s` | proved | through `Auth.Sessions.accepts`, `Auth.Sessions.start` and others: `Auth.Sessions.Ended.run`, `Auth.Sessions.accepts_iff` and others |
| `Auth.Sessions.sweep` | proved | `Auth.Sessions.sweep_ended` |
| `Auth.Sessions.start` | proved | `Auth.Sessions.ids_starts`, `Auth.Sessions.length_start_le`, `Auth.Sessions.live_open` and others |
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
| `OAuth.Used.claim` | proved | `OAuth.Used.claim_holds`, `OAuth.Used.claim_ok`, `OAuth.Used.claim_ok_holds` and others |
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

## `Lanes/Web/Auth/Password.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Auth.instDecidableEqDigest` | proved | its type, `Decidable` |
| `Auth.instHashableDigest` | tested | `Tests/Auth.lean` |
| `Auth.instReprDigest` | tested | `Tests/Auth.lean` |
| `Auth.Digest.codec` | proved | its type, `Codec` |
| `Auth.instCodableDigest` | proved | its type, `Codable` |
| `Auth.Digest.hex` | proved | through `Auth.Password.verify`, `Auth.Stored.text`: `Auth.Password.verify_hash`, `Auth.Password.verify_phc` and others |
| `Auth.Digest.ofHex?` | proved | through `Auth.Stored.read?`: `Auth.Stored.read?_text` |
| `Auth.Phc.cut` | proved | through `Auth.Phc.parse?`, `Auth.Stored.read?`: `Auth.Phc.parse?_encode`, `Auth.Stored.read?_text` |
| `Auth.Phc.after` | proved | through `Auth.Phc.parse?`, `Auth.Stored.read?`: `Auth.Phc.parse?_encode`, `Auth.Stored.read?_text` |
| `Auth.Phc.number?` | proved | through `Auth.Phc.parse?`, `Auth.Stored.read?`: `Auth.Phc.parse?_encode`, `Auth.Stored.read?_text` |
| `Auth.Phc.encode` | proved | `Auth.Phc.parse?_encode` |
| `Auth.Phc.parse?` | proved | `Auth.Phc.parse?_encode` |
| `Auth.Phc.check` | proved | through `Auth.Password.verify`: `Auth.Password.verify_hash`, `Auth.Password.verify_phc` and others |
| `Auth.Phc.instDecidableEq` | proved | its type, `Decidable` |
| `Auth.Phc.instRepr` | tested | `Tests/Auth.lean` |
| `Auth.Stored.text` | proved | `Auth.Stored.read?_text` |
| `Auth.Stored.read?` | proved | `Auth.Stored.read?_text` |
| `Auth.Stored.codec` | proved | its type, `Codec` |
| `Auth.Stored.instCodable` | proved | its type, `Codable` |
| `Auth.Password.salt` | proved | through `Auth.Password.verify`: `Auth.Password.verify_hash`, `Auth.Password.verify_phc` and others |
| `Auth.Password.digest` | proved | through `Auth.Password.verify`: `Auth.Password.verify_hash`, `Auth.Password.verify_phc` and others |
| `Auth.Password.hash` | proved | `Auth.Password.verify_hash` |
| `Auth.Password.current` | proved | through `Auth.Password.verify`: `Auth.Password.verify_hash`, `Auth.Password.verify_phc` and others |
| `Auth.Password.verify` | proved | `Auth.Password.verify_hash`, `Auth.Password.verify_phc`, `Auth.Password.verify_raw` |

## `Lanes/Web/Auth/Token.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Hmac.Key.of` | checked | `Tests/OAuth.lean` |
| `Hmac.Key.mac` | proved | `Auth.checkForm_other`, `Auth.verify_sign_other` |
| `Auth.Keys.of` | tested | `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` |
| `Auth.Keys.find?` | proved | `Auth.checkForm_iff`, `Auth.checkForm_other`, `Auth.verify_eq_some` and others |
| `Auth.Keys.rotate` | proved | `Auth.verify_rotate` |
| `Auth.message` | proved | `Auth.checkForm_other`, `Auth.message_inj`, `Auth.verify_sign_other` |
| `Auth.tag` | proved | through `Auth.checkForm`, `Auth.sign` and others: `Auth.checkForm_formToken`, `Auth.checkForm_iff` and others |
| `Auth.decimal` | proved | through `Auth.checkForm`, `Auth.sign` and others: `Auth.checkForm_formToken`, `Auth.checkForm_iff` and others |
| `Auth.head` | proved | `Auth.verify_sign_other` |
| `Auth.signWith` | proved | `Auth.verify_eq_some`, `Auth.verify_expired`, `Auth.verify_sign_other` |
| `Auth.sign` | proved | `Auth.verify_rotate`, `Auth.verify_sign` |
| `Auth.splitDot` | proved | through `Auth.checkForm`, `Auth.verify`: `Auth.checkForm_formToken`, `Auth.checkForm_iff` and others |
| `Auth.fields` | proved | through `Auth.checkForm`, `Auth.verify`: `Auth.checkForm_formToken`, `Auth.checkForm_iff` and others |
| `Auth.verify` | proved | `Auth.verify_eq_some`, `Auth.verify_expired`, `Auth.verify_rotate` and others |
| `Auth.formHead` | proved | `Auth.checkForm_other` |
| `Auth.formTokenWith` | proved | `Auth.checkForm_iff`, `Auth.checkForm_other` |
| `Auth.formToken` | proved | `Auth.checkForm_formToken` |
| `Auth.formId` | proved | through `Auth.checkForm`: `Auth.checkForm_formToken`, `Auth.checkForm_iff` and others |
| `Auth.checkForm` | proved | `Auth.checkForm_formToken`, `Auth.checkForm_iff`, `Auth.checkForm_other` |

## `Lanes/Web/Html/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Html.empty` | tested | `Tests/Html.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and others |
| `Html.instInhabited` | tested | `Tests/Html.lean` |
| `Html.escapeChar` | proved | through `Html.escape`, `Html.render`: `Html.escape_safe`, `Html.lex_render` and others |
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
| `Html.document` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `instToHtmlHtml` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `instToHtmlString` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `instToHtmlNat` | tested | `Tests/Html.lean` |
| `instToHtmlInt` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `instToHtmlList` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `instToHtmlArray` | tested | `Tests/Html.lean` |
| `instToHtmlOption` | tested | `Tests/Html.lean` |
| `instToAttrString` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `instToAttrListString` | tested | `Tests/Html.lean` |
| `instToAttrNat` | tested | `Tests/Html.lean` |
| `instToAttrInt` | tested | `Tests/Html.lean` |
| `instToAttrBool` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
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
| `Hx.target` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Hx.Swap.name` | tested | `Tests/Html.lean` |
| `Hx.swap` | tested | `Tests/Html.lean` |
| `Hx.eventName` | proved | `Hx.eventName_plain`, `Hx.mem_eventName` |
| `Hx.Trigger.render` | proved | `Hx.render_plain` |
| `Hx.trigger` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Hx.confirm` | tested | `Tests/Html.lean` |
| `Hx.boost` | tested | `Tests/Html.lean` |
| `Hx.pushUrl` | tested | `Tests/Html.lean` |
| `Hx.indicator` | tested | `Tests/Html.lean` |
| `Hx.events` | tested | `Tests/Html.lean` |
| `Http.Request.isHtmx` | tested | `Tests/Html.lean` |
| `Http.Response.trigger` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Response.hxRedirect` | tested | `Tests/Html.lean` |

## `Lanes/Web/Http/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.reprBody` | proved | through `Http.Request.field?`, `Http.Request.form`: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` |
| `Http.Method.codec` | proved | its type, `Codec` |
| `Http.Request.codec` | proved | its type, `Codec` |
| `Http.hexValue?` | proved | through `Http.Request.field?`, `Http.Request.form` and others: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` and others |
| `Http.percentDecodeBytes` | proved | through `Http.Request.field?`, `Http.Request.form` and others: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` and others |
| `Http.percentDecode` | proved | `Http.percentDecode_percentEncode` |
| `Http.hexDigit` | proved | through `Http.encodeForm`, `Http.percentEncode`: `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` and others |
| `Http.unreserved` | proved | through `Http.encodeForm`, `Http.percentEncode`: `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` and others |
| `Http.percentEncodeByte` | proved | through `Http.encodeForm`, `Http.percentEncode`: `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` and others |
| `Http.percentEncode` | proved | `Http.percentDecode_percentEncode`, `Http.percentEncode_plain` |
| `Http.parseForm` | proved | `Http.parseForm_encodeForm` |
| `Http.encodeForm` | proved | `Http.Request.form_encodeForm`, `Http.parseForm_encodeForm` |
| `Http.Request.param?` | spec | used only in statements |
| `Http.Request.header?` | proved | `Http.Conn.respond_opens`, `Http.Request.header?_eq_lookup`, `Http.Request.sameOrigin_iff` and others |
| `Http.Request.text?` | proved | through `Http.Request.field?`, `Http.Request.form`: `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` |
| `Http.Request.form` | proved | `Http.Request.field?_eq_lookup`, `Http.Request.form_encodeForm` |
| `Http.Request.field?` | proved | `Http.Request.field?_eq_lookup` |
| `Http.Response.ofText` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean`, `Tests/HttpConn.lean` and others |
| `Http.Response.text` | checked | `Tests/Fronted.lean`, `Tests/Gate.lean`, `Tests/HttpConn.lean` and others |
| `Http.Response.html` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Response.json` | tested | `Tests/Html.lean` |
| `Http.Response.empty` | tested | `Tests/Auth.lean`, `Tests/Html.lean` |
| `Http.Response.redirect` | checked | `Tests/SharedCache.lean` |
| `Http.Response.withHeader` | checked | `Tests/SharedCache.lean` |

## `Lanes/Web/Http/Conn.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Conn.closing` | proved | through `Http.Conn.answer`, `Http.Conn.encode` and others: `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` and others |
| `Http.Conn.nosniff` | proved | through `Http.Conn.answer`, `Http.Conn.encode` and others: `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` and others |
| `Http.Conn.sendable` | proved | `Http.Conn.read_encode`, `Http.Conn.sendable_writable` |
| `Http.Conn.encode` | proved | `Http.Conn.answer_waiting`, `Http.Conn.read_encode` |
| `Http.Conn.refusal` | proved | through `Http.Conn.pump`, `Http.Conn.run` and others: `Http.Conn.pump_piece`, `Http.Conn.run_buffer` and others |
| `Http.Conn.timeout` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.continueWire` | proved | through `Http.Conn.pump`, `Http.Conn.run` and others: `Http.Conn.pump_piece`, `Http.Conn.run_buffer` and others |
| `Http.Conn.streamed` | proved | `Http.Conn.read_streamed` |
| `Http.Conn.streamable` | proved | `Http.Conn.read_streamed`, `Http.Conn.respond_opens` |
| `Http.Conn.streamHead` | proved | `Http.Conn.read_streamed`, `Http.Conn.respond_opens` |
| `Http.Conn.lastChunk` | proved | `Http.Conn.flushStream_ended`, `Http.Conn.read_streamed` |
| `Http.Conn.heartbeatChunk` | proved | `Http.Conn.flushStream_going` |
| `Http.Conn.next` | proved | `Http.Conn.run_submits` |
| `Http.Conn.room` | proved | `Http.Conn.wantsInput_room` |
| `Http.Conn.wantsInput` | proved | `Http.Conn.wantsInput_room` |
| `Http.Conn.deadline` | proved | `Http.Conn.step_tick` |
| `Http.Conn.settle` | proved | through `Http.Conn.pump`, `Http.Conn.run` and others: `Http.Conn.pump_piece`, `Http.Conn.run_buffer` and others |
| `Http.Conn.waitMore` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.streamHead?` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.Inflow.start` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.begin` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.take` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.flushSlots` | proved | through `Http.Conn.flushStream`, `Http.Conn.run` and others: `Http.Conn.flushStream_ended`, `Http.Conn.flushStream_going` and others |
| `Http.Conn.flush` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.finish` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.Inflow.next` | proved | through `Http.Conn.Inflow.gather`, `Http.Conn.run` and others: `Http.Conn.gather_length`, `Http.Conn.pump_piece` and others |
| `Http.Conn.Inflow.gather` | proved | `Http.Conn.gather_length`, `Http.Conn.pump_piece` |
| `Http.Conn.Slot.isOpened` | proved | through `Http.Conn.answer`, `Http.Conn.flushStream` and others: `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` and others |
| `Http.Conn.pump` | proved | `Http.Conn.pump_piece` |
| `Http.Conn.took` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.respond` | proved | `Http.Conn.respond_ignored`, `Http.Conn.respond_opens` |
| `Http.Conn.Outflow.accept` | proved | through `Http.Conn.flushStream`, `Http.Conn.pulled` and others: `Http.Conn.flushStream_ended`, `Http.Conn.flushStream_going` and others |
| `Http.Conn.pulled` | proved | `Http.Conn.pulled_ignored`, `Http.Conn.pulled_large`, `Http.Conn.pulled_part` |
| `Http.Conn.flushStream` | proved | `Http.Conn.flushStream_ended`, `Http.Conn.flushStream_going` |
| `Http.Conn.earlier` | tested | `Tests/Loopback.lean` |
| `Http.Conn.wakeAt` | tested | `Tests/Loopback.lean` |
| `Http.Conn.drain` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.advance` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.Slot.stop` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.quiet` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.answer` | proved | `Http.Conn.answer_ignored`, `Http.Conn.answer_waiting` |
| `Http.Conn.receive` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.expire` | proved | through `Http.Conn.run`, `Http.Conn.step`: `Http.Conn.run_buffer`, `Http.Conn.run_slots` and others |
| `Http.Conn.step` | proved | `Http.Conn.step_closed`, `Http.Conn.step_notReading`, `Http.Conn.step_reading` and others |
| `Http.Conn.run` | proved | `Http.Conn.run_buffer`, `Http.Conn.run_slots`, `Http.Conn.run_submits` and others |
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
| `Http.trimBlank` | proved | through `Http.parseCookies`, `Http.readSetCookie`: `Http.parseCookies_cookieHeader`, `Http.readSetCookie_header` and others |
| `Http.parseCookie` | proved | through `Http.parseCookies`: `Http.parseCookies_cookieHeader` |
| `Http.parseCookies` | proved | `Http.parseCookies_cookieHeader` |
| `Http.Request.cookies` | tested | `Tests/Auth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and others |
| `Http.Request.cookie?` | tested | `Tests/Auth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and others |
| `Http.Request.sameOrigin` | proved | `Http.Request.sameOrigin_iff` |
| `Http.Request.bodyWithin` | spec | used only in statements |
| `Http.hostCookie` | tested | `Tests/Auth.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and others |
| `Http.Response.setCookie` | proved | `Http.setCookie_read` |
| `Http.Response.clearCookie` | tested | `Tests/Auth.lean` |
| `Http.Response.noStore` | checked | `Tests/SharedCache.lean` |
| `Http.Response.noFraming` | tested | `Tests/Html.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and others |

## `Lanes/Web/Http/CookieSound.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.readSetCookie` | spec | used only in statements |
| `Http.cookieHeader` | spec | used only in statements |

## `Lanes/Web/Http/Front.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.gateSig` | proved | `Http.Gate.always_up`, `Http.Gate.answered_le_handled`, `Http.Gate.answered_of_leaves` and others |
| `Http.gateActor` | proved | `Http.gateActor_bounded` |
| `Http.gateSystem` | proved | `Http.Gate.always_up`, `Http.Gate.answered_le_handled`, `Http.Gate.answered_of_leaves` and others |
| `Http.frontWiring` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and others |
| `Http.frontedSig` | proved | `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup`, `Http.fronted_arrival_answered` and others |
| `Http.frontedInput` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and others |
| `Http.frontedOutput` | proved | through `Http.fronted`, `Http.served`: `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup` and others |
| `Http.fronted` | proved | `Http.fronted_answered_le_arrived`, `Http.fronted_answered_nodup`, `Http.fronted_arrival_answered` and others |
| `Http.servedSig` | proved | `Http.kernel_served_answered_le_arrived`, `Http.served_answered_le_arrived`, `Http.served_answered_nodup` and others |
| `Http.served` | proved | `Http.kernel_served_answered_le_arrived`, `Http.served_answered_le_arrived`, `Http.served_answered_nodup` and others |
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

## `Lanes/Web/Http/JournalName.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.journalName` | tested | `Tests/Web.lean` |
| `Http.gateOf` | tested | `Tests/Web.lean` |
| `Http.formerGate` | tested | `Tests/Web.lean` |
| `Http.regate` | tested | `Tests/Web.lean` |
| `Http.regateUpgrade` | tested | `Tests/Web.lean` |

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
| `Http.Ops.route?` | proved | `Http.Ops.route?_default`, `Http.Ops.route?_hidden`, `Http.Ops.route?_metrics` and others |
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
| `Http.matchAt` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.find` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.pieces` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.Limits.message_max` | proved | `Http.Request.read_done`, `Http.Request.read_more` |
| `Http.Request.elements` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.version?` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.method?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.pchar` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.targetChar` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.hostChar` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.segments?` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.queryPart?` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.pair?` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.query?` | proved | through `Http.Request.read`, `Http.Request.readHead` and others: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.target?` | proved | `Http.Route.link_target`, `Http.Route.match?_target`, `Http.dispatch_link` and others |
| `Http.Request.fieldLine?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.host?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.tabbedFraming` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.framing?` | proved | through `Http.Request.read`, `Http.Request.readHead`: `Http.Conn.step_submit_read`, `Http.Request.readHead_headWire` and others |
| `Http.Request.parseHead` | proved | `Http.Request.readHead_headWire` |
| `Http.Request.readHead` | proved | `Http.Request.readHead_headWire`, `Http.Request.read_badChunkSize` |
| `Http.Request.chunkSize` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and others |
| `Http.Request.chunks` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and others |
| `Http.Request.Head.close` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and others |
| `Http.Request.Head.expectsContinue` | tested | `Tests/ReadRequest.lean` |
| `Http.Request.Head.incoming` | proved | through `Http.Request.read`: `Http.Conn.step_submit_read`, `Http.Request.read_append` and others |
| `Http.Request.read` | proved | `Http.Conn.step_submit_read`, `Http.Request.read_append`, `Http.Request.read_badChunkSize` and others |

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
| `Http.Path.seg` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Path.slug` | tested | `Tests/Html.lean`, `Tests/Loopback.lean`, `Tests/TutorialWeb.lean` and others |
| `Http.Path.nat` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Path.root` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Path.append` | tested | `Tests/Html.lean`, `Tests/TutorialWeb.lean`, `Tests/TutorialWeb/EndToEnd.lean` and others |
| `Http.Path.pre` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Route.get` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
| `Http.Route.post` | tested | `Tests/Fixtures/BankWeb.lean`, `Tests/Fronted.lean`, `Tests/Html.lean` and others |
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
| `Http.SharedCache.directives` | proved | through `Http.SharedCache.leaks`, `Http.SharedCache.outside` and others: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_reuses` and others |
| `Http.SharedCache.says` | proved | `Http.SharedCache.serve_storable` |
| `Http.SharedCache.vary` | proved | `Http.SharedCache.serve_reuses` |
| `Http.SharedCache.explicitlyFresh` | proved | through `Http.SharedCache.leaks`, `Http.SharedCache.outside`: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_storable` |
| `Http.SharedCache.heuristic` | proved | through `Http.SharedCache.leaks`, `Http.SharedCache.outside`: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_storable` |
| `Http.SharedCache.storable` | proved | `Http.SharedCache.serve_storable` |
| `Http.SharedCache.reuses` | proved | through `Http.SharedCache.Store.serve?`, `Http.SharedCache.leaks`: `Http.SharedCache.serve_of_leaks`, `Http.SharedCache.serve_reuses` and others |
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
| `SigV4.blank` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and others |
| `SigV4.squeeze` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and others |
| `SigV4.trimValue` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and others |
| `SigV4.insertHeader` | proved | through `SigV4.canonicalHeaders`, `SigV4.sign`: `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted` and others |
| `SigV4.canonicalHeaders` | proved | `SigV4.canonicalHeaders_lower`, `SigV4.canonicalHeaders_sorted`, `SigV4.mem_canonicalHeaders` |
| `SigV4.signedHeaders` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.canonicalRequest` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.algorithm` | proved | through `SigV4.sign`: `SigV4.target_sign` |
| `SigV4.unsignedPayload` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/SigV4.lean`, `Tests/S3.lean` and others |
| `SigV4.payloadHash` | tested | `Tests/Oracle/All.lean`, `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean` and others |
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
| `Http.Waiting.start` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and others |
| `Http.Waiting.wait` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and others |
| `Http.Waiting.releases` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and others |
| `Http.Waiting.release` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and others |
| `Http.Waiting.answer` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and others |
| `Http.Waiting.drain` | proved | through `Http.Waiting.exec`: `Http.Waiting.exec_answered`, `Http.Waiting.exec_drain` and others |
| `Http.Waiting.Trace.apply` | spec | used only in statements |
| `Http.Waiting.exec` | spec | used only in statements |

## `Lanes/Web/Http/Wire.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.frames` | proved | `Http.Request.fields_framing` |
| `Http.Request.target` | proved | `Http.Request.target_visible`, `SigV4.target_sign` |
| `Http.Request.kept` | proved | through `Http.Request.fields`, `Http.Request.wire` and others: `Http.Request.fields_framing`, `Http.Request.fields_token` and others |
| `Http.Request.fields` | proved | `Http.Request.fields_framing`, `Http.Request.fields_token` |
| `Http.Request.head` | proved | `Http.Request.head_plain` |
| `Http.Request.wire` | proved | `Http.Request.head_plain`, `Http.Request.read_wire`, `Http.Request.read_wire_extract` |
| `Http.Request.headOnly` | proved | `Http.Request.headOnly_plain` |
| `Http.Request.wireHead` | proved | `Http.Request.headOnly_plain` |
| `Http.Reading.map` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.headEnd` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.crlf` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.skip` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.hex` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.chunkSizeDigits_max` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.chunkExtensionBytes_max` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.sizeLineEnd` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.chunkHead` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.dechunk` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.decimal?` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.splitLines` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.statusLine?` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.headerLine?` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.head?` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.framing?` | proved | through `Http.Response.read`, `Http.Response.readHead` and others: `Http.Conn.read_encode`, `Http.Conn.read_streamed` and others |
| `Http.readFrom` | proved | `Http.Response.read_some` |
| `Http.Response.read` | proved | `Http.Conn.read_encode`, `Http.Conn.read_streamed`, `Http.Response.read_append` and others |
| `Http.readHeadFrom` | proved | through `Http.Response.readHead`: `Http.Response.readHead_ended` |
| `Http.Response.readHead` | proved | `Http.Response.readHead_ended` |
| `Http.Response.parse` | trusted | TRUSTED.md: The HTTP wire format |

## `Lanes/Web/Http/WireSpec.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.Response.kept` | proved | through `Http.Response.writable`: `Http.Conn.sendable_writable`, `Http.Response.read_wire` and others |
| `Http.Response.lowered` | proved | `Http.Conn.read_encode`, `Http.Conn.read_streamed`, `Http.Response.read_wire` and others |
| `Http.Response.writable` | proved | `Http.Conn.sendable_writable`, `Http.Response.read_wire`, `Http.Response.read_wireAfter` and others |
| `Http.Response.headWire` | proved | through `Http.Response.wire`, `Http.Response.wireAfter` and others: `Http.Response.read_wire`, `Http.Response.read_wireAfter` and others |
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
| `Http.Client.Call.keyed` | trusted | TRUSTED.md: The HTTP client adapter's handler |
| `Http.Client.handlerKeyed` | trusted | TRUSTED.md: The HTTP client adapter's handler |

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
| `S3.backup` | trusted | TRUSTED.md: The S3 client's IO |

## `Lanes/Web/IO/Server.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Http.serveWith` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.serveFronted` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.ServerConfig.journalName` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.serve` | trusted | TRUSTED.md: The HTTP adapter's IO |
| `Http.restoreJournal` | trusted | TRUSTED.md: The HTTP adapter's IO |
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
| `Tls.isAddress` | trusted | TRUSTED.md: The TLS client |
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

## `Lanes/Web/S3/Backup.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.backupPut` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Backup.lean` |
| `S3.shipped` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Backup.lean`, `Tests/Ship.lean` |
| `S3.listedPage` | tested | `Tests/Ship.lean` |

## `Lanes/Web/S3/Basic.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Endpoint.aws` | tested | `Tests/S3.lean` |
| `S3.Key.of?` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Backup.lean` and others |
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
| `S3.Bucket.host` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and others |
| `S3.Bucket.path` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and others |
| `S3.Bucket.scope` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Backup.lean` and others |
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
| `S3.Op.modelled` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `S3.Answer.modelled` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3.lean`, `Tests/Oracle/Service/S3Post.lean` and others |
| `S3.presign` | tested | `Tests/S3.lean`, `Tests/S3Upload.lean`, `Tests/Testing.lean` and others |
| `S3.presignPart` | tested | `Tests/S3Upload.lean` |

## `Lanes/Web/S3/Multipart.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `S3.Multipart.minPart_bytes` | proved | `S3.Multipart.Plan.range_full` |
| `S3.Multipart.maxPart_bytes` | proved | `S3.Multipart.Plan.range_full` |
| `S3.Multipart.maxParts` | proved | `S3.Multipart.Plan.count_le` |
| `S3.Multipart.maxObject_bytes` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Multipart.lean`, `Tests/S3Upload.lean` |
| `S3.Multipart.Plan.count` | proved | `S3.Multipart.Plan.count_le`, `S3.Multipart.Plan.range_full`, `S3.Multipart.Plan.range_last` and others |
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
| `S3.Post.Condition.json` | proved | through `S3.Post.Condition.holds`, `S3.Post.Document.encode` and others: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and others |
| `S3.Post.field?` | proved | through `S3.Post.decode?`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and others |
| `S3.Post.Condition.read?` | proved | through `S3.Post.decode?`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and others |
| `S3.Post.Document.json` | proved | through `S3.Post.Document.encode`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and others |
| `S3.Post.Document.read?` | proved | through `S3.Post.decode?`: `S3.Post.admitted_bounded`, `S3.Post.decode?_encode` and others |
| `S3.Post.Document.encode` | proved | `S3.Post.decode?_encode` |
| `S3.Post.decode?` | proved | `S3.Post.admitted_bounded`, `S3.Post.decode?_encode`, `S3.Post.form_policy` |
| `S3.Post.signature` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.lookup` | proved | through `S3.Post.Condition.holds`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and others |
| `S3.Post.Condition.holds` | proved | `S3.Post.check_holds` |
| `S3.Post.Condition.field?` | proved | through `S3.Post.check`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and others |
| `S3.Post.exempt` | proved | through `S3.Post.check`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.check_holds` and others |
| `S3.Post.check` | proved | `S3.Post.admitted_bounded`, `S3.Post.check_holds` |
| `S3.Post.KeyRule.condition` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.KeyRule.field` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.maxObject_bytes` | proved | through `S3.Post.Length.max`, `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.SuccessStatus.code` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.expiration` | proved | `S3.Post.expiration_parse` |
| `S3.Post.credential` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.chosen` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.signer` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.eqs` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.conditions` | proved | through `S3.Post.form`: `S3.Post.admitted_bounded`, `S3.Post.form_policy` |
| `S3.Post.document` | proved | `S3.Post.form_policy` |
| `S3.Post.Form.fields` | tested | `Tests/Oracle/Service/All.lean`, `Tests/Oracle/Service/S3Post.lean`, `Tests/S3Upload.lean` and others |
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

## `LanesCli/Changelog.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Changelog.changesDir` | none |  |
| `Cli.Changelog.sections` | tested | `Tests/Lint.lean` |
| `Cli.Changelog.parse` | tested | `Tests/Lint.lean` |
| `Cli.Changelog.files` | none |  |
| `Cli.Changelog.read` | none |  |
| `Cli.Changelog.assemble` | tested | `Tests/Lint.lean` |
| `Cli.Changelog.unreleasedHeading` | tested | `Tests/Lint.lean` |
| `Cli.Changelog.strayEntries` | none |  |
| `Cli.Changelog.check` | none |  |
| `Cli.Changelog.insertRelease` | tested | `Tests/Lint.lean` |
| `Cli.Changelog.run` | none |  |

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
| `Cli.Generated.sortStrings` | tested | `Tests/Lint.lean` |
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
| `Cli.Generated.countless` | tested | `Tests/Lint.lean` |
| `Cli.Generated.trustedPlan` | none |  |
| `Cli.Generated.trustedTotal` | none |  |
| `Cli.Generated.decisionsDir` | none |  |
| `Cli.Generated.parseDecisionName` | none |  |
| `Cli.Generated.parseHeading` | none |  |
| `Cli.Generated.readDecisions` | none |  |
| `Cli.Generated.indexLine` | tested | `Tests/Lint.lean` |
| `Cli.Generated.indexText` | tested | `Tests/Lint.lean` |
| `Cli.Generated.textFiles` | none |  |
| `Cli.Generated.numberPlan` | none |  |
| `Cli.Generated.decisionsPlan` | none |  |
| `Cli.Generated.statusDir` | none |  |
| `Cli.Generated.sectionsMarker?` | none |  |
| `Cli.Generated.generatedNote` | tested | `Tests/Lint.lean` |
| `Cli.Generated.sortItems` | tested | `Tests/Lint.lean` |
| `Cli.Generated.trimFragment` | none |  |
| `Cli.Generated.fragmentProblems` | none |  |
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
| `Cli.Inventory.isBound` | none |  |
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

## `LanesCli/Journal.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.Journal.values` | none |  |
| `Cli.Journal.schemaProgram` | none |  |
| `Cli.Journal.usage` | none |  |
| `Cli.Journal.run` | none |  |

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
| `Cli.Lint.jsonString` | tested | `Tests/Lint.lean` |
| `Cli.Lint.Finding.kind` | tested | `Tests/Lint.lean` |
| `Cli.Lint.Finding.json` | tested | `Tests/Lint.lean` |
| `Cli.Lint.Report.json` | tested | `Tests/Lint.lean` |
| `Cli.Lint.run` | none |  |

## `LanesCli/Main.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `usage` | none |  |
| `flag?` | none |  |
| `stats` | none |  |
| `checkJson` | none |  |
| `main` | none |  |

## `LanesCli/New.lean`

| Definition | Status | Evidence |
| --- | --- | --- |
| `Cli.New.Source.toToml` | tested | `Tests/New.lean` |
| `Cli.New.repository` | tested | `Tests/New.lean` |
| `Cli.New.pinned` | tested | `Tests/New.lean` |
| `Cli.New.warnings` | tested | `Tests/New.lean` |
| `Cli.New.ofCheckout` | none |  |
| `Cli.New.moduleName` | tested | `Tests/New.lean` |
| `Cli.New.validName` | none |  |
| `Cli.New.files` | tested | `Tests/New.lean` |
| `Cli.New.fill` | tested | `Tests/New.lean` |
| `Cli.New.run` | none |  |
