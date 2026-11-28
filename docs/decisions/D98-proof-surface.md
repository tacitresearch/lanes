# D98. A small proof surface, and each property written once (a proposal)

Status: Accepted

*A proposal for tacitresearch/lanes#100, part C of the design direction (#93). It moves no code.
The owner agreed to the headline on 2026-11-27; the parts below are for the owner to decide.
Every count and line number was checked against `main` at `cb53031` on 2026-11-28.*

Applications are going to prove theorems against Lanes in their own repositories. Today a proof
may unfold any definition of the semantics, a check and a proof state the same property in two
texts, "implements" says nothing about answering, a bounded pass exits 0, and a spec cannot say
"unavailable". Each of these is cheap to fix now and expensive once other people's proofs rest
on it. This decision proposes seven changes:

1. A small, named **proof surface**. Apps prove against it; the bodies behind it are hidden, and
   every module is experimental unless it says it is stable.
2. **Each property written once**, as a `Prop`. Its check is derived through `Decidable`, with a
   theorem that a pass means the `Prop` holds of every state checked.
3. A **standard liveness check**: once nothing is enabled, every input has been answered. And a
   standard statement, `System.ImplementsLive`.
4. **Honest results**: a bounded pass has its own exit code. #102 does this.
5. **Specs that can fail**: a spec may answer "unavailable" or "may have taken effect", so the
   gate's `503` and `504` are inside it. Paired with liveness when the system is not
   overloaded, so that failing always is not enough.
6. **Named sets of environment assumptions**, shared with the runtime contract (#86).
7. **Timers' delays**, as an opt-in constraint on runs that keeps every existing proof true.

## What is true today

The deep sweep of the checker (2026-11-27) made the claims below. Each was checked again.

| Claim | Checked |
|---|---|
| Most library files expose every body | True: 186 of the 220 files of `Lanes/` open `@[expose] public section`; `@[no_expose]` appears 13 times; nothing is `@[irreducible]`. The sweep said 180 of 213; the library has grown. |
| Every module is stable | True: `docs/RELEASING.md`, "Stability": "a module without that line is stable". No file has a `Stability:` line. |
| Example proofs unfold the semantics | True, counted below: 44 tactic calls in 16 files of 8 of the 13 apps with proofs. `.net` appears 96 times in example proofs. |
| A property is checked as a `Bool` and proved as a `Prop`, with nothing between them | Partly out of date. Raft now bridges them by hand: 11 theorems such as `RaftKV.electionSafety_invariant` (`examples/raft-kv/RaftKV/Proofs/Election.lean:258`) prove the `Bool` from the `Prop`, by `grind`. Seven auxiliary checks (`termsSorted`, `candidatesBehind`, `requestsCurrent`, `votesKnown`, `matchedHeld`, `acksHeld`, `appendsCut`) have no bridge. Rookery's checks are a third text (`judge`, `examples/rookery/Check.lean`). The point stands: two texts, and a hand proof between them when there is one. |
| The checker has no step properties | True: `Check.Property` is `always` or `sometimes` of `S → Bool` (`Lanes/Check/Search.lean:53`). The web tutorial checks "only its uploader deletes a file" by reading the driver (`docs/TUTORIAL-WEB.md:305-307`). |
| `Implements` is safety only | True: weak simulation (`Lanes/Semantics/Refinement.lean`, `System.Implements` in `Lanes/Semantics/Service.lean:150`). CLAIMS: "a cluster that answers nothing refines its spec too". |
| The deadlock check is off by default | True (`Lanes/Check/Search.lean:84`). New: a "deadlock" includes a state whose successors all fall outside the constraint (`successors`, `Lanes/Check/Search.lean:280`; `Check.search_deadlock`, `Lanes/Check/SearchSound.lean:1008`). Part 3 depends on this. |
| `Report.ok` ignores completeness | True, now at `Lanes/Check/Search.lean:144`. The template exits on `report.ok` (`templates/app/Check.lean.tmpl`, last line). |
| The spec is one deterministic `Service` | True (`Lanes/Core/Service.lean`). The gate answers `503` and `504` (`Lanes/Web/Http/Gate.lean:76,80`). |
| Timers ignore their delay | True: `.after _ msg` (`Lanes/Core/World.lean:150`); any pending timer may fire (`:203`). The kernel arms at `clock_ms + delay_ms` and re-arms a pending timer with the new deadline (`Kernel.perform`, `Lanes/Runtime/Kernel.lean:89-97`). |
| Each theorem picks its own environment premises | True, listed in part 6. |

## 1. A small, named proof surface

### 1.1 What apps prove against

The surface is the list below. An app's proof may name these and unfold its own definitions.
It does not unfold anything else of Lanes. Most of the list exists; *new* marks what is missing.

| Concern | Definitions | Lemmas and rules |
|---|---|---|
| Systems and actors | `Signature`, `Actor` (`init`, `step`, `recover`), `Effect` (`send`, `emit`, `after`, `cancel`, `stop`), `System` (`actor`, `accept`, `boot`), `Envelope` | `Effect.sends`, `Effect.armed`, `Effect.emits`, `Effect.retime` and their `@[simp]` lemmas (`Lanes/Core/Run.lean`); *new* `@[simp]` equations of `Effect.isStop` |
| A state, read but not built | `SysState` read through `state`, `up`, `timers`, `outbox`, and the messages on a link, `c.onLink src dst` (today `linkMsgs src dst c.net`, `Lanes/Semantics/Link.lean`, which imports only `Lanes.Core.Run` and can move to `Lanes/Core/`) | the `linkMsgs` lemmas; *new* projections of `SysState.blank` and `SysState.init` (below) |
| Events and runs | `Event`, `Visible`, `Event.timed`, `SysState.init`, `SysState.step`, `SysState.run`, `System.Reachable`, `System.Run` | one characterisation per event, `SysState.step_input` … `step_start` (`Lanes/Core/Step.lean`), restated with named results (1.2); `SysState.settle_eq`, `SysState.startActor_eq_started` (`Lanes/Core/Run.lean`); `SysState.run_append`; `System.Run.step_some`, `step_none`, `reachable` |
| Invariants | `System.Invariant`, `System.Inductive`, `Actor.Invariant`, `Actor.Inductive` | `System.Inductive.invariant`; `actor_invariant` and `System.invariant_of_actor` (`Lanes/Proof/Lift.lean`); `System.Monotone` with `and`, `and_net`, `and_state`, `of_iff`, `invariant` (`Lanes/Proof/Monotone.lean`); `System.withGhost`, `System.withPast`, `System.Invariant.of_ghost`; `SysState.Loses`; `System.traced`; `System.Emits.outputs` |
| Refinement | `Service`, `Service.spec`, `System.Implements`, `Account` | `System.Implements.history`, `Refines.of_map`, `Account.implements`, `Server.implements` |
| Fairness and liveness | `System.Run.Fair`, `System.LeadsTo`; *new* `System.ImplementsLive` (part 3) | `Run.Fair.delivered`, `Fair.handled`, `Fair.output_taken`, `LeadsTo.ensures_of_invariant`, `LeadsTo.trans`, `LeadsTo.induction` (`Lanes/Semantics/Liveness.lean`) |
| Environment | `EnvModel`, `Link`, `EnvModel.Faultless`; *new* the bundles of part 6 | the implications between bundles (part 6) |
| The outside | `Outside` | `Outside.allows`, `Outside.after_induction`, `Outside.Beside` |
| The checker | `Check.Property`; *new* `Check.invariant`, `Check.witness` (part 2) | `Check.system_sound_of_respects`, `Check.refines_traces`; *new* `Check.invariant_of_pass` |

Behind the surface, and hidden: how an event is performed (`SysState.perform`, `performAll`,
`settle`, `handle`, `down`, `startActor`), when one is enabled (`deliverable`, `hasMail`), the
bodies of `SysState.blank`, `SysState.init` and `SysState.step`, and the bodies of behaviours'
actors (`Server.actor`, which the template's `actor_invariant [Server.actor, service]` unfolds
today; it gets a `@[simp]` step lemma instead).

The representation of the network is the part most likely to change: a list today, oldest first,
with `erase` of the first occurrence (`Lanes/Core/World.lean:83`, `:193`). Per-link queues or a
multiset would suit the checker better. The view `onLink` is what survives that change: the
messages on one link, in order where the link is ordered. It is also what the checker keeps when
it merges states (`NetEquiv`, `Lanes/Proof/Equiv.lean:33`), so a property that reads the network
only through `onLink`, and through membership on unordered links, gives one verdict on merged
states. That makes part 2's soundness premise a lemma instead of a per-app proof.

### 1.2 What the examples' proofs unfold today

Counted over the 57 files of `examples/*/…Proofs*` (12,305 lines): every `simp`, `simpa`,
`simp_all`, `dsimp`, `rw` and `unfold` whose list names a `SysState` definition of the semantics.
There are 44 such tactic calls, in 16 files of 8 apps (bank, election, kv-cache, ledger,
payments, raft-kv, rookery, watchdog). By name, with the lemma that would replace each:

| Unfolded | Calls | Apps | Why it is unfolded | Replaced by |
|---|---|---|---|---|
| `SysState.blank` | 32 | all 8 | `Monotone.blank`, an inductive invariant's start, `Account`'s start are stated of `blank` | *new* `@[simp]` `blank_state`, `blank_up`, `blank_onLink` (nothing in flight), `blank_timers`, `blank_outbox` |
| `SysState.init` | 14 | bank, kv-cache, ledger, rookery, watchdog | the start state of a refinement or an invariant | `init_induction` (`Lanes/Core/Step.lean:82`), `init_timers_of_not_mem_boot` (`Lanes/Semantics/FairRuns.lean:99`); *new* `init_eq_blank` for `boot = []`, `init_outbox` and `init_onLink` of actors whose `recover` sends and emits nothing |
| `SysState.settle` | 8 | bank, watchdog | what a step did | `settle_eq`, `settle_outbox_eq`, `settle_up_of_ne`, `settle_timers_of_ne`, `mem_net_settle` (exist); *new* `settle_state` |
| `SysState.handle` | 7 | bank, kv-cache, watchdog | the same | *new* `handle_eq`: `c.handle env i msg = c.settle env i ((sys.actor i).step (c.state i) msg)`, general (today only `Server.handle_eq` and the behaviours' own) |
| `SysState.perform` | 5 | bank, watchdog | the same | `performAll_eq` (exists); with `handle_eq` and `settle_eq` it is never needed |
| `SysState.startActor` | 4 | bank, kv-cache, watchdog | a restart | `startActor_eq_started` (exists) |
| `SysState.deliverable` | 3 | kv-cache, watchdog | which message may be delivered | *new* `deliverable_iff`: the first of `onLink` on an ordered link, a member otherwise |
| `SysState.down` | 3 | ledger | an actor stopping | `linkMsgs_down` (exists); *new* `down_state`, `down_outbox` |
| `SysState.performAll` | 2 | watchdog | | `performAll_eq` |
| `SysState.step`, `run`, `hasMail` | 1 each | kv-cache | a concrete run, the stale read, computed by `simp` | `run_cons` and the per-event lemmas: one rewrite per event. A concrete run costs more lines. |

The same lists also unfold `Effect.isStop` (15 calls, 5 apps) and `System.withGhost` and
`System.withPast` (19 calls, raft-kv and election). Both get `@[simp]` lemmas.

The representation shows in three more ways: `.net` 96 times in 8 apps, `{ c with net := … }`
24 times in 5 apps (bank, ledger, payments, raft-kv, watchdog), and `c.net.erase` 11 times in 4
(bank, ledger, raft-kv, rookery). Most of these restate the shapes of Lanes' own rules, which
are written over the representation:

- `Monotone.input` is stated of `{ c with net := c.net ++ [⟨none, …⟩] }`
  (`Lanes/Proof/Monotone.lean:255`), and `Monotone.blank` of `SysState.blank`;
- `step_deliver` gives `({ c with net := c.net.erase e }).handle env e.dst e.msg`
  (`Lanes/Core/Step.lean:102`);
- `Account`'s moves are stated of `({ c with net := c.net.erase e }).grow …`
  (`Lanes/Semantics/Account.lean:251`), and an account's value takes `c.net` itself.

So the first work is in Lanes, not in the apps: name the operations (`c.accepted x`, an input
put in flight; `c.taken e`, a message out of flight) and restate the rules with them. Then an app
never writes the record.

Inside the library, 32 files besides `Lanes/Core/World.lean` unfold these definitions, in 256
tactic calls (the most: `Lanes/Proof/JoinSound.lean` 43, `Lanes/Core/Run.lean` 20,
`Lanes/Runtime/ShardSound.lean` 17). They are the inside of the surface, and keep their access
through `import all` (1.3).

### 1.3 How to hide a body in Lean v4.37

Tested, not read: a two-module package on the pinned toolchain, `leanprover/lean4:v4.37.0-rc1`.
Module `A` defines `perform`; module `B` has `public import A` and tries to use it.

| How `A` declares it | `simp [perform]` in `B` | `unfold perform` in `B` | `rfl` through it in `B` | Compiled code in `B` |
|---|---|---|---|---|
| `def` in `@[expose] public section` | works | works | works | runs |
| `def` in a plain `public section` | refused: "Expected a definition with an exposed body" | fails | fails | runs |
| `@[no_expose] def` in an exposed section | refused | not tried | fails | runs |
| `@[irreducible] def`, exposed | **works** | **works** | fails | runs |
| `@[irreducible] def`, not exposed | refused | fails | fails | runs |
| any of these, with `import all A` in `B` | works | works | works | runs |

And:

- `@[irreducible]` does not hide a body. It stops only definitional unfolding; `simp [f]` and
  `unfold f` still see it. What hides is the module system: a body not exposed, by leaving
  `@[expose]` off or by `@[no_expose]`.
- Structure fields stay public when the bodies are hidden: `c.net` and `{ c with net := [] }`
  still work in `B`. A `private` field refuses both in `B`. A private constructor refuses
  `⟨…⟩` but still lets `B` read the fields.
- `decide` in `B` works through a `Decidable` instance of a predicate whose body is hidden: the
  instance's body is visible. `decide` on a hidden `Bool` function fails. A check runs compiled
  code, so the checker is not affected either way.
- A public theorem in `A` proved by `rfl` through a body `A` does not expose is refused ("This
  theorem is exported from the current module … must be exposed"). `by simp [f]` in `A` works.
  Lemmas that are `rfl` today need a tactic proof.
- `import all` must stand beside `public import`: `public import all A` is refused. Any module may
  write `import all`, so it is an escape hatch, not a wall. A lint should refuse `import all
  Lanes…` outside `Lanes/`. I did not test `import all` across packages.

So the proposal is: once the lemmas of 1.2 exist and the examples use them, take `@[expose]` off
the hidden definitions of `Lanes/Core/World.lean` (they move into a plain `public section`), and
give the 32 library files `import all Lanes.Core.World`. `SysState`'s fields stay public for now
(question 2).

### 1.4 Every module experimental by default

`docs/RELEASING.md` makes a module stable unless it says otherwise, and protects only names and
types. For a proof, a changed body breaks as surely as a changed type, if the proof unfolds it.
Proposed text for "Stability":

- A module is experimental unless its `/-! -/` header has the line `Stability: stable`.
- In a stable module, a change to an exposed body is a breaking change. A hidden body may
  change in any release.
- `lanes lint` checks the line (lint `stability`): its value is `stable` or `experimental`, and
  a stable module imports experimental modules only privately.

At the first release the stable modules are those of the surface: `Lanes/Core/Actor.lean`,
`System.lean`, `World.lean` (names and types; most bodies hidden), `Step.lean`, `Run.lean`,
`Lanes/Proof/Lift.lean`, `Monotone.lean`, `Ghost.lean`, `Past.lean`,
`Lanes/Semantics/Liveness.lean`, `Service.lean` and `Refinement.lean`. Everything else,
the checker included, starts experimental and is promoted by a pull request of its own.

## 2. Each property written once

### 2.1 The shape

The `Prop` is the source. It lives in a module that imports only `Std`, because the check is a
binary that must not link Mathlib (rule 1.6). The check is derived from it:

```lean
/-- The `always` check of `P`, through its `Decidable` instance. -/
def Check.invariant (name : String) (P : SysState sys → Prop) [DecidablePred P] :
    Check.Property (World sys D) :=
  .always name fun w => decide (P w.state)

/-- A complete PASS: `P` holds of every world the check reaches. -/
theorem Check.invariant_of_pass … (hfailure : (system sys sc props opts).failure = none)
    (hcomplete : (system sys sc props opts).complete = true)
    (hp : Check.invariant name P ∈ props) (hw : sc.Reachable sys opts.constraint w) :
    P w.state
```

`Check.invariant_of_pass` is `Check.system_sound_of_respects` followed by `of_decide_eq_true`.
Its premise that the property gives one verdict on merged states is discharged once, by
`Check.invariant_respects`, for every `P` that reads the network only through `onLink` (1.1).
`Check.witness name Q` is the `sometimes` beside it (rule 5.3). One instance is missing from the
library: `Decidable (∀ a : α, p a)` and `Decidable (∃ a, p a)` for an `Enum α`.

The convention: the theorem is `sys.Invariant env P` of the same `P`, and the `CLAIMS` row names
one `P`. Rule 5.1, check before you prove, is then about one statement.

Step properties come with it. A property of a transition, `A : SysState sys → Event σ →
SysState sys → Prop` with `DecidablePred`, is checked on each transition the search takes, and
proved as `∀ c ev c', sys.Reachable env c → c.step env ev = some c' → A c ev c'`. The web
tutorial's "only its uploader deletes a file" is one, and stops reading the driver. This needs
the search to give each transition to the properties; its soundness theorem is new.

### 2.2 What cannot be derived this way

- **Quantifiers over large types.** `∀ n : Nat`, `∀ k : K` for keys with no `Enum`: the `Prop`
  must be stated over what the state holds (`∀ x ∈ c.state i`), or the instance does not exist.
- **Statements about runs**, not states: refinement (`Implements`), and anything over a history
  (`Implements.history`'s `∃ acts cut`). Refinement already has its own derived check, the
  monitor, with its own theorem (`Check.refines_traces`).
- **Liveness** (`LeadsTo`, `ImplementsLive`): about infinite fair runs. Part 3's check is a
  bounded stand-in, not a derivation.
- **Invariants of a ghost system.** Raft's auxiliary invariants (`Votes`, `Logged`) are of
  `recording`, the system with history (`System.withPast`). The check runs the plain system.
  Only what `System.Invariant.of_ghost` brings down to the plain system can be checked.
- **Properties that tell merged states apart**: a `Prop` that reads the order of all messages
  (`c.net.head?`) or of the outbox is decidable, but a PASS of it is not sound. Writing against
  `onLink` avoids it.
- **Properties of the spec's functions for every configuration**, as rookery proves of
  `Board.handle`: a check sees one configuration.
- **A `Prop` stated in the proof layer's vocabulary** (Mathlib's `Multiset`, `Finset`): its
  instance is in a module the check cannot import.

### 2.3 On a real example: Raft's election safety

Today raft checks `electionSafety : Cluster → Bool` (`examples/raft-kv/RaftKV/Properties.lean:30`),
proves `election_safety`, a `Prop` over `role = .leader _`
(`examples/raft-kv/RaftKV/Proofs/Election.lean:237`), and bridges them with
`electionSafety_invariant` (`:258`), twelve lines that end in `grind`. A sketch of the same
property written once, not compiled:

```lean
-- RaftKV/Properties.lean: Std only, so the check can run it.
/-- At most one leader per term: two nodes that lead the same term are one node. -/
def ElectionSafe (c : Cluster N config machine) : Prop :=
  ∀ a b : N, isLeader (c.state a) = true → isLeader (c.state b) = true →
    (c.state a).term = (c.state b).term → a = b

instance : DecidablePred (ElectionSafe (N := N) (config := config) (machine := machine)) :=
  fun _ => by unfold ElectionSafe; infer_instance   -- `∀` over `Enum N`, the new instance

-- Check.lean
  Check.invariant "at most one leader per term" ElectionSafe,

-- RaftKV/Proofs/Election.lean
theorem election_safety (config : Config) (machine : Machine C R M) (env : EnvModel (sig N C R)) :
    (cluster N config machine).Invariant env ElectionSafe := by
  refine .of_ghost (.past _) fun c hc a b ha hb hterm => ?_
  exact (votes_monotone.invariant env c hc).2.leader_unique (p := (c.state a).1)
    (q := (c.state b).1) List.mem_cons_self List.mem_cons_self ha hb hterm

-- RaftKVProofs/Checked.lean: the PASS gives the same `Prop`.
  … : ElectionSafe w.state :=
    Check.invariant_of_pass … hfailure hcomplete (.tail _ (.head _)) hrun.reachable
```

`electionSafety_invariant` goes. So does this property's case in `props_respect`: it reads
only actor states. The proof is shorter, since `leader_unique` already takes `isLeader … = true`
and the `isLeader_iff` steps go. The other ten bridges go the same way.

## 3. A standard liveness check

### 3.1 The check

**Answered** means: the refinement monitor has a candidate with nothing pending and nothing in its
outbox (`Monitor.settled`, new; `Lanes/Check/Monitor.lean`). Every input took effect, in some
order the spec allows, and every output it produced was handed over. It needs the monitor, so
it applies to checks with `Service.monitored`, which the template has.

**Nothing enabled** needs a change first. Today a deadlock is a state with no successor
*within the constraint* (`successors` filters by `opts.constraint` before `expandWith` tests for
none; `Check.search_deadlock` states it so; the fingerprinted recheck does the same,
`Lanes/Check/Fingerprint.lean:201`). So turned on as it is, the check reports a state cut off
by the bounds, such as raft's `maxTerm`, as a deadlock. Split the two cases:

- **quiet**: the model has no successor at all. These are checked.
- **cut**: it has successors, all outside the constraint. These make the search incomplete,
  as `maxDepth` does, and are not checked.

A failure, "unanswered at the end", is then a real run of the scenario to a quiet state that
is not answered. Its theorem is `search_deadlock`'s, with `m.next s = []`.

**Default on when sound.** Whether an unanswered quiet state is a bug depends on the
environment. An input lost on a lossy link, or a mailbox lost when its actor crashes
(`SysState.down`), leaves an input that no system can answer. So the check is on by default
exactly when the scenario's environment meets the premises of `ImplementsLive` (3.2), which is
decidable over `Enum σ.Id`, and the report says when it was off and why. The template's check
meets them. Lanes' own tests already do this by hand: `Tests/Schedule.lean` and `Tests/Jobs.lean`
set `checkDeadlock := maxCrashes == 0`; `Tests/Gate.lean` and `Tests/Fronted.lean` write
"everything sent and every request answered" as `terminal`; `examples/videos/Videos/Check.lean`
sets `checkDeadlock := live, terminal := settled`.

**What it does not catch.** A system that never goes quiet: a retry timer that never gives up
fires forever, so no state is quiet and the check passes. The checker has no search for cycles.
Bounded retries (rule 2.6) make such runs end, so the check sees them. A quiet state is quiet
within the scenario's budget: more inputs or more crashes would enable more events.

### 3.2 The statement

```lean
/-- `sys` implements `svc` under `env`, and answers: in every fair run, every input takes
effect and the outputs it produces are handed over. -/
structure System.ImplementsLive (sys : System σ) (env : EnvModel σ)
    (svc : Service σ.In σ.Out S T) (deadlines delivered : Deadlines σ T) : Prop where
  implements : sys.Implements env svc deadlines delivered
  answers : ∀ r : sys.Run env, r.Fair → ∀ n, ∃ m, n ≤ m ∧
    -- the prefix up to `m` is explained (`Implements.Explains`) by a history in which every
    -- input before `n` is taken and every output of those takes is handed over before `m`
    Settles svc deadlines delivered (r.prefix m) n
```

The exact form of `Settles` is the first work. Its premises are a bundle of part 6: the inputs
arrive and the actors that take them do not crash. The first instance is `Server.implementsLive`,
from `Server.implements` and `Run.Fair.handled` and `Fair.output_taken`. Every app's `CLAIMS`
row then says "proved" or "not proved" of the same statement, as the Raft row does in prose.

## 4. Honest results

`Report.ok` is `failure.isNone` (`Lanes/Check/Search.lean:144`), so a pass cut short by
`maxStates` exits 0 in the template. 88 lines in 40 files of `examples/` and `Tests/` test `ok`
and `complete` together by hand. Issue #102 gives a bounded pass its own exit code, prints
"bounded" plainly, and adds `--json` with a kind for each failure. This decision adds nothing to
it but one request: that the exit codes tell apart a complete exact pass (0), a failure (1), and
a pass that is not exhaustive (2), which covers both a bounded and a fingerprinted pass.

## 5. Specs that can fail

The gate answers `busy` (`503`) when `maxPending` requests wait, and `timedOut` (`504`) when a
request's deadline passes (`Lanes/Web/Http/Gate.lean:76,80`). The two differ in what they say:

- a `503` at arrival comes before the request is forwarded (`Gate.step`, `.arrive`): it did not
  take effect;
- a `504` comes after: the request was forwarded, may still take effect, and its late answer is
  dropped.

`busy` is also the answer "to requests in flight when it stops", which were forwarded: that one
says what a `504` says (question 8).

A combinator over `Service`, so the deterministic `step` that apps write stays:

```lean
/-- How a service may fail an input. -/
structure Service.Failures (In Out : Type) where
  /-- The answer that says `x` did not take effect: `503`. -/
  refuse : In → Option Out
  /-- The answer that says nothing about whether `x` took effect: `504`. -/
  unknown : In → Option Out
  /-- Inputs may be refused only while at least this many wait. -/
  busyAt : Nat
```

`svc.mayFail f` is a `Spec` whose states are `svc.spec`'s with a multiset of *orphans*. It has
every step of `svc.spec`, and three more:

- **refuse** a pending `x`, while at least `f.busyAt` inputs are pending: `x` leaves, `refuse x`
  goes to the outbox, the value is unchanged;
- **give up** on a pending `x`, when its deadline passes (a deadline of the spec, D42): `unknown x`
  goes to the outbox and `x` becomes an orphan;
- **an orphan takes effect**, at any later moment or never: the value is `svc.step`'s, and its
  outputs are dropped.

This is how Jepsen and Porcupine read a timed-out operation: one that may take effect at any
later time. The monitor's candidates grow by one branch per pending input; its construction is
the same in kind. With it, `Http.served sys` has a spec to refine, the app's own lifted through
the bridge, and the CLAIMS row "Ledger and rookery: the system behind the HTTP gate implements
the spec: not proved" gets a target.

**Failing always is not enough.** A system that refuses everything would implement `mayFail`
if refusing were always allowed. Two things stop it:

- refusing is a step only while `busyAt` inputs wait, so at low load a refusal is a refinement
  failure, found by the monitor;
- giving up is allowed at any deadline, and in the untimed semantics a deadline may pass at once,
  so safety cannot stop a system that gives up on everything. Liveness does:
  `ImplementsLive (svc.mayFail f)` under a bundle `NotOverloaded` says that in a fair run in
  which fewer than `busyAt` inputs wait and no waiting input's deadline passes, every input
  takes effect with its own answer.

With part 7, "no deadline passes" becomes "the system answers within `requestTimeout_ms`". That
is a claim about speed, which the benchmark measures and no proof makes. The theorem says the
system never chooses to fail when it need not.

## 6. Named sets of environment assumptions

Today each theorem writes its own premises:

| Premise as written today | Theorems | Bundle |
|---|---|---|
| none: every environment model | `Shop.charged_at_most_once`, `TodoDb.outputs_noUnkeyed`, `Videos.private_to_owner`, `RaftKV.election_safety`, `Election.election_safety` | none |
| `env.Faultless` | `Counter.implements`, `Upload.implements`, `Bank.money_conserved`, `Server.implements` | `Faultless` (exists, `Lanes/Core/System.lean:185`) |
| the link from outside does not duplicate | `Rookery.implements`, raft-kv's refinement, `Ledger.implements` (`hin`), kv-cache (every link) | `InputsOnce` |
| each user's link to the ledger is ordered and does not duplicate | `Ledger.implements`, `Ledger.implements_timed` | `Fifo (users) ledger` |
| an actor does not crash | the ledger (`Ledger.implements_timed`), the scheduler and the reminders (`Reminders.delivery_answered`), the site (`Videos.report_settles`), the scheduler (`Videos.job_ends`) | `Stays A` |
| a link loses nothing | scheduler to reminders (`Reminders.delivery_answered`), outside to the site (`Videos.report_settles`) | `Lossless src dst` |
| the environment `{}` | the watchdog's fair run (`Watchdog.exists_fair_run_never_barks`) | `SingleProcess` |
| a fair run | every liveness theorem | `Run.Fair`, of runs, not of `env` |

Proposed, in `Lanes/Core/System.lean`, each a `Prop` of an `EnvModel`:

- `InputsOnce`: no link from outside duplicates.
- `InputsArrive I`: no link from outside to an actor of `I` loses.
- `Stays A`: no actor of `A` crashes.
- `Lossless src dst`, `Fifo src dst`: one link, or a set of them.
- `Faultless`, as now.
- `SingleProcess`: `Faultless`, and every link ordered. `Kernel.env` meets it
  (`Lanes/Runtime/Kernel.lean:81`), by a one-line lemma.
- `Networked`: what the transport between processes gives (D30), for `System.shards`.

With implications between them (`SingleProcess → Faultless → InputsOnce`, and so on), a theorem
premised on `InputsOnce` applies to the kernel by one lemma, not by an audit.

The runtime contract (#86) then has two obligations here: every execution is a run under an
environment that meets the runtime's bundle, and every infinite execution is `Run.Fair`. Fairness
is assumed of the runtime today (`TRUSTED.md`, "Progress"). Some bundles can also be watched where
they run, as PObserve watches logs (part 8): the gate can count the request ids it sees twice,
which is `InputsOnce` failing.

## 7. Timers' delays

The semantics ignores a timer's delay (`Lanes/Core/World.lean:150`), and any pending timer may
fire at any moment (`:203`). That is sound for safety, and P makes the same choice. It also
puts out of reach every claim about how long something lasts: rookery's rate limit is proved per
window firing (`Rookery.rate_limit_run`), not per minute, and its README says the semantics does
not model how long a window, a session or a lock lasts.

The proposal is a premise on runs, not a change to `SysState.step`. A run is **timely** for a
clock `t : ℕ → ℕ`, milliseconds at each position, when:

1. `t` never goes back;
2. a timer fires no earlier than its deadline: if `i`'s timer `msg` fires at `m`, and the last
   step before `m` that armed it was at `n` with delay `d`, then `t n + d ≤ t m`;
3. an actor's timers fire in the order of their deadlines.

`System.Run.Timely r t` goes in `Lanes/Semantics/`, beside `Run.Fair`. The deadline is the one
of the last arming, which is what the kernel does when it re-arms a pending timer.

Every existing proof stays true. `SysState.step`, `Reachable` and `Run` do not change. Every
existing theorem is about all reachable states or all (fair) runs, so it holds of the timely
ones. A new theorem takes `Timely` as one more premise, and may use it.

Two obligations keep the premise from being empty:

- **the kernel's runs are timely**: `Kernel.timerNext` names only the earliest timer of the
  agenda, and only once `clock_ms` has reached it (`Lanes/Runtime/Kernel.lean:193`), and the
  kernel's clock never goes back (`Kernel.advance`). `Kernel.fire` itself does not compare the
  deadline with the clock, so the theorem is about runs driven by `Kernel.step` and
  `timerNext`. It is not proved today; it goes in the runtime contract;
- **timely and fair together are possible**: every finite timely prefix extends to a run that is
  both, since the clock can always move on until the next timer is due. In Abadi and Lamport's
  terms, the pair is machine closed.

The checker stays untimed: a clock in the checker's state would multiply its states.

## 8. Perspectives

**Lamport, safety and liveness.** Lamport named the two kinds of property in his 1977 paper on
proving multiprocess programs: a safety property says nothing bad happens, a liveness property
that something good eventually does. Alpern and Schneider (1985) proved that every property is
the conjunction of one of each. In TLA a specification is the initial condition, the next-state
relation and a fairness condition together, so "implements" includes liveness. That supports
part 3: a standard `ImplementsLive`, so an app's headline is not safety alone. TLA+ also checks
(TLC) and proves (TLAPS) the same formula, which is part 2. Abadi and Lamport's machine closure
is the test part 7 has to pass.

**AWS's P and PObserve.** In P (Desai and others, PLDI 2013) a specification is a monitor over the
events of a run, so "this step was a delete by its owner" is a natural property: part 2's step
properties. P checks liveness in bounded runs with *hot* monitor states: a run that ends while a
monitor is hot fails, which is part 3's check. P's timers fire nondeterministically, as Lanes'
do. PObserve, as AWS describes it, checks logs of tests and of production runs against the
same P specifications; I have not used it. It is the precedent for watching the environment's
assumptions and the outside's models where they run (part 6, and finding 7 of the sweep).

**The Go 1 compatibility promise.** Go 1 (2012) promised that programs written to its
specification keep compiling and running through Go 1.x. The promise is useful because it says
what it covers, the specification and the standard library's API, and lists the ways a program
can depend on more and lose the promise: unspecified behaviour, `unsafe`, struct literals with
unkeyed fields. The proof surface is the specification here. A hidden body is unspecified
behaviour, `import all` is `unsafe`, and `{ c with net := … }` is the unkeyed struct literal.
Experimental modules are outside the promise, as Go's `x/` packages are.

**Ousterhout.** *A Philosophy of Software Design* asks for deep modules, much behind a simple
interface, and names information leakage: one design decision reflected in many modules. That
the network is a list, oldest first, is one decision, and it shows in 8 apps. The surface is the
interface of the semantics as a deep module, and the lemmas of 1.2 pull the list surgery down
into Lanes, where one change fixes it once. Rule 1.3 already cites him.

## 9. Costs, order of work, questions

### Costs

| Work | Estimate |
|---|---|
| Stability default and lint `stability` | a day |
| `Check.invariant`, `Check.witness`, their theorems, `Enum`'s instances; raft and the template ported | 3 to 5 days; each further app a day or two |
| Step properties in the checker, with their soundness theorem | about a week |
| Quiet and cut told apart, `Monitor.settled`, the default rule; `search_deadlock`, `search_deadlock_free` and the fingerprinted and reduced theorems restated | 3 to 5 days |
| `ImplementsLive` and `Server.implementsLive` | 1 to 2 weeks |
| Environment bundles, their implications, the examples' premises restated | about a week, shared with #86 |
| The surface: the missing lemmas; `Monotone`, `Account` and `step_*` restated with named operations (32 library files' proofs follow); 16 example files moved onto it; bodies hidden, `import all`, a lint | 3 to 4 weeks |
| `Service.mayFail`, the monitor's branch, the theorem that the gate refines it | 2 to 3 weeks, most of it the gate's theorem |
| `Run.Timely`, the kernel's theorem, a first use (rookery's rate per minute) | 2 to 3 weeks |

What it costs users: proofs against the surface are a little longer where a `simp` with the
bodies closed a goal in one line, as kv-cache's concrete stale read does. What it costs Lanes: the
32 library files need `import all`, and lemmas proved by `rfl` today need a tactic.

### Order of work

1. The stability default. It is one paragraph, and everything after it can then change freely.
2. #102, in progress.
3. Derived checks, on raft and the template, so that new apps copy the new form.
4. Quiet and cut, and the standard check on by default, in the template too.
5. The environment bundles, with #86.
6. `ImplementsLive` and its first instance; one CLAIMS row per app.
7. The surface's lemmas, the rules restated, the examples moved; then the bodies hidden.
8. `Service.mayFail` and the gate's refinement.
9. Timely runs.

Steps 3 and 4 come early because they change what the template teaches, and every new app starts
from it. Hiding the bodies comes last because it needs every lemma first.

### Questions for the owner

1. **How to hide bodies.** By the module system (`@[no_expose]`, so `B` cannot unfold), or only by
   a lint on the examples? *Default:* the lint first, while the lemmas are written; then
   `@[no_expose]` on the definitions of 1.1 once no example unfolds them.
2. **`SysState`'s fields.** Make them private too, so `{ c with net := … }` is refused outside
   Lanes? *Default:* no, not now. Name the operations, lint the record update in examples, and
   decide again before 1.0.
3. **The stability default.** Flip it, so every module is experimental unless marked stable?
   *Default:* yes, with the stable list of 1.4.
4. **Checks.** Replace `Property.always` of a `Bool`, or add `Check.invariant` beside it?
   *Default:* beside. A `Bool` check that reads the driver stays, and its CLAIMS row says
   "checked only".
5. **The liveness check's default.** On exactly when the scenario's environment meets
   `ImplementsLive`'s premises, and the report says when it was off? *Default:* yes.
6. **`ImplementsLive`.** A structure of both halves, or a second theorem beside `Implements`?
   *Default:* the structure, so the headline names one statement; CLAIMS reports each half.
7. **Specs that fail.** A combinator over the deterministic `Service`, or a relational `step`?
   *Default:* the combinator, `Service.mayFail`; a relational step only when a second need for it
   appears (kv-cache's read cache may be one).
8. **`503` at stop.** The gate answers `busy` to requests already forwarded when it stops. Should
   it answer `504` there, or should the spec read that `503` as "unknown"? *Default:* `504`, so
   that a `503` always means "did not take effect".
9. **Timers.** `Run.Timely` as an opt-in premise, an `EnvModel` field, or nothing yet? *Default:*
   the opt-in premise, after the rest; per actor, not across actors.
10. **Bundles.** Where they live and what they are called. *Default:* `Lanes/Core/System.lean`,
    the names above, settled with #86.
