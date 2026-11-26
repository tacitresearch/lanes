# Lean on Lanes — Design Document

Nov 25, 2026 · Nathan Barry

## What Lanes is

Lean on Lanes (the Lanes framework) is a general toolkit for building verified software in Lean. One small set of composable tools (actors, a semantics, a model checker, proof tactics, I/O adapters and a web layer) covers full-stack applications, coordination services, and distributed systems that an agent designs, implements and verifies on its own. Lanes prescribes no project layout or application architecture.

The name is the design. Every actor runs in its own lane, nothing shares state, and the runtime merges traffic only at the edges. Tagline: **Proved logic, contained concurrency.**

What a user sees: one dependency, `lanes`, and one command, `lanes new myapp`. No external solver to install and no second package for the web layer. The same step function runs in production, in the simulator, in the model checker and in the proofs.

Target: the large majority of backend and distributed-systems work: APIs, workflows, coordination services, ledgers, replicated protocols (Raft, Paxos), and DynamoDB-style systems built by agents, where the bugs come from state, concurrency, retries and partial failure.

## Design principles

1. **Logic is a pure step function.** Every component is `step : State → Msg → State × List (Effect Msg)`. No I/O, no shared memory, no locks inside the logic.
2. **Effects are data.** Sends, replies, timers and external I/O are returned as values; the runtime performs them and feeds results back as messages.
3. **Concurrency lives only at the edges.** The runtime turns the concurrent world into an ordered stream of messages per actor. The part you prove has no concurrency in it.
4. **Layered specs, one language.** Abstract specs (a service spec and, for protocols, a protocol model) are small, readable Lean transition systems; implementation actors are the code that runs, used directly by the simulator, the model checker and the proofs. A checked refinement connects the two, so there is no hand-maintained model to keep in sync.
5. **Bugs first, proofs second.** Model checking and simulation find counterexamples in seconds; proofs come after the design survives them.
6. **Failure is visible.** Message loss, reordering, duplication and crashes are part of the semantics, never hidden behind location transparency.
7. **Tools, not conventions.** Each layer is usable on its own: use the runtime without the web layer, the model checker without the runtime, the semantics without any of it.

## Design guidelines

The full rules, each with its reason, live in [LANES_STYLE — Design and Code Guidelines](../LANES_STYLE.md). They also ship in every generated app as `LANES_STYLE.md` plus an `AGENTS.md` section. They adapt TigerStyle, Ousterhout, Erlang/OTP, crash-only software, Lampson's hints and functional-programming practice. The ones that shape the framework itself:

- **Essential vs accidental state** (Out of the Tar Pit): specs and actor state hold only essential state, and caches are derived views with a theorem tying them to the source.
- **Data, calculations, actions:** messages and effects are data, `step` is a pure calculation, and only the runtime and adapters act.
- **Illegal states unrepresentable; parse, don't validate:** invariants go in types first, then theorems. Raw input is parsed once, in adapters.
- **Let it crash, crash-only:** an unexpected state leads to `stop`. Supervisors are library actors with proved specs. Start always means recover, so the recovery path is proved and runs on every restart.
- **Runtime as error kernel:** the trusted base stays small, and every exception to it is listed in `TRUSTED.md`.
- **End-to-end arguments:** dedup and idempotency keys live at app endpoints, and every `io` effect carries a key and a deadline.
- **OTP-style behaviours:** `Server`, `StateMachine`, `Supervisor`, `Pool` and `Timer` in `Lanes.Behaviours`, each with its spec and refinement proof.
- **Check before prove:** every invariant is model-checked, with a vacuity check, before proof work starts.
- **Enforced, not aspirational:** `lanes lint` checks for no IO in `step`, total logic, bounded state, layering, field leaks, shallow modules and listed trusted code.

## Architecture

The left column is the code that runs; the right column is what the proofs are about. They meet at the actors (the same functions) and at the runtime (a CSLib simulation proof to the semantics).

*(Architecture diagram not included in this copy.)*

Applications touch only the top-left box. Everything on the right except the environment models is proved; the bottom two runtime layers are trusted, as for any Lean program.

## Package and dependencies

One package, `lanes`, built on CSLib, which brings Mathlib and Batteries. No Veil or Lentil dependency.

**Why CSLib and Mathlib.** Proofs about real systems need finite sets and cardinalities (quorums), sums (balances, quotas), orders (logs, versions), list lemmas and probability. Mathlib has them, AI provers are trained on its idioms, and CSLib adds transition systems, simulations, infinite executions, temporal operators and actor-shaped distributed models. Building the Lanes semantics as a CSLib LTS keeps it compatible with the wider library and upstreamable later. Mathlib ships prebuilt caches (`lake exe cache get`), so the cost is a download, not hours of compiling.

**Relation to Veil.** Veil (verse-lab) offers a distributed-protocol DSL, model checkers and SMT-backed proofs. Lanes does not depend on it for three reasons. Veil tracks a different Lean toolchain than CSLib (v4.35.0 vs v4.37.0-rc1). It requires an SMT solver in every user's setup. And it has a small maintainer base. Lanes builds the parts it needs (an explicit-state model checker and liveness tooling) directly on its own step functions.

**Specs are plain Lean.** A dedicated spec language mainly earns its keep by keeping proof obligations inside fragments an SMT solver can decide. Lanes proofs are Lean proofs, so specs are ordinary Lean structures and functions. Veil's checker engine is Apache-2.0, so its parallel search, fingerprinting and seen-set design can be ported into `Lanes.Check` with attribution.

**Veil as an optional design-time tool.** For a new protocol, iterating on invariants with SMT feedback is fast. A protocol can be designed in Veil, and the stable invariant set then ported into a Lanes protocol model, where agents prove it and obligation automation maintains it. Finding an inductive invariant is the expensive step; re-proving a known-good set is mechanical. For example, kv-lean, a Raft-backed key-value store previously verified with Veil at the protocol level, supplies a ready invariant set and serves as the main benchmark throughout this document. For new protocols, the counterexample-to-induction finder handles invariant discovery on small instances, with Veil as an option when SMT feedback helps. No Lanes build depends on Veil.

### Modules inside the one package

| Module | Contents | Imports |
| --- | --- | --- |
| `Lanes.Actors` | `Actor`, `Effect`, runtime, scheduler, supervision | Std only |
| `Lanes.Env` | HTTP, KV, database, clock and node-transport adapters | Std only |
| `Lanes.Html` | Typed components, HTMX and streaming renderer | Std only |
| `Lanes.Kit` | Optional app tools: persistence, auth, forms, jobs | Std only |
| `Lanes.Semantics` | System semantics as a CSLib LTS, network and fault models, refinement | CSLib, Mathlib |
| `Lanes.Temporal` | Fairness, leads-to, ranking-function tactics | CSLib, Mathlib |
| `Lanes.Check` | Model checker, liveness lasso search, linearizability checker, simulation | Std, Semantics |
| `Lanes.Audit` | Trusted-code report and CI gate | Lean metaprogramming |

Runtime modules import only Std, so app code compiles fast and binaries stay small; only proof modules pay for Mathlib.

**Toolchain.** Lanes follows CSLib's toolchain, which follows Mathlib's, which tracks Lean releases closely.

**Optional bridges, later and off the default path:** a Veil export for SMT proofs of protocols that fit its decidable logic, and upstreaming `Lanes.Semantics` into CSLib once it is stable.

## Trust boundary and environment model

Everything above the semantics is proved, the environment is assumed by explicit model, and everything below the actor library is trusted.

| Layer | Status | How it is checked |
| --- | --- | --- |
| Actor step functions | Proved | Per-actor invariants by induction over messages |
| System safety, liveness and refinement to specs | Proved | Over `Lanes.Semantics`, with model checking first |
| Environment (network, DB, HTTP, clock, other machines) | Assumed | Explicit Lean models; each assumption named and reviewable |
| Actor library (mailboxes, scheduler) | Proved for the deterministic scheduler; trusted and trace-checked for the concurrent one | CSLib simulation proof, trace checking in CI |
| `implemented_by` swaps | Trusted, human-audited | `Lanes.Audit` report, differential tests |
| `Std.Async`, Lean runtime, compiler, clang | Trusted | Shared by every Lean program |

Environment models are part of the specification, not a gap: "the KV store is linearizable", "links may lose, reorder and duplicate messages but not forge them", "timers fire no earlier than requested". A property is only claimed when every layer it depends on is proved or named as an assumption.

## Build order

Each phase is useful on its own, so stopping after any of them leaves a working tool.

1. **Foundations:** Lake package on CSLib's toolchain, the module layout above, CI with `lake exe cache get`.
2. **First cut (the one-week target):** runtime, `Actor`/`Effect` API, deterministic scheduler with traces, a minimal model checker, and per-actor proofs for one reference app.
3. **Everything the first real system needs (a Raft-backed KV store):** environment actors and generic data types, vacuity checks, the counterexample-to-induction finder, the semantics on CSLib, service spec, protocol model and refinement checking, invariant obligation automation, and the linearizability checker. First benchmark: port kv-lean's Raft invariants.
4. **On demand after that:** refinement proof support (history and prophecy variables), scheduler fairness proof, liveness, storage, clock and Byzantine fault models, symmetry and parallel search, the audit tooling, the web layer, and the app kit.

### Decisions to settle at the start

1. Message typing: one sum type per actor, with typed references `ActorRef Msg`.
2. Delivery the runtime promises: per-sender FIFO within a process; loss, reordering and duplication only on links between machines.
3. External responses re-enter as ordinary messages tagged with a request id.
4. Every `step` is total, so Lean checks handler termination for free.
5. Runtime modules never import Mathlib.

## Phase 1: Runtime and the Actor API

A working runtime built entirely in Lean on `Std.Async` and `Std.Sync`, the API every application writes against, and per-actor proofs for the reference apps.

```lean
structure Actor (S Msg : Type) where
  init : S
  step : S → Msg → S × List (Effect Msg)

inductive Effect (Msg : Type)
  | send  {M} (to : ActorRef M) (m : M)
  | reply (m : Msg)
  | after (ms : Nat) (m : Msg)
  | io    (req : ExtRequest) (onDone : ExtResponse → Msg)
  | stop

theorem step_preserves {s m} (h : Inv s) : Inv (A.step s m).1
```

(Design sketch; exact typing settled at the start.)

### Runtime components

- **Mailbox:** a bounded `Std.Channel` per actor with a backpressure policy.
- **Actor loop:** receive, call `step`, commit state, hand effects to the dispatcher; one message at a time.
- **Dispatcher:** routes `send`, completes `reply`, schedules `after`, forwards `io` to adapters.
- **Registry and supervisor:** spawn and stop; one-for-one and all-for-one restart policies.
- **Heavy work:** long computations run as separate `Task`s that report back with a message, because the runtime is cooperative, not preemptive.
- **Deterministic scheduler:** single-threaded, seeded message order, emits a trace of every delivery. Used for tests, replay, and as the base of the model checker.

**Per-actor proof library:** `Reachable A s` with an induction principle, invariant combinators, effect lemmas, and tactic macros over `grind`, `omega` and `simp` for the obligation shape `Inv s → Inv (step s m).1`.

### Reference apps

1. **Bank ledger:** balances never negative (per actor); money conserved across transfers (system).
2. **Rate-limited gateway:** bucket never exceeds capacity (per actor); no client exceeds its quota (system).
3. **Raft-style leader election:** at most one leader (safety); eventually a leader under fair delivery (liveness).

**Exit criterion:** the reference apps run under both schedulers with identical traces for the same message order, and all per-actor invariants are proved.

## Phase 2: Semantics, specs and refinement

Define once what a Lanes system means, as a CSLib LTS, so no application ever writes its own model or refinement proof.

### The semantics (`Lanes.Semantics`)

- **Global state:** actor states by `ActorId`, the multiset of in-flight messages, pending timers and external requests, and which nodes are up.
- **A step** delivers one message, fires a timer, completes a request, or crashes or restarts a node. CSLib's FLP `Algorithm` (receive a message, update state, emit a multiset of messages) is the precedent for this shape.
- **Network model as a parameter:** reliable per-sender FIFO, lossy, reordering, duplicating, and combinations; crash faults per node. In-process links use reliable; links between machines use lossy, reordering and (with retries) duplicating.
- **Fairness as a parameter:** weak fairness of delivery per mailbox, needed for liveness.
- **Theorems proved once for every app:** a per-actor invariant lifts to a system invariant; effects are delivered as the network model allows.

### Connecting the runtime

1. **Trace checking:** traces from the runtime are replayed against the semantics in CI; any rejected trace is a runtime bug.
2. **Deterministic scheduler proof:** stated as a CSLib simulation (`IsSimulation`) from the scheduler to the semantics, including that the scheduler is fair. That proof is what earns the fairness assumption used in liveness proofs.
3. **Concurrent runtime:** kept small, trace-checked, and treated as trusted.

### Abstract specs and refinement (`Lanes.Spec`)

A spec is a small transition system over abstract state, written in plain Lean, whose labels are what the outside world sees: client requests and responses. It is the readable artifact humans review and the interface between components.

```lean
structure KVSpec (K V : Type) where
  store : K → Option V

inductive Op (K V) | put (k : K) (v : V) | get (k : K)
inductive Res (V)  | ok | value (v : Option V)

-- Each visible operation takes effect atomically.
def KVSpec.step : KVSpec K V → Op K V → KVSpec K V × Res V
  | s, .put k v => ({ store := Function.update s.store k (some v) }, .ok)
  | s, .get k   => (s, .value (s.store k))

-- Specs that need nondeterminism are relations, or list their successors for the checker.
inductive ConsensusSpec.Step : Option V → Label V → Option V → Prop
  | decide (v : V) : ConsensusSpec.Step none (.decided v) (some v)
```

### Three levels, each refining the one above

1. **Service spec** (`KVSpec`): what clients see.
2. **Protocol model:** a small transition system in plain Lean over protocol-level relations ("the leader of term t holds entry i"). Protocol invariants are stated and proved here, never over implementation details.
3. **Implementation actors:** the code that runs, with codecs, queues and timers. Internal protocol messages are τ steps.

Each refinement maps one level to the next, and refinements compose. kv-lean used the same three-level structure with level 2 written in Veil; Lanes writes level 2 in plain Lean.

```lean
-- Level 2: Raft at the protocol level (sketch)
structure RaftModel (N V : Type) where
  currentTerm : N → Nat
  log         : N → List (Nat × V)   -- (term, value)
  votedFor    : N → Nat → Option N
  commitIndex : N → Nat

inductive RaftModel.Step : RaftModel N V → Label V → RaftModel N V → Prop
  -- becomeLeader, appendEntries, advanceCommit, ...

theorem election_safety (h : Reachable s) :
    isLeader s t l₁ → isLeader s t l₂ → l₁ = l₂
```

```lean
-- Implementation → protocol model: read each node's log out of its actor state
def absImpl (sys : Lanes.SysState RaftKV) : RaftModel N V := ...
-- Protocol model → service spec: apply the committed prefix
def absModel (m : RaftModel N V) : KVSpec K V := ⟨fun k => m.committed.applyTo k⟩

theorem impl_refines_model : Lanes.Refines (Lanes.sem RaftKV) RaftModel.lts absImpl
theorem model_refines_spec : Lanes.Refines RaftModel.lts KVSpec.lts absModel

-- Composed: the running code refines KVSpec
theorem raftKV_refines := impl_refines_model.trans model_refines_spec
```

- `Lanes.Refines` is a thin layer over CSLib: weak simulation with τ steps (`LTS/HasTau`), which is refinement with stuttering.
- Linearizability is refinement to a sequential spec such as `KVSpec`.
- Specs compose: each partition refines `KVSpec`, and the router is proved against a map of partitions.
- Later, as proofs need them: auxiliary history and prophecy variables for refinement mappings that cannot be written from current state alone.

### How much structure an app needs

The three levels are a ceiling, not a requirement. Structure grows with the app:

| What you are building | Levels |
| --- | --- |
| Prototype or internal tool | Implementation only: actors, tests, model checking on small instances |
| Ordinary CRUD app you care about | Implementation plus invariants (authorization, validation, view invariants) |
| CRUD where concurrency matters (shared editing, payments) | Service spec plus implementation, with refinement |
| Systems with their own protocol (replication, sagas, caches) | All three levels |

The protocol model appears only when there is hidden coordination: internal state and messages that clients never see but correctness depends on.

### Example: a CRUD todo app (two levels)

```lean
structure TodoSpec where
  todos : UserId → TodoId → Option Todo

inductive Req  | create (u : UserId) (title : String) | toggle (u : UserId) (id : TodoId)
               | delete (u : UserId) (id : TodoId)    | list (u : UserId)
inductive Resp | created (id : TodoId) | ok | notFound | items (l : List Todo)

def TodoSpec.step : TodoSpec → Req → TodoSpec × Resp
  | s, .toggle u id => match s.todos u id with
    | none   => (s, .notFound)   -- other users' todos do not exist for you
    | some t => ({ s with todos := update s.todos u id (some { t with done := !t.done }) }, .ok)
  | ...
```

- **Implementation:** the HTTP adapter turns each request into a message for a handler or session actor; the handler validates, emits `io (.sql …)`, and replies with a `Lanes.Html` fragment. Postgres is an environment model with serializable transactions, so each transaction is one atomic step.
- **Refinement:** the mapping reads the todos table into `TodoSpec`. Request and response are visible labels; the transaction commit is where the spec step happens; decoding, the database round trip and rendering are τ steps.
- **What it buys:** users only see and change their own data, acknowledged writes appear in later lists (read-your-writes), and responses match the spec.
- **Where the checker earns its keep even here:** lost updates from read-modify-write outside a transaction; a cache, whose agreement with the database is an invariant over hidden state (the point where a middle level pays off); checkout-style sagas, whose state machine is a small protocol model; exactly-once background jobs.

**Exit criterion:** the semantics with its lifting theorems, trace checking in CI, and the Raft KV store checked against `KVSpec` on small instances; the scheduler simulation and fairness proofs follow when liveness needs them.

## Phase 3: Model checking and system proofs

Find bugs in seconds on small instances, then prove the properties for all instances, all on the same step functions.

### Model checker (`Lanes.Check`)

- Explicit-state search over every message interleaving of a small instance (for example 3 nodes, bounded messages), under the chosen network and fault model. The deterministic scheduler from Phase 1 already provides the execution engine.
- State hashing and visited sets; symmetry reduction for interchangeable nodes later.
- Random simulation for instances too large to explore exhaustively.
- Counterexamples are message traces, replayable in the deterministic scheduler and readable by agents.

### Checking features

| Feature | Why it matters |
| --- | --- |
| Environment actors | Clients, adversaries and timeouts that choose nondeterministically, allowed only inside the checker; the implementation's `step` stays deterministic |
| Generic data types | Actors are written generic over keys, values and node ids, so the checker runs them with 2 keys instead of real strings; the precondition for checking implementation-level code |
| State constraints and coverage | Bound otherwise infinite models; report which actions never fired |
| "Sometimes" properties | Vacuity checks: confirm interesting states are reachable, so no proof succeeds for a silly reason |
| Refinement checking | At every step, `abs` is unchanged or moves by an allowed spec step with the same label; a violation is a trace |
| Counterexample-to-induction finder | Given a candidate invariant, find a small-instance state where it holds but one step breaks it; the main aid for agents strengthening invariants |
| Symmetry, parallel and compiled search | When instances get too large; engine design ported from Veil |

**Not planned:** symbolic checking of all parameter values up to k steps (Veil's `sat trace`, Apalache). It is the one capability that needs SMT; Veil remains available as a separate tool for it.

### Invariant obligation automation (`lanes prove`)

Without SMT, proving a protocol invariant set means showing every invariant is preserved by every action: about 675 obligations for kv-lean's Raft model (roughly 45 invariants × 15 actions). Lanes automates the mechanical share and hands the rest to agents:

1. **Split the matrix:** generate one goal per invariant × action pair.
2. **Frame discharge:** compute each action's footprint and close every pair whose invariant reads none of the fields it writes. At the protocol level the matrix is dense (most Raft invariants and actions touch the logs), so this mainly clears the easy invariants. It pays off most at the implementation level: handler × node-field lemmas ("this handler keeps the term", "never touches seen"), where one protocol change otherwise ripples through dozens of lemmas.
3. **Automation pass:** run `grind` (an SMT-style engine inside Lean: congruence closure, case splits, lemma matching), `simp` and `omega` on the rest.
4. **Quorum library:** Mathlib-based lemmas for quorum intersection and majority counting, the core of the genuinely hard Raft and Paxos invariants.
5. **Report and re-run:** list what is left for agents, with the counterexample-to-induction finder attached to any pair that fails on a small instance; re-check only affected pairs after a change.

**Expectations.** Expect a sizeable leftover at the protocol level. Raft's invariants are quantifier-heavy ("for every node, index and term…"), and `grind`'s quantifier instantiation is weaker than cvc5 on the decidable fragments Veil relies on. Grind patterns and `@[grind]` lemmas over the protocol model's relations narrow the gap; agents prove the rest. If the measured leftover is too large, add an optional SMT backend for the protocol layer only (cvc5 through lean-smt with proof reconstruction, as Veil does), off by default.

**Benchmark:** port kv-lean's Raft invariants. With Veil that layer is about 300 lines; the estimate by hand is 3,000–6,000 lines. The measured share the automation closes, at both the protocol and implementation levels, decides whether the optional SMT backend is needed.

**Linearizability checker.** For DynamoDB-style systems the key claim is "per-key linearizable". Record operation histories from simulated runs and check them against a sequential spec, as Jepsen and Porcupine do; then prove the property. CSLib's eventual-consistency formalization (`Computability/Distributed/Consistency`) is the reference for weaker consistency definitions.

**System invariant proofs.** Inductive invariants over `Lanes.Semantics`, proved in Lean with `grind`, `omega`, `simp` and Mathlib, written mostly by agents. This replaces SMT automation: obligations are uniform, and the proofs can use any Mathlib or CSLib lemma.

**Exit criterion:** the model checker finds a seeded split-brain bug in the election app; money conservation and at-most-one-leader are proved for all instances; the gateway's history passes the linearizability check.

## Proof automation and theory

Domain-specific tactics are ordinary Lean code, so Lanes ships its own. In kv-lean the protocol invariants were the cheap layer; the effort went into refinement case-splits, frame churn on every protocol change, and liveness. The tactics are ordered by that.

| Order | Tactic | What it closes |
| --- | --- | --- |
| 1 | `lanes_frame` | Pairs where a step does not touch what the goal reads: handler × node field at the implementation level, action × invariant at the protocol level. Also what lets apps extend a library protocol with fields and handlers while reusing its proofs. |
| 2 | `inv_split` | Splits "this invariant set is inductive" into one goal per invariant × action, runs the automation on each, reports what is left. The engine behind `lanes prove`. |
| 3 | `refine_step` | Refinement proofs: case-splits on the implementation step and proposes the matching spec step or τ step, with the mapping unfolded. |
| 4 | EPR instantiation + SAT | Instantiate quantified hypotheses with the terms in the goal, then solve the propositional residue with Lean's built-in SAT solver and kernel-checked SAT proofs (the `bv_decide` machinery). No external solver. |
| 5 | `quorum`, `leads_to`, `ranking`, grind extensions | Quorum intersection, fairness rules and ranking side conditions, and patterns for message multisets, logs and maps. |

**Scope of the EPR tactic.** It is complete only for stratified models, where function symbols do not form a cycle between sorts. kv-lean's Raft model is not: `cur_term : node → term` and `term_leader : term → node` form a cycle, and it uses total orders on terms and indexes. Veil copes because cvc5's model-based quantifier instantiation goes beyond pure EPR. So:

- A stratification checker reports whether a model is stratified and shows any cycle (`node → term → node`).
- The standard fix is Ivy's: replace a cycle-forming function with a relation (`leader_of : term → node → Prop`) plus a uniqueness invariant. Agents can do this from the checker's output, but it is real modelling work.
- On unstratified models the tactic falls back to bounded instantiation, a heuristic.
- Benchmark on the kv-lean port; if the leftover is too large, use the optional SMT backend for the protocol layer.

**Liveness is mostly a design problem.** Liveness bugs in replicated protocols usually come from adversarial schedules the design did not anticipate, not from proof friction. So the investment goes to the checking side: adversary environment actors and the lasso search, more than tactics.

### Theory to build in Lanes, then upstream to CSLib

Two items bridge to theory CSLib already has; the rest are new.

| Theory | Already in CSLib | What Lanes adds, then upstreams |
| --- | --- | --- |
| Quorum systems | Nothing | Majority quorums, general quorum systems, Byzantine 2f+1 and 3f+1, built on Mathlib's finite-set counting. New. |
| Replicated-log theory | Nothing log-specific; list prefixes come from Mathlib and Batteries (`List.IsPrefix`) | Log matching, committed prefixes, "same index and term implies same prefix". New. |
| Refinement with stuttering | `LTS/HasTau` (τ steps, saturated transitions, τ-closure); weak bisimulation and weak bisimilarity in `LTS/Bisimulation`; strong simulation only in `LTS/Simulation` | Weak simulation (refinement needs one direction, not bisimulation), forward and backward simulations, refinement mappings as functions. An extension of CSLib's existing work. |
| History and prophecy variables | Nothing | Abadi–Lamport-style auxiliary variables that do not change behaviour. New. |
| Linearizability | Defined axiomatically in `Distributed/Consistency` (Burckhardt-style histories, linearizability, sequential, causal and eventual consistency, replicated data types), with the hierarchy proved | Bridge only: the per-object composition theorem, and a proof that refining a sequential spec implies CSLib's history-based `Linearizability`, so Lanes results are stated in CSLib's vocabulary. |
| Message-passing semantics | FLP's `Algorithm` (asynchronous, multiset of messages) and `StatefulProcesses.Network` (synchronous handshakes, for choreographies) | General asynchronous semantics with loss, reordering, duplication, crashes and restarts, timers and external I/O (`Lanes.Semantics`), presented as a generalisation of FLP's `Algorithm`. |
| Fairness and leads-to | Generic `LeadsTo` and its rules (`OmegaSequence/Temporal`), infinitely-often (`InfOcc`), infinite executions of any LTS; fairness only inside FLP (`ProcFair`, `FairRun`, `FairScheduler`) | Generic weak and strong fairness for any LTS, and the rules fairness ⇒ leads-to and ranking ⇒ leads-to. Generalises FLP's fairness. |

Most valuable upstream contributions: quorum systems, replicated-log theory, history and prophecy variables, and generic fairness.

### Protocol library

Existing protocol models, such as Veil's Raft (`Examples/TLA/Raft.lean`, a direct translation of Ongaro's `raft.tla`), are benchmark models: model-checked on small instances rather than proved, not implementations, and not built for reuse. Lanes ships protocols as four layers:

1. **Service interface, `ReplicatedLog`:** an append-only committed log every replica agrees on. Raft, Multi-Paxos and Viewstamped Replication all refine it, so apps depend on a replicated log and can swap protocols; a state machine on top (KV store, lock service) refines its own sequential spec by applying the log.
2. **`RaftModel`:** a protocol model in plain Lean, global-state style with history variables where invariants need them, generic over node and value types, written stratification-aware, with its invariants proved and a proof that it refines `ReplicatedLog`. Starts from kv-lean's model and invariant set.
3. **Variants and extensions:** the adversary and network level is a parameter, and each variant states what it is proved against. Apps extend `RaftModel Ext` with extra fields and actions. Base invariants are proved once for any extension whose new actions leave base fields alone or change them only in allowed ways, with `lanes_frame` discharging those conditions. This lets proofs survive protocol revisions such as new message types or changed vote rules: only the affected pairs are re-proved.
4. **Reference implementation:** Raft as Lanes actors with codecs, timers and persistence, proved to refine `RaftModel`. Apps plug in their state machine and get a running, verified replicated log, the way systems use etcd's raft library today.

The same pattern applies to Multi-Paxos, chain replication and two-phase commit.

**Checker cross-validation:** Veil's `Benchmarks/TLA/Raft/` holds TLC configurations with known state counts; running `Lanes.Check` on the same instances and comparing counts validates the checker early.

## Phase 4: Liveness

Prove "something good eventually happens" for all instances, check it on small ones, and make the runtime deliver the fairness the proofs assume.

**Foundations already in CSLib:** infinite executions (`LTS/OmegaExecution`), `LeadsTo` and its combination rules (`OmegaSequence/Temporal.lean`, already tagged for `grind`), divergence and termination, fair message delivery (`FLP/FairScheduler`), and the safety-liveness decomposition.

### `Lanes.Temporal`

- **Fairness:** weak and strong fairness per mailbox and per action, stated in the semantics.
- **Ranking functions:** a well-founded measure that strictly decreases on every fair step proves the goal is eventually reached. Each obligation is an ordinary safety-style lemma, which agents handle well.
- **Leads-to chains:** request ⇝ queued ⇝ processed ⇝ replied, each link proved separately and chained.
- **Proof ergonomics:** borrow the design of Lentil's temporal-logic proof mode (Iris-style) without depending on it.

### Checking and reductions

- **Lasso search in the model checker:** a reachable cycle where a fairly scheduled action stays enabled but the goal never happens. Complete for a finite instance.
- **Liveness-to-safety reduction** (as in Ivy) where it applies, so the safety checker and invariant proofs handle liveness.
- **Bounded response by default:** for services, "reply within N steps or a timeout" is a safety property, easier to prove and more useful than "eventually".

**Runtime side.** The scheduler fairness proof (Phase 2) justifies the fairness assumption. In production, bounded-response properties are monitored through `Std.Async`'s `Watchdog`, so a violation becomes an alert, not a silent hang.

**Exit criterion:** "eventually a leader" proved for the election app under fair delivery; the lasso search finds a seeded livelock; one bounded-response property monitored live.

## Phase 5: Adapters, environment models and distribution

Every external system is an adapter actor in the runtime plus a Lean model of its behaviour in the semantics; applications only ever see messages.

| Adapter | Built on | Environment model (the assumption) |
| --- | --- | --- |
| HTTP server | `Std.Http.Server` | One `Request` message per request; one reply back |
| HTTP client | `Std.Async.TCP` (no client in Std yet) | A response or a timeout eventually arrives |
| Clock and timers | `Std.Time`, `Std.Async.Timer` | Timers fire no earlier than requested; clock is monotonic |
| KV store | In-process actor first, persistent later | Linearizable get, put, compare-and-set |
| SQL database | Native Postgres wire-protocol client, later | Transactions at the configured isolation level |
| Files | `IO.FS` | Writes durable once acknowledged |
| Node transport | TCP between machines | Links may lose, reorder and duplicate messages, never forge them |

### Distribution across machines

- `ActorRef` carries a node id; messages are serialised by derived encoders; nothing in an app changes except where an actor lives.
- Links between machines use the lossy, reordering and duplicating network model, because TCP connections drop and retries resend.
- A crashed node stops all its actors; on restart they recover from their logs (Phase 8). Crash and restart are steps in the semantics, so protocols are proved against them.
- Static cluster membership first; dynamic membership later, itself written as a Lanes protocol.
- Raft is the test case: each node is an actor on its own machine, and the proofs from Phases 3 and 4 cover the code that runs on every machine.

### Fault and environment models

- **Storage:** fsync semantics, so unsynced writes can be lost and writes can tear on crash. Event-sourced persistence depends on this model.
- **Clocks:** bounded drift and process pauses. Leader leases and lease-based reads are only safe under a stated clock assumption, a classic source of production bugs.
- **Byzantine nodes (optional):** adversary actors that may send any message under their own identity, for blockchain-style protocols.
- **Partitions:** expressed through the lossy link model plus scheduled link failures in environment actors.

**Shared external state:** either a single owner per entity (all access through that actor, serialised by construction) or a modelled store with a stated consistency model.

**No FFI:** TLS is terminated in a reverse proxy for now and listed as environment.

**Out of scope:** location transparency that hides network failure, and automatic clustering or rebalancing.

**Exit criterion:** the gateway serves real HTTP traffic, and the election app runs across three machines with its proofs intact.

## Phase 6: Trusted-code escape hatch and audit

Performance-critical code may run a faster implementation than the one proofs see, but every swap is declared, tested and listed for human review.

### The ladder (use the highest rung that works)

1. **In-place updates first:** single-owner arrays and buffers are already updated in place by Lean's runtime; nothing trusted.
2. **`@[csimp]`:** fast version proved equal to the spec; nothing trusted.
3. **`@[implemented_by]`:** fast version (may use unsafe Lean) trusted, not proved; allowed only with a registered differential test.
4. **`opaque` plus axioms:** only inside Lanes' own runtime primitives; forbidden in app code.

### Tooling

- [ ] `#trusted_report MyApp`: lists every `implemented_by`, `extern`, `opaque` and axiom reachable from the app (`#print axioms` misses the first two).
- [ ] `@[trusted_impl (test := ...)]`: refuses to compile without a property-based test comparing both versions.
- [ ] CI gate: the report must match a checked-in allow-list.
- [ ] Debug mode that runs both versions and compares results on every call.

Work that needs SIMD, GPUs or control over memory layout runs as a separate service behind an adapter, with its behaviour as an environment assumption.

## Phase 7: Web layer (`Lanes.Html`)

Server-rendered HTML driven by session actors, so all state stays on the server and client/server consistency is a single-actor property, not a distributed one.

**Model.** Each user session is an actor; a click or form submit is a message; the response, an HTML fragment, is a `reply` effect. Views are pure functions `Model → Html`, so "the UI never shows an order as paid unless the payment committed" is an ordinary invariant.

**Components as Lean macros, templ-style.** Go's templ has the right design (typed components, HTML as functions) but needs a `templ generate` step and its own language server. In Lean the same syntax is a macro inside the normal compiler: no generate step, errors on the template line, hover and go-to-definition inside templates. ProofWidgets and doc-gen4 already use JSX-like Lean syntax.

```lean
component Cart (c : CartState) : Html :=
  <div id="cart">
    {for item in c.items do <CartRow item={item}/>}
    <button hx-post={Routes.checkout} hx-target="#cart"
            disabled={c.items.isEmpty}>Checkout</button>
  </div>
```

- **Escaping by type:** `Html` and `String` are distinct; raw text enters only through one escaping function, proved correct once.
- **Typed attributes and routes:** `disabled` is a `Bool`; `hx-post` must name a route the router defines, so dead links fail to compile.
- **Provable views:** `Html` is an inductive type.
- **Intent, not HTMX syntax:** the renderer emits `hx-post`/`hx-target` today and native attributes if the Triptych proposals reach browsers.
- **Streaming:** reply with a skeleton and fill it with `<template for>` as slow effects finish (Chrome 150+, polyfill elsewhere).
- **JS islands** for interactions that cannot wait for a round trip, registered as trusted code; LiveView-style websocket push later.

**Out of scope:** WebAssembly clients, and a Lean-to-JavaScript backend unless offline or rich-client apps become a real requirement.

**Exit criterion:** the bank app has a working web UI with checkout, no application logic on the client, and the paid-state invariant proved.

## Phase 8: App kit (`Lanes.Kit`, optional)

Optional tools for applications that need them. Nothing here is required, and nothing imposes a project layout; each tool states the invariant it makes provable.

| Tool | What it is | What becomes provable |
| --- | --- | --- |
| Persistence | Event sourcing: an actor's mailbox is a durable log, state is `step` replayed over it, with snapshots; typed queries for read models | State after recovery equals state before the crash |
| Migrations | Versioned schema and event upgrades in Lean | Every migration preserves app invariants |
| Auth and sessions | Cookies, sessions, CSRF tokens, password hashing; SHA-256, HMAC and Argon2 or bcrypt in Lean (no FFI) | Primitives match their specs; state-changing requests carry a valid session and token |
| Forms and validation | Typed decoding from form data into messages, errors rendered back | No unvalidated input reaches `step` |
| Jobs and schedules | Durable `after` messages and cron on persistent mailboxes | Exactly-once processing, given an idempotent handler |
| Mail and webhooks | SMTP and outbound webhook adapters | Delivery attempts bounded and retried per the stated model |
| Config and secrets | Environment configs and encrypted credentials | (Operational) |
| Deploy | Single native binary, Dockerfile generator, documented TLS proxy | (Operational) |

**Templates, not conventions:** `lanes new` offers starting points (`--web`, `--service`, `--protocol`) that users are free to reshape.

## Agent workflow and developer experience

Make the work uniform enough that agents can design, implement and verify a system largely on their own, with humans reviewing specifications.

### The loop an agent runs

1. Write a small abstract spec, then actors and their `step` functions; run property-based tests on `step`.
2. Run the model checker on a small instance; fix counterexamples from their traces.
3. State invariants, refinement to the spec and liveness properties; check them on small instances, using the counterexample-to-induction finder to strengthen invariants.
4. Prove them: `lanes prove` lists open obligations, all in a few uniform shapes; the agent discharges them with Lean tactics and Mathlib.
5. Run `#trusted_report` and the linearizability checker before shipping.

**Humans review the spec:** the abstract specs, invariants, environment assumptions and the trusted-code allow-list. Proofs are machine-checked and need no review.

**Developer experience:** `lanes new` templates, rebuild-on-save dev server, error pages in the browser, a console attached to a running system, structured logs, and a tutorial that takes one app from empty to fully proved.

## What fits and what does not

Lanes pays off when an invariant whose violation costs money or trust can break through concurrency, retries, partial failure or message ordering.

| Fit | Examples |
| --- | --- |
| Strong | Ledgers and payments, workflows and sagas, coordination services (rate limiters, leases, locks), replicated protocols (Raft, Paxos, CRDT sync), DynamoDB-style stores, session-based web apps, policy engines |
| Works, less benefit | Plain CRUD where correctness lives in the database; integration-heavy glue whose guarantees rest on models of third-party services; per-record data transforms |
| Poor | GPU and numeric workloads, storage engines and packet data planes (hot paths needing memory-layout control), hard real-time and embedded code, offline-first and canvas-heavy clients, exploratory data science |

For poor fits, the usual pattern still applies: coordination in Lanes, the hot path as a separate service behind an adapter, its behaviour stated as an environment assumption.

## Risks and open questions

| Risk | Impact | Mitigation |
| --- | --- | --- |
| Proof effort for system properties without SMT automation | Slower proofs of protocols | Three-level structure keeps invariants at the protocol level; obligation automation; agents for the hard pairs; Veil optional at design time. Measured on the kv-lean port |
| Model-checker state explosion | Only tiny instances checkable | Symmetry reduction, random simulation, bounded instances |
| Lean, Mathlib and CSLib churn | Upgrade work | Follow CSLib's toolchain; pin and upgrade deliberately |
| `Std.Async` and `Std.Http` are young | Runtime bugs, API changes | Thin wrappers, trace checking, upstream fixes |
| No preemption | One slow `step` stalls its thread | Total, short steps; heavy work in separate Tasks |
| No TLS or HTTP client in Std | No direct HTTPS calls without FFI | Reverse proxy; minimal Lean HTTP client |
| Concurrent runtime remains trusted | Bugs below the semantics | Keep it small; trace checking |

### Open questions

- [ ] Typed actor references across actor kinds: dependent types, or one message sum type per system?
- [ ] How fairness assumptions are presented so users can see what "eventually" depends on
- [ ] Event-log snapshot frequency and retention
- [ ] How dynamic cluster membership is modelled
- [ ] Which parts of `Lanes.Semantics` and `Lanes.Temporal` to upstream into CSLib, and when

## Prior art and sources

| Work | What Lanes takes from it |
| --- | --- |
| CSLib | LTS, simulation and bisimulation, infinite executions, `LeadsTo`, fair scheduling, FLP's actor-shaped `Algorithm`, consistency models |
| Veil | Network and fault options; checker engine design (parallel search, fingerprinting) to port under Apache-2.0; invariant-synthesis ideas |
| Lentil | Temporal-logic proof mode design |
| Verdi (Coq), IronFleet (Dafny) | Handlers as functions, generic network semantics, refinement from code to protocol |
| P and PObserve, TLA+/TLC and trace validation, Ivy, Stateright | Abstract specs with refinement, actor model checking, liveness-to-safety, conformance checking, actors that run unchanged on a real network |
| Jepsen, Porcupine | History-based linearizability checking |
| Erlang/OTP, Orleans, Akka, Phoenix LiveView | Supervision, single-owner actors, server-rendered sessions |
| templ, HTMX, Triptych | Typed components, hypermedia updates |
| FoundationDB, TigerBeetle | Deterministic simulation |

**Lean references:** `Std.Sync.Mutex`, `Std.Async`, `Std.Http`, Tasks and Threads, Lean FRO roadmap.
