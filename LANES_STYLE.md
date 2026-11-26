# LANES_STYLE — Design and Code Guidelines

Nov 25, 2026 · Nathan Barry

These rules govern every Lanes API, application and proof, and complement the [Lean on Lanes design document](docs/DESIGN.md). Each rule states its reason, so humans and agents can judge cases the rules do not cover. They adapt TigerStyle, Ousterhout's deep-module design, Erlang/OTP, functional-programming practice and classic systems papers to Lean. Rule numbers (for example 3.4) are stable and are cited by lint checks and code reviews.

## 1. Architecture and modules

Keep essential state and logic in pure Lean that can be proved, and push everything accidental to a small, trusted edge. Most of the rules below follow from that split.

1. **Separate the essential from the accidental.** Essential state is what the users' problem needs (accounts, log entries, votes). Accidental state is what we add for speed or plumbing (caches, indexes, connection pools). Specs and actor state hold only essential state. Anything derived lives in a separate, rebuildable view with a theorem tying it back to the source. *Why:* Out of the Tar Pit traces most complexity to state and control flow, and to the accidental kinds above all.
2. **Write the spec first.** Every service starts with an abstract spec such as `KVSpec`, even a five-line one. If the interface cannot be specified, it is not ready to build. *Why:* Lampson's first hint. The spec is also the interface agents code against.
3. **Deep modules, narrow interfaces.** A module should hide a lot of behavior behind a small surface. Expose a few functions and an opaque state type, not record fields. One `Actor S Msg` with three message kinds beats five actors that forward to each other. *Why:* Ousterhout. Shallow modules move complexity into their callers.
4. **Don't complect.** Keep separate concerns separate: values from identity, `step` from scheduling, policy from mechanism, what from when. A function that both decides and performs is two functions. *Why:* Simple Made Easy. Interleaved concerns cannot be reasoned about, or proved, one at a time.
5. **Put end-to-end checks at the ends.** Duplicate suppression, ordering and crash recovery belong to the application endpoints: idempotency keys, client sequence numbers, the spec-level operation id. Transport-level retries are an optimization, never the correctness argument. *Why:* Saltzer, Reed and Clark. Only the endpoint knows what "done" means.
6. **No module cycles, no tangles.** The dependency graph runs one way: Kit → Web → Adapters → Runtime → Semantics → Spec. Lower layers never import upper ones. *Why:* cycles make every change global and break incremental proofs.
7. **Use the obvious name, once.** One concept gets one name across code, specs and docs: a `Ballot` is never also a `Term`. Names state units and bounds: `timeout_ms`, `maxBatch`. *Why:* TigerStyle. Agents and proofs both match on names.

## 2. State and types

Encode as many invariants as you can in types, prove the rest as theorems, and leave runtime checks only for input from outside.

1. **Make illegal states unrepresentable.** Model a role as a sum type that carries its own data, not as flags spread across a record:

   ```lean
   inductive Role
     | follower (leader? : Option NodeId)
     | candidate (votes : Finset NodeId)
     | leader (nextIndex matchIndex : NodeId → Nat)
   ```

   This rules out a leader with no `matchIndex` or a follower holding votes, with no invariant to prove. Use subtypes (`{n : Nat // n < cap}`) and `Fin` for bounds. *Why:* Minsky. Every state the type rules out is an invariant you never have to prove.
2. **Parse, don't validate.** Adapters turn raw bytes into typed messages exactly once, at the edge: `parse : ByteArray → Except ParseError Msg`. Inside, `step` only ever sees `Msg`, never a raw string or an unchecked `Nat`. *Why:* King. A check whose result is thrown away has to be repeated, while a parsed value carries its proof.
3. **Data, calculations, actions.** Messages and effects are data. `step` and everything it calls are calculations: pure and total. Only the runtime and adapters perform actions. Keep the action layer as thin as possible and push logic down into calculations. *Why:* Grokking Simplicity. Calculations can be tested, replayed and proved, while actions can only be trusted.
4. **Effects are values, not calls.** `step` returns `List (Effect Msg)` and never runs `IO`. If a feature seems to need `IO` inside `step`, add a new effect constructor and a response message. *Why:* this keeps the semantics a plain LTS and makes the model checker run the real code.
5. **Explicit options, no hidden defaults at call sites.** Configuration is one `structure Config` with every field named and documented, passed in at `init`. No global mutable settings and no environment-variable lookups inside logic. *Why:* TigerStyle. A default hidden in a library has caused more outages than any explicit value.
6. **Bounded everything.** Every queue, map, retry loop and batch has a stated maximum in its type or `Config`, and the spec says what happens at the limit (reject, shed, back-pressure). *Why:* TigerStyle. Unbounded structures are where liveness and memory bugs hide, and bounds keep the model checker finite.

## 3. Actors and failure

The Lanes failure rule combines Erlang and crash-only software: when something goes wrong, crash fast and let another actor recover, with the recovery path proved.

1. **Let it crash, inside a supervisor.** An actor that hits a state its spec does not cover emits `stop` instead of limping on. Its supervisor, an ordinary library actor with a pure `step`, decides whether to restart, escalate or give up, under a stated restart budget (`maxRestarts` within `window_ms`). *Why:* Armstrong's rule is to let some other process fix the error. Defensive code inside a worker hides the bugs the model checker should find.
2. **The runtime is the error kernel.** Only the runtime and adapters may be trusted without proof, and they stay small. Every app actor is untrusted in the sense that its crash must never corrupt another actor's state. *Why:* the Erlang error kernel. A small trusted base is what makes the trust boundary auditable.
3. **Crash-only: stop = crash, start = recover.** There is no separate clean-shutdown path. An actor starts only by running `recover` over its durable log or snapshot, and the semantics model crash at every step. So the path we prove is also the path that runs on every restart. *Why:* Candea and Fox. A recovery path that rarely runs is a recovery path that does not work.
4. **Every external request is idempotent and has a deadline.** Effects carry an idempotency key and a timeout. A retried `io` must give the same result as the original, or the spec must say why not. *Why:* crash-only systems retry, and retries are only safe on idempotent operations.
5. **Prefer the standard behaviours.** Before writing a bespoke actor, check `Lanes.Behaviours`: `Server` (request and reply), `StateMachine` (explicit states, like `gen_statem`), `Supervisor`, `Pool` and `Timer`. Each comes with its spec and refinement proof. *Why:* OTP behaviours separate the generic part, written and proved once, from the app-specific callbacks.
6. **Make actions atomic.** One message equals one atomic transition. If an operation must touch two actors atomically, the spec must say so, and the design goes through a protocol such as 2PC or a single owner, never through shared state. *Why:* Lampson. Atomic actions are what keep crash recovery tractable.
7. **Batch at the edges, not in the logic.** Adapters may coalesce writes, fsyncs and network sends. `step` still sees one message at a time, and a refinement proof shows the batch is unobservable. *Why:* Lampson and TigerStyle. Batching buys throughput, and putting it at the edge keeps the proofs simple.
8. **Back-pressure, not unbounded mailboxes.** Every mailbox has a bound. When it is full, the sender gets an explicit `busy` reply or the runtime sheds load as the spec says. *Why:* an unbounded mailbox only turns overload into memory exhaustion later.

## 4. Code inside `step`

TigerStyle carries over to Lean almost unchanged. Lean adds one twist: an assertion should become a type or a theorem wherever it can.

| TigerStyle rule | Lanes form |
| --- | --- |
| Assert pre- and postconditions, two per function on average | State them as a type (subtype, `Fin`), a theorem next to the function, or a spec invariant. Use `assert!` only at adapter boundaries, where input is untrusted. |
| Put a limit on everything | Bounds go in types or `Config`. Recursion uses structural or `termination_by` measures, with no `partial` in logic. |
| Push ifs up, fors down | Branch on message kind once, at the top of `step`, with one `match` and one handler per constructor. Helpers are branch-free calculations over collections. |
| Functions of 70 lines or fewer | Same rule. One handler per message constructor, each short enough for one proof goal. |
| No recursion, static allocation | Total functions with `termination_by`. No `IO.Ref`, `ST` or `unsafe` in logic, and FBIP for in-place updates. |
| Handle every error | Use `Except` or a sum type in the result, never `panic!` or `default` in logic. An unexpected state leads to `stop` (rule 3.1), never a silent skip. |
| Zero technical debt | Do not merge a `sorry`, an `admit` or a TODO inside a proof. A missing proof becomes an explicit axiom listed in `TRUSTED.md` (rule 5.5). |
| Name with units, longest qualifier last | `timeout_ms`, `log_index_max`, `replyTo`. Use namespaces, not prefixes. |
| Simple control flow | Do not use `do` blocks with `mut` in `step` unless the result really is clearer. Prefer `match` and folds. |

Two additions for Lean itself:

- **Total by default.** Use no `partial def`, `unsafe` or `@[implemented_by]` outside `Lanes.Trusted`. Each use goes through the audit (Phase 6).
- **Small proof terms.** If a proof needs over 30 lines of manual tactics, extract a lemma or improve the design. Proof pain is a signal about the design, not something to grind through.

## 5. Specs and proofs

Specs are code. They are held to the same naming, size and review rules, and the model checker runs them before anyone tries to prove them.

1. **Check before you prove.** Every invariant and refinement map is model-checked on small bounds (3 nodes, 2 values, depth 12 or more) before proof work starts. A counterexample costs seconds, while a failed proof attempt costs hours.
2. **One invariant, one name, one sentence.** Each invariant is a named `def` with a docstring stating it in English: `/-- At most one leader per term. -/ def electionSafety`. Avoid anonymous conjunctions over 3 clauses, and split them so `inv_split` and CTI reports name the clause that failed.
3. **Add a vacuity check to every invariant.** Pair each safety property with a `sometimes` check proving the guarded state is reachable. *Why:* an invariant over an unreachable state passes trivially, a common way TLA+ models give false confidence.
4. **Keep refinement maps boring.** An abstraction function should be a short, total projection. If it needs history or prophecy variables, add them to the implementation state explicitly and document why.
5. **Trusted code is listed, not hidden.** Every `axiom`, `@[extern]`, `@[implemented_by]` and `unsafe` goes in `TRUSTED.md` with an owner, a reason and a test that exercises it. CI fails on unlisted ones, using `#print axioms` on the top theorems.
6. **Specs say what happens at limits and on faults.** Each spec states its behavior on full queues, timeouts, crashes and partitions, even if that behavior is just "returns `unavailable`". A spec that only covers the happy path is a wish.
7. **Liveness is designed in, not proved after.** Each liveness property names its fairness assumption and its ranking measure in the design doc before any code is written.

## 6. Enforcement

A rule that no tool checks will drift, so most rules here map to a `lanes lint` check, a CI gate or an agent instruction.

| Check | Rule | How |
| --- | --- | --- |
| `no-io-in-step` | 2.4 | Elaborator walk: `step` and anything it calls must not mention `IO`, `ST`, `BaseIO` or `unsafe`. |
| `total-logic` | 4 | Reject `partial`, `panic!` and `default`-as-error outside `Lanes.Trusted`. |
| `trusted-listed` | 5.5 | `#print axioms` on top theorems, diffed against `TRUSTED.md`. |
| `no-sorry` | 4 | Fail on `sorry` or `admit` in merged code. |
| `bounded` | 2.6 | Flag `List`, `Array` or `HashMap` fields in actor state with no bound in the type or `Config`. |
| `layering` | 1.6 | Import graph must follow the layer order. Cycles fail. |
| `field-leak` | 1.3 | Warn when another module reads a state structure's fields directly instead of through its API. |
| `shallow-module` | 1.3 | Warn on modules whose public surface is large relative to their body. |
| `fn-length` | 4 | Warn over 70 lines per `def`, and over 30 lines per manual proof. |
| `vacuity` | 5.3 | Every invariant has a passing `sometimes` check in the checker run. |
| `idempotent-io` | 3.4 | Every `Effect.io` carries an idempotency key and a timeout. |

CI order: build, then `lanes lint`, then the model checker on small bounds, then proofs, then the trusted-code diff. Checking runs before proving, so counterexamples show up early.

**`AGENTS.md` snippet (goes in every generated app):**

```markdown
## Lanes rules for agents
- Read LANES_STYLE.md before writing code. Cite rule numbers in PR descriptions when a rule shaped a choice.
- Write or update the spec first; model-check it before writing the implementation or a proof.
- step is pure: no IO. New external work = new Effect constructor + response message.
- Encode invariants in types first, theorems second, runtime asserts only at adapters.
- Never add sorry, partial, unsafe or an axiom without listing it in TRUSTED.md.
- On an unexpected state, emit stop; do not add defensive fallbacks.
- Run `lanes lint && lanes check` before claiming a task is done.
```

## Sources

| Source | Used in |
| --- | --- |
| TigerStyle, TigerBeetle | 2.5, 2.6, 4 |
| John Ousterhout, *A Philosophy of Software Design* (deep modules, information leakage) | 1.3, 6 |
| *Out of the Tar Pit*, Moseley and Marks, 2006 | 1.1 |
| *Hints for Computer System Design*, Butler Lampson, 1983 | 1.2, 3.6, 3.7 |
| *Simple Made Easy*, Rich Hickey, 2011 | 1.4 |
| *End-to-End Arguments in System Design*, Saltzer, Reed and Clark, 1984 | 1.5 |
| *Effective ML*, Yaron Minsky (make illegal states unrepresentable) | 2.1 |
| *Parse, don't validate*, Alexis King, 2019 | 2.2 |
| *Grokking Simplicity*, Eric Normand (actions, calculations, data) | 2.3 |
| *Making reliable distributed systems in the presence of software errors*, Joe Armstrong, 2003 | 3.1, 3.2 |
| OTP Design Principles, Erlang/OTP | 3.1, 3.5 |
| *Crash-Only Software*, Candea and Fox, HotOS 2003 | 3.3, 3.4 |
