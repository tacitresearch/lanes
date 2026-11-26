# Decisions

Decisions taken while implementing `DESIGN.md`: the ones it left open, and the places where the
implementation departs from its sketches. Each entry gives the decision and the reason. Newest
last.

## D1. Message typing: per-actor message types, indexed by identity

*Settles DESIGN "Decisions to settle" 1 and the open question on typed references.*

A `Signature` has `Id : Type` and `Msg : Id → Type`. `Effect.send (to : σ.Id) (msg : σ.Msg to)`
is checked by Lean: an identity is the typed reference. There is no `ActorRef M` wrapper and no
existential over message types.

Why: the sketch `send {M} (to : ActorRef M) (m : M)` quantifies over a type inside `Effect`. That
puts effects in `Type 1` and makes messages in flight impossible to compare or hash, which the
model checker and the semantics both need. Indexing by identity keeps everything first-order
data, keeps full typing, and needs no casts.

## D2. Identities name actors that always exist (virtual actors)

There is no spawn effect and no registry in the semantics. Identity types may be infinite
families (`account (n : Nat)`); an actor that has never run is in its `init` state and starts on
its first message. Actors listed in `System.boot` start when the system does.

Why: the global state is then a total function from identities to states, which is the simplest
thing to state invariants and refinement maps over. Dynamic populations (one session actor per
user) need no extra machinery. This is the Orleans model.

## D3. `Effect` is `send | emit | after | cancel | stop`; no `io`, no `reply`

*Departs from the DESIGN sketch of `Effect`.*

- `io (req) (onDone : ExtResponse → Msg)` is gone. An external system is an actor identity whose
  behaviour in the semantics is its model and whose behaviour in production is an adapter
  (DESIGN Phase 5 already says this). Calling it is a `send`; its answer is an ordinary message.
- `reply` is `emit (out : σ.Out)` for answers leaving the system, and `send` between actors.
- `cancel` is new. A timer is identified by its message: `after` on a pending timer restarts it,
  `cancel` disarms it.

Why: a function inside an effect (`onDone`) cannot be stored in a state that must be hashed and
compared. Timers without cancel leave stale timers pending, which multiplies model-checker
states for protocols such as Raft that reset election timers.

## D4. The system boundary is explicit: `In`, `Out`, `accept`

A signature declares external inputs `In` and outputs `Out`. `System.accept : In → (i : Id) × Msg i`
routes an input to an actor. Internal messages cannot be injected from outside.

Why: invariants of protocols do not survive forged internal messages, so "any message may
arrive" is the wrong open-system semantics. Inputs and outputs are also exactly the visible
labels for refinement to a service spec.

## D5. Start is recovery

`Actor.recover : S → S × List Eff` runs on every start, including the first, and returns the
state to resume from with startup effects. The default keeps nothing (`fun _ => (init, [])`).
A crash, or `stop`, loses the actor's timers and the mailbox contents that arrived over links
that never lose messages.

Why: rule 3.3. One start path means the recovery path is the one that is proved and the one that
runs. `recover` as a function on the surviving state says precisely what is durable, without
committing to a storage design yet.

## D6. One executable definition of the semantics

`SysState.step : EnvModel σ → SysState sys → Event σ → Option (SysState sys)` in
`Lanes/Actors/World.lean` is the meaning of a system. The scheduler, the model checker and trace
replay call it; `Lanes.Semantics` wraps it as a CSLib `LTS`. It imports only `Std`.

Why: no second model to keep in sync, and the checker is sound by construction
(`SysState.step_of_mem_successors`). Network and fault models do not change the state type; they
decide which events are enabled.

*Consequence for layering (rule 1.6):* the step function sits below the runtime, and the CSLib
wrapper and proofs sit beside it, imported by neither the runtime nor apps' executable code.

## D7. `Actor` takes its effect type as a parameter

`Actor S Msg Eff`. Actors in a system use `Eff = Effect σ i` (`σ.Actor i S`). Library actors
keep `Eff` abstract and are placed in a system with `Actor.mapEff`.

Why: a reusable actor (a rate limiter, a Raft node) must not mention the signature of the system
it ends up in. Invariants transfer along `mapEff` (`Actor.Invariant.mapEff`).

## D8. The model checker stores full states

`Check.search` keeps every state and compares exactly, where Veil stores 63-bit fingerprints.

Why: state counts are then exact and comparable with TLC, and a hash collision cannot silently
drop states. Fingerprinting and parallel search come with the v2 engine, with an exact mode kept
for validation.

## D9. Library files use Lean's module system

`module`, `public import`, `@[expose] public section`, as CSLib does. Examples and tests are
plain files.

Why: explicit public surface (rule 1.3), faster rebuilds, and CSLib and Mathlib already require
it of anything upstreamed.

## D10. Toolchain and pins

Lean `v4.37.0-rc1`, CSLib pinned by commit in `lakefile.toml`, Mathlib as CSLib pins it.
License Apache-2.0, matching CSLib, Mathlib and Veil (whose checker design is followed).

## D11. Two import roots: `Lanes` and `Lanes.Semantics`

`import Lanes` is the runtime layer (Std only). `import Lanes.Semantics` adds the proof layer
(CSLib, Mathlib). Executable code imports the first; proof files import the second.

Why: measured. A test binary that imported the proof layer was 157 MB; the same binary on the
runtime layer is 8 MB. Mathlib also defines the token `<i`, which breaks `<input>` in templates.
`lanes lint` enforces the split (`layering`).

*Still open:* an app that never proves anything still downloads Mathlib, because Lanes is one
package. DESIGN accepts that cost ("a download, not hours of compiling"). If it hurts adoption,
the fix is a second package for the proof layer, which is a packaging change only.

## D12. Template tags have no space after `<`

`<div>` is a tag; `a < b` is a comparison. The grammar requires the tag name to follow `<`
directly.

Why: found by building the generated app. Without the rule, `if count < limit then (…)` in any
file importing Lanes parsed `<limit then` as the start of a tag and failed.

*Since extended:* the syntax is scoped (`open scoped Lanes.Html`), so files that are not views
are unaffected, including `a<b` written without spaces.

## D13. The runtime orders steps with one logical clock

Every step takes a number from a global counter and each message carries its sender's number.
When an actor stops, messages numbered at or before the stopping step are dropped with the
mailbox and later ones are carried into the next mailbox.

Why: `SysState.down` says precisely which messages a stopping actor loses. Without the clock,
"sent before the stop" depends on thread timing and recorded traces do not always replay.
With it, the recorded trace ordered by step number is a run of `SysState.step`, which is what
`Tests/Runtime.lean` checks.

## D14. Proofs of system invariants go through per-event lemmas

`Lanes/Actors/Step.lean` states, for each event, when it is enabled and the exact next state
(`step_deliver`, `step_drop`, …). A system invariant proof cases on the event and rewrites with
these; conservation proofs add `sum_update` and `sum_map_erase` from `Lanes/Semantics/Sums.lean`.
`Examples/BankProofs.lean` is the worked example and the shape `lanes prove` will generate.

## D15. JSON is a `Std`-only port of `Lean.Data.Json`

`Lanes.Json` (`Lanes/Data/Json/`) is the value type, parser, printers and `ToJson`/`FromJson`
classes of Lean core, ported so that nothing imports `Lean`. It differs from the original in
four ways:

- **Total.** No `partial`. The parser is written directly over the positions of the input
  (`s.Pos`) and not in `Std.Internal.Parsec`, whose results do not record that the position
  advanced; each function returns a proof of that, and recursion is on the bytes left to read.
- **Canonical values.** A `JsonNumber` carries a proof that it has no trailing fractional zero,
  and an object is an array of fields sorted by key (built by `Json.mkObj` or the parser), where
  the original uses `Std.TreeMap.Raw`. Structural equality is then equality of documents, so
  `Json` has `DecidableEq` and a `Hashable` that agrees with it, and printed key order is fixed.
- **Bounded.** `Json.parse` takes `maxDepth` (default 128) and `maxDigits` (default 1000, for
  both the digits of a number and its exponent) and rejects input beyond them.
- **Strict.** An unpaired `\u` surrogate is an error, not U+FFFD.

There is no `deriving` handler (it needs `Lean` meta code); instances for structures are written
by hand. `LawfulJson` states that an encoding loses nothing.

Why: any `import Lean` takes a compiled binary from about 5 MB to about 137 MB, and runtime
modules must stay small (design decision 5). Canonical values make `Json` usable in actor
messages and states, which the model checker compares and hashes (D8).

## D16. An actor never waits inside a step

A send whose receiver's mailbox is full goes to the sender's outbox, and a separate task delivers
the outbox in order. Inputs from outside are where back-pressure applies: `Runtime.input` waits
and `Runtime.tryInput` refuses, which the HTTP adapter turns into `503`.

Why: waiting inside a step deadlocks as soon as an actor sends to its own full mailbox, or two
actors fill each other's. The semantics has no bound on messages in flight, so losing or
refusing a send between actors would break conformance; refusing at the boundary does not.
The cost is that the outbox is unbounded, which is stated in `TRUSTED.md`.

## D17. URL attributes are rendered through `Html.safeUrl`

`href`, `src`, `action`, `formaction` and `xlink:href` keep relative URLs and the schemes
`http`, `https`, `mailto` and `tel`. Anything else renders as `about:invalid#blocked`. The check
is in `Attr.render`, so it covers values built without the template macro too. `<script>` and
`<style>` take no children in templates.

Why: escaping stops text becoming markup but does not stop `javascript:` in a link. Checking at
render time needs no extra types in views. The price is that `data:` and other schemes cannot be
used in those attributes yet.

## D18. The runtime is a proved kernel inside a thin shell

*Supersedes D13 and D16.*

`Lanes/Actors/Kernel.lean` holds every runtime decision as pure functions over a hash map of
actors and a queue: accept an input, take the oldest message (starting its receiver if it is
down), fire a timer. `Kernel.abs` reads a kernel state as a `SysState`, and
`run1_sound`, `accept_sound`, `fire_sound` and `abs_boot` prove each operation is a run of
`SysState.step` under `Kernel.env`, with the reported events being that run.

`Lanes/Actors/Runtime.lean` is one task per shard that feeds the kernel from a bounded inbox
and carries out its commands (hand over an output, arm a timer).

Why: the first runtime was 400 lines of concurrent IO making decisions under locks. A review
found five defects in it and fixing them introduced a sixth. None of that logic needed to be
concurrent. As pure functions it is proved once, and the per-actor tasks, gate mutexes, logical
clock and outbox are gone. Recorded traces now replay by theorem; the repeat-run stress loop
went from twenty minutes to seconds.

Consequences:

- Actors in one shard do not run in parallel. Parallelism will come from several shards, each
  a system joined to the others by links, which the semantics already models.
- A stopped actor starts again on its next message. The eager restart policy and its budget
  are gone from the runtime; supervision returns as library actors with specs (rule 3.1).
- The only assumption about `Std.Async` is the inbox channel and the timer.
