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
