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

Measured again on 2026-11-27 for the module system's `meta import`: a library that does
`public meta import Lean`, imported by an application either way, still gives a 137 MB binary,
because Lake links it. So sugar for applications (a declaration that defines a type together
with its codec, or a system together with its signature and instances) has to be a macro, which
needs only `Init` and sees the declaration's syntax, not a deriving handler or an elaborator.


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

## D19. The HTTP adapter's logic is a gate actor

`Lanes/Http/Gate.lean` defines `gate`, an actor that parses each request into an input, keeps
the list of waiting requests, and answers each one: with the system's response, with `504` when
its timer fires, or with `503` beyond `maxPending`. `gated sys` is `sys` with the gate in
front; the inner actors' outputs become messages to the gate. `Lanes/Env/Http.lean` serves
`gated sys` and only moves bytes.

Why: the first adapter kept the waiting table in a mutex and the deadline in a per-request
`select`. A review found two defects there. As an actor the logic is checked and proved
together with the application. `Tests/Gate.lean` explores every race between a response and its
deadline on two requests and shows each is answered exactly once. `gate_bounded` proves the
table's bound. `Lanes/Http/GateSound.lean` proves the safety half for every system, bridge and
configuration:

- `Http.answered_le_arrived`: in any run, no request id is output more often than it was input.
  The claim is about arrivals because a reused id may rightly be answered once per arrival.
  The environment may crash and restart any actor and lose, reorder and duplicate on any link,
  except that the link from outside to the gate does not duplicate. That exception is needed:
  a duplicated arrival that the bridge refuses is refused twice. `Kernel.env` meets it.
- `Http.answered_nodup`: so with distinct ids, which the adapter allocates, no id is answered
  twice.
- `Http.deadlines_armed`: while the gate is up, every waiting request has its deadline armed,
  in every environment.

The first is proved by a count along the run: answers output, answers in the outbox, the id's
place in the pending list and arrivals in flight never exceed the arrivals so far. It needs no
history variable and no `Nodup`, because the pending list is counted, not tested for
membership. The file is `GateSound`, not `GateProofs`, because it imports only `Std` and
`lanes lint` keeps the name `…Proofs.lean` for files that may import Mathlib.

Not proved: that every arrival is answered. That is liveness. It rests on timers firing and on
the gate not crashing, since a crash loses the gate's mailbox.

## D20. History variables are ghosts with an erasure theorem

`Lanes/Actors/Ghost.lean`. A `Ghost` gives each actor a history, updated on every step from the
state and the message. `SysState.erase_step` proves the system with ghosts takes exactly the
steps of the system without them, so `System.Invariant.of_ghost` carries an invariant proved
with histories to the real system.

Why: protocol safety often needs the past ("this node voted for that candidate in term 3").
The alternatives were to store the history in the actor's real state, which costs memory at run
time and changes the code being verified, or to prove about traces, which is heavy. A ghost
costs nothing at run time, and there is a theorem saying so.

## D21. A proof rule for invariants no fault can break

`Lanes/Actors/Monotone.lean`. `System.Inductive.of_monotone` proves an invariant under every
environment model from five cases: the blank state, an input, an actor's step, an actor's
recovery, and that removing messages, timers and outputs keeps it.

Why: a direct proof has eight event cases and must reason about erased messages, filtered
mailboxes and crashes, although loss, duplication, reordering and crashes can only remove
things or replay a step. This is the usual "the network is a set of messages ever sent"
argument of Raft and Paxos proofs, stated once for the Lanes semantics. It does not fit
invariants that count messages in flight, such as conservation of money; those are false under
loss anyway and are proved directly for a faultless environment.

## D22. Routes are values with a proof; htmx attributes come from them

`Lanes/Http/Route.lean`, `Lanes/Html/Htmx.lean`. A `Path α` is a printer and a parser with a
proof that parsing what was printed gives the value back. `Route.match?_link` follows for every
route. Views take URLs and htmx attributes from routes (`Hx.request route value`), and a
request is decoded with `Http.dispatch` over the same routes.

Why: a view that hard-codes `hx-post="/transfer"` and a decoder that matches `["transfers"]`
is a bug no type catches. With one value for both, a link to a missing route does not compile,
and `POST` to a `GET` route cannot be written.

Templ features taken: components, fragments (`<>…</>`), attribute splices (`{attrs}`),
conditional classes (`Html.classes`). Not taken: bare text children. Lean's tokenizer would
split arbitrary text into Lean tokens, so text is a string literal.

A `Path` also carries a proof that no segment it prints is empty, `.` or `..`. Those do not
survive a URL: an empty first segment makes `//host`, which a browser reads as another site, and
browsers remove dot segments however they are escaped. Free text in a path is therefore a
`Slug`, which cannot be one of them, and a number matches only in its canonical spelling.

## D23. Time is data, and a shard is a thread

*Refines D18, after a second independent review.*

The kernel now owns the clock's meaning. The shell reports what the clock says
(`Kernel.advance`); the kernel keeps an agenda of pending timers, says which are due
(`Kernel.step`), how long nothing will be (`Kernel.wait`) and whether the shard is idle
(`Kernel.quiet`), and does a bounded batch of work in one pure call (`Kernel.runBatch`). There
are no timer commands, no tokens handed to the shell and no sleeping task per timer. The shell
sleeps once, until the next deadline or the next input.

The shard's loop runs on a thread of its own, not as an `Async` task, and keeps the kernel in a
reference that each operation empties and refills.

Why:

- The review found that cancelled timers kept sleeping and then flooded the bounded inbox, and
  that waiting for "no timers" waited for cancelled ones. With the agenda in the kernel,
  cancelling is a pure update and there is nothing to leak.
- It found that no theorem said what the kernel tells the shell to do. With timers inside, the
  only thing left to tell is the outputs, and `Kernel.exec_outputs` proves they are exactly the
  outputs of the run.
- It found that a message cost time linear in the number of actors. The cause is in Lean's
  runtime, not in any logic: an object another thread may see is never updated in place, and
  state held across an `await` is handed to the task system. So an `Async` loop copies its
  state on every update. A plain loop on its own thread does not. `Tests/Scale.lean` measures
  it: the same cost per message at 1,000 and at 100,000 actors.

Consequences:

- A program whose `main` returns without stopping its runtimes does not exit, as with any
  thread that is not a daemon. `Http.Server.stop` stops the runtime.
- `stop` means stop now: the shard finishes the commands already handed over and one batch,
  then ends, even if actors still have messages for each other. Draining could never end.
- Every kernel operation is total and consumes the kernel: there is no "nothing to do" result
  that would force the caller to keep a second reference.
- The agenda holds exactly the pending timers, whatever the shell does
  (`Kernel.exec_wellFormed`, in `Lanes/Actors/KernelTimers.lean`). Soundness does not depend on
  it (`fire_sound` holds for any timer the shell could name); promptness does. From it: a timer
  that is due is fired and not slept through, a kernel that says there is work does some, the
  shell sleeps until exactly the earliest deadline, and idle means nothing queued and nothing
  pending (`Kernel.WellFormed.wait_of_due`, `step_of_due`, `step_events_ne_nil`, `wait_for_ms`,
  `quiet_iff`).
- A timer that is due and a message that is queued take turns (`Kernel.timerTurn`,
  `Kernel.timerNext`). The first version always fired the due timer, and a later review showed
  what that costs: an actor that arms `after 0` again in its timer's handler, or enough periodic
  timers that one is always due, kept every message waiting for ever. Always taking the message
  would starve timers the same way. With turns, each waits for at most one step of the other
  kind (`Kernel.WellFormed.step_of_queued`, `step_of_due`). One bit of state is enough and the
  bound is the smallest there is; counters or priorities would need a policy nobody has asked
  for.
- The batch of work the shell asks for is a kernel operation like the others (`Kernel.Op.batch`),
  so `Kernel.exec_reachable`, `exec_outputs` and `exec_wellFormed` are about the calls the shell
  makes, not about single steps it never makes.
- Proving it found a defect. `Kernel.fire` erased the agenda entry at the `due` it was given
  before looking whether the timer it was given was pending. A shell that fired a real `due` at
  another actor or for another message made the kernel forget the timer that `due` belonged to:
  it stayed pending, never fired, and the shard counted as idle. `fire` now leaves the agenda as
  it is unless the timer is pending (`Tests/Kernel.lean`). The shell in `Runtime.lean` reaches
  `fire` only through `step`, which names the agenda's own entry, so it could not do this.

## D24. Durability is a journal of what the kernel was asked, replayed

*Departs from `DESIGN.md`, which backs `Actor.recover` with stored state.*

A shard keeps a journal: every input, every clock reading and every batch of work it asks of
the kernel, appended to a file and synced before any output of that work is handed over. After
the process dies, the shard replays the journal through the same kernel and is in the state it
was in.

Why this and not storing actor states:

- The kernel is a pure function of the requests made of it, and `step` cannot do IO, so replay
  gives the same state by construction. Other systems that replay a log have to trust that
  handlers are deterministic; here the type of `step` says so.
- A process restart is then not a crash in the semantics at all. The run simply continues, so
  everything proved for a faultless environment, such as conservation of money, still holds
  across restarts. Storing states and losing the messages in flight would have made every
  restart a crash of every actor with message loss, and most such properties false.
- Only inputs need a codec, not every actor's state.
- It is the shape replication needs: a replicated shard is a replicated journal.

What it costs:

- One sync per batch before outputs leave. Batching more inputs per sync is the lever.
- The journal grows and replay takes longer until there are snapshots. Snapshots need a codec
  for states and are the next step, together with releasing idle actors.
- Outputs produced after the last sync mark may be handed over again after a restart: outputs
  are delivered at least once, and an adapter that must not repeat itself needs to deduplicate.
- Replaying a journal with changed code gives a different state. Upgrades will go through a
  snapshot. Until then the journal's header carries a name the application chooses for the
  system and its version, and a file with another name is refused.
- Opening a journal never repairs it. A write that did not finish is cut off, because that is
  what the death of the process leaves and it is proved to be all it leaves
  (`Journal.open?_cut`). Anything else that is wrong is refused and left alone: the first
  version cut the file at the first entry it could not read, which deleted a journal that was
  opened with the wrong codec.
- Time is the kernel's time. Timers do not advance while the process is down.

What a shard does in one turn (take an input if there is one, do a batch of work, and say what
to journal) is one pure function, `Journal.turn`. A turn in which nothing happens leaves the
kernel untouched, clock included, and journals nothing, so the journal describes the kernel
exactly at every moment (`Journal.turns_kernel`), with no assumption about the clock.

`Actor.recover` keeps its meaning: it runs when an actor starts again after stopping itself or,
under an environment model with crashes, after a crash.

What is proved: nothing new is needed for the kernel. `Kernel.exec_reachable` and
`Kernel.exec_outputs` already hold for any list of requests, so they hold for the replayed one.
What has to be proved is that the file gives back the list that was written
(`Lanes/Data/Frame.lean`, and the law every `Codec` carries), including when the last write was
torn. What stays trusted is that the shell syncs before it hands outputs over.

## D25. Composition is a join, and what survives it is projection

`Lanes/Actors/Join.lean`, `Lanes/Actors/JoinSound.lean`. `System.join a b wiring` is one
`System` whose actors are those of both; an output of one that the wiring routes to the other
is a message to the actor the other's `accept` names. `System.Reachable.left` proves that a
reachable state of the join, seen from `a`, is a reachable state of `a` alone under
`EnvModel.left`, and `System.Invariant.join_left` carries the invariants of `a` into the join.

Why this and not a calculus of open systems with assumptions and guarantees: a theorem about a
system already holds for every input and every environment model, so "whatever the other side
does" is what it already says. Nothing has to be added to a system for it to compose, and the
join is an ordinary `System`, so the checker, the runtime and every theorem apply to it.

Why the link from outside is `Link.network` in `EnvModel.left`: seen from `a`, messages from
outside and from each actor of `b` are all inputs, on one link. In the join each sender has its
own link, so the join may deliver them in an order, lose them or repeat them in ways no single
link model other than the most permissive one allows.

The proof is not the forward simulation it looks like. Two equal inputs from different senders
are two messages in the join and one kind of message alone; the join may deliver the newer and
keep the older, while `a` alone always removes the oldest of equal messages. So the induction
carries, for each state of the join, every way of leaving out messages from outside: alone,
`a` is simply never sent a message that the join is going to remove out of turn.

Consequences:

- The two sides are not alike, because a join boots `a` first. What the boot of `a` sends `b`
  is in flight before the first messages of `b` itself, and `b` alone can only receive inputs
  after its own boot. `System.Reachable.right` therefore holds up to `SysState.Equiv`, the
  order of messages on different links, which no actor can observe; `Tests/Join.lean` proves
  the exact statement false for two one-actor systems (`heralded_right_not_alone`). It holds
  exactly when the boot of `a` sends `b` nothing (`right_of_quiet_boot`). Invariants of actor states transfer on both sides; other
  invariants of `b` transfer when they do not depend on that order (`join_right`).
- The cause is in the semantics, not in `join`: `SysState.net` is one list, so a state records
  an order between messages on different links that nothing observes, and a system alone cannot
  have an input waiting when it boots. Allowing inputs before the boot, or stating reachability
  up to `SysState.Equiv` throughout, would make both sides exact. Neither was changed here.
- What is proved of `a` only for reliable inputs does not transfer. A system with one wire to
  the other and one to the outside would need two outside links to keep each one's model.
- `SysState.step_swap` (private for now) is the symmetry of `join`: the join with its sides
  exchanged takes the same steps. The right-hand theorems are the left-hand ones through it.
- `SysState.Equiv` started in the checker; it is in the core now (`Lanes/Actors/Equiv.lean`),
  since theorems about systems put together are stated up to it.

## D26. An adapter is a model of the outside and a handler, tested against each other

`Lanes/Actors/Outside.lean`, `Lanes/Env/Clock.lean`. Whatever a system does not contain (a
client, a clock, another service) reaches it through outputs and inputs, never through an
effect that does IO, so `step` stays pure and every answer from outside is in the journal when
a shard is replayed. An adapter for such a thing is two parts:

- an `Outside`: which inputs the thing may send, given what it has seen. The checker explores
  the system against it (`Outside.driver` with a few sample inputs), and theorems name it as
  their assumption;
- a handler: what the real thing does with an output, in IO.

A conformance test records a real run and checks it with `Outside.allows`: the real thing did
only what the model allows.

Why: a property checked against a model of the outside says nothing if the real outside does
something else, and nothing else ties the two together. The gate's guarantee assumed request
ids are never reused; that assumption is now `Http.outside`, and the real server is tested
against it.

Why a model and not an actor: an actor is deterministic, and what the outside does is a
choice. The semantics already puts every choice in the events, and inputs are events.

Consequences:

- `Runtime.idle` waits for the system, not for an adapter that is about to answer. A test waits
  for the answer it expects.
- Outputs are handed over in an order the semantics does not fix. A model that assumed the
  order of outputs was caught by the checker while this was being written.

## D27. Liveness: infinite runs, weak fairness per obligation, leads-to

`Lanes/Semantics/Liveness.lean`, `Lanes/Semantics/FairRuns.lean`,
`Lanes/Semantics/GateLive.lean`. Everything proved before this was safety. "Every request is
eventually answered" is about infinite runs, and only about those in which the system is not
held back forever.

- A run (`System.Run`) is an infinite sequence of states from the initial one. Each position
  takes an enabled event or stutters.
- An `Obligation` is an event the system makes happen itself: deliver a message, fire a timer,
  start an actor, hand over an output. `Obligation.Due` says when it is owed: the message is
  deliverable and its receiver is up, the timer is armed and its actor is up, the actor is
  stopped and has mail, the output is in the outbox.
- A step restarts an obligation (`Obligation.Restarted`) when the obligation is a timer and
  the step is one of its actor that arms it: among the effects of the actor's `step` or
  `recover`, computed from the state before, is `after _ msg` (`SysState.arms`). Nothing
  restarts a delivery, a start or an output.
- A run is fair (`Run.Fair`) when it is weakly fair to every obligation on its own: one that,
  from some point on, is due at every position and restarted at none is taken at a later
  position. For a timer: one that stays pending and is not armed again fires.
- `sys.LeadsTo env P Q`: in every fair run, a position where `P` holds is followed by one
  where `Q` holds.
- The proof rule is Lamport's WF1 (`LeadsTo.ensures_of_invariant`): from a reachable state
  with `P` and not `Q`, every step keeps `P` or reaches `Q`, one obligation is due, taking it
  reaches `Q`, and no step restarts it without reaching `Q`. Its premises are about single
  steps, like those of an invariant. The last one (`quiet`) is filled in for an obligation
  that is not a timer, so only a proof that rests on a timer states it.

Why this formulation:

- Stuttering, so that a system with nothing enabled has runs. What rules out a run that idles
  while there is work is fairness, not the shape of a run. TLA and CSLib's FLP do the same.
- Obligations are a type, not a set of events chosen per theorem. Inputs, drops, duplicates
  and crashes are the environment's choice and have no obligation, so fairness cannot be
  assumed of them even by mistake.
- Due is not the same as enabled. A stopped actor without mail can start where the
  environment model has `restarts`, and no one owes that start. So `restarts`, like
  `mayCrash`, only adds runs, and turning it on never makes a liveness theorem easier.
- Fairness is per obligation. Fairness to "some timer fires" lets one deadline wait forever
  while others fire, and then the liveness of one request does not follow. `DESIGN.md` said
  per mailbox; on an ordered link only the oldest message is deliverable, so there it is the
  same thing.
- Weak fairness, because it is enough for what stays due until taken (timers, outputs, the
  head of a link) and it is what a runtime that takes its work in turn provides. Strong
  fairness waits for a theorem that needs it.
- A timer that is armed again is not obliged to fire. The semantics leaves a pending timer
  that is armed again as it is, and a `timeout` may fire it at any moment; the runtime gives
  it a new deadline. Fairness first obliged every timer that stays pending to fire
  (`Run.Impatient`, kept for comparison). That described no run of the runtime in which an
  actor keeps a timer from firing by arming it again, which is what a keep-alive does, and in
  every fair run of a Raft model a follower that hears from its leader would have timed out
  anyway. So fairness now promises what the runtime does: a timer that stays pending and is
  not armed again fires. The semantics is unchanged: `World.lean` still lets any pending timer
  fire, so safety proofs cover a timer that fires early. Giving a timer an identity that
  arming changes, in the semantics as in the kernel, was the alternative. It would change
  the semantics, and the proofs about timers with it, for something only liveness needs.
- The new fairness is weaker, so there are more fair runs and a leads-to theorem says more
  (`Run.Impatient.fair`: every run that was fair before is fair now). What it costs is the
  fourth premise of the rule.
- CSLib's `ωSequence`, `LTS.OmegaExecution` and `ωSequence.LeadsTo` are used as they are. Its
  fairness is that of processes in the FLP algorithm, where a message in flight stays
  receivable; here an obligation can stop being due, so fairness of events is defined here.
- It lives in the proof layer. Runtime code has no use for infinite runs, and the sequences
  come from CSLib.

Consequences:

- The first liveness theorem: in any environment that does not crash the gate, a request
  waiting in the gate stops waiting (`Http.pending_leaves`), and an answer to it is handed
  over (`Http.pending_answered`). The obligation is the request's deadline, which
  `deadlines_armed` keeps due and no step restarts (`Http.deadline_not_restarted`): the gate
  arms a deadline when it admits a request, which was not waiting, and when it starts, which
  it does not do while it is up.
- The gate must not crash, and the theorem is false without that: the gate crashes after
  admitting a request, nothing obliges a start without mail, and the request stays in its
  state forever. Recovering it needs restart as an obligation or an assumption.
- Fair runs exist (`Lanes/Semantics/FairRuns.lean`). Every finite run extends to a fair run
  (`System.exists_fair_run_of_run`, machine closure), so every reachable state is on one
  (`System.Reachable.exists_fair_run`) and a leads-to theorem is never true for lack of runs
  (`System.LeadsTo.reachable`). It holds for every system and environment model with no
  assumption, infinitely many identities included. The fair run is the one `FairScheduler`
  makes (`Lanes/Actors/FairScheduler.lean`, executable, checked on runs in `Tests/Fair.lean`):
  it keeps the owed events in a queue and takes the one owed longest. The queue needs no list
  of all actors, because an event changes the timers of one actor at most, and that is what
  makes the proof work for an infinite signature. Being due is computable (`SysState.owed`,
  `Obligation.due_iff_owed`), so the schedule is a function and nothing is chosen classically.
- The scheduler counts a timer that a step arms again as owed from that step: it goes to the
  back of the queue. The existence proof did not need this, since a scheduler that fires every
  pending timer in its turn makes impatient runs and those are fair. It was changed so that
  the runs it makes are of the kind fairness now allows and the runtime produces: a timer
  that is armed again before its turn does not fire. The scheduler has turns and no clock, so
  a keep-alive stays quiet under it only when the step that arms it comes round first
  (`Tests/Fair.lean` has a watchdog that does and one whose keeper has stopped).
- What the change buys is a theorem (`Examples/WatchdogProofs.lean`). A dog arms its `silence`
  timer again at every `ping`. The run in which its keeper pings forever is fair, with the
  timer pending at every position and never firing (`exists_fair_run_never_barks`); in every
  impatient run the dog barks (`impatient_barks`).
- "Eventually" has no bound, and nothing here ties a fair run to the clock. The kernel's
  theorems about due timers are about steps; that the runtime's runs are fair is assumed.
- Fairness says nothing about a timer for as long as steps keep arming it again. That is the
  point for a keep-alive, and it means "the timer fires" needs "the arming stops" first: a
  proof that a follower times out has to show that heartbeats no longer reach it.
- The checker cannot check a leads-to property. Until it has a lasso search, the premises of
  the rule are checked as `always` properties (`Tests/Gate.lean`).

## D28. A shard is a system, and a cluster is runtimes with a router

`Lanes/Actors/Shard.lean`, `Lanes/Actors/Cluster.lean`. `System.shard sys hosts` is `sys` as a
shard that hosts some of its actors sees it: a message to an actor hosted elsewhere leaves as
an output (a parcel), a parcel arriving is an input, and an actor not hosted only forwards. A
cluster starts one ordinary runtime per shard and routes parcels between them, on a lane that is
never full so that two shards cannot block each other.

Why not a kernel that knows about shards: the kernel and its proofs stay as they are, each
shard keeps the journal it already has, and the same `System.shard` with a router over a socket
is a system spread over machines. The work moves to one theorem, that shards and parcels in
flight together stand for a state of the one system, which is about composition and not about
any kernel.

Consequences:

- Outputs of different shards are not ordered among themselves.
- A cluster has no journal yet. Each shard would journal the parcels it receives, so messages
  need a codec, and a restarted shard must be sent again what its journal does not have.
- Back-pressure is at each shard's outside inbox. Between shards nothing is refused, so a
  shard that falls behind is noticed only by its queue.

The theorem (`Lanes/Actors/ShardSound.lean`, `Lanes/Actors/Lossy.lean`). `System.split sys
hosts` is two shards joined, each parcel one emits an input of the other; a wired emit is a
direct send in a join, so a message between shards is one message in flight, as in `sys`.
`System.SplitReachable.merged`: in a run where every input from outside goes to the shard that
hosts its receiver and no parcel comes from outside, every state of the split, read as one
state, is a state `sys` reaches alone, up to `SysState.Equiv`. The proof is a forward
simulation, one event to one event of the same kind, carried by the invariant that nothing is
in flight to or from a copy that only forwards. Why it is not simpler:

- *Booting.* A join boots its left system first, and real shards boot independently, so the
  split's first state is `sys` booted in another order. Without stops that order is invisible
  up to `SysState.Equiv`. A boot actor that stops as it starts loses the messages already in
  flight to it, and which those are depends on the order: `fragile` in `Tests/Split.lean`
  reaches, split, a state it never reaches alone. The theorem assumes `System.SteadyBoot`
  (no boot actor stops as it starts, or the links to it are lossy). This is a property of
  booting shards one by one, not of `System.shard`, and the fix, if one is wanted, is in what
  a boot is.
- *State invariants need no assumption.* `System.Reachable.lossy`: whatever a system reaches,
  it reaches when every link may also lose messages, the same events with drops after each
  crash and stop. Where every link is lossy a stop loses nothing, so `SteadyBoot` holds, and an
  invariant of actor states proved for every environment transfers (`Invariant.split_state`).
- *Outputs.* Two equal outputs from different shards are two values in the split's outbox and
  one in `sys`, so the split may hand over the newer first. The correspondence is exact up to
  the order of the outputs waiting (`merged_exact`), which `SysState.Equiv` already ignores.
- *The copies that only forward.* `EnvModel.split` lets them neither crash nor restart by
  themselves; they are never started, because nothing is ever in flight to them. A statement
  for an arbitrary environment of the split would treat their starts and crashes as steps that
  change nothing.

## D29. A snapshot is a restart without the crash

`Lanes/Actors/{Kernel,Journal,Snapshot,Disk}.lean`, `Lanes/Env/Journal.lean`. A journal that only
grows makes a restart take as long as the shard has lived. A snapshot saves the kernel, and the
journal is cut at the point of the save.

- *Saving is a kernel operation.* A kernel has an image (`Kernel.image`: cells, queue, agenda,
  clock) and can be restored from it. The restored kernel is the same system state
  (`Kernel.abs_image_kernel`) and has the same timers on its agenda (`WellFormed.image`), so
  every kernel theorem covers it. It is not the same value, because a hash map built again is
  laid out differently. The usual way out is a theorem that kernels alike in everything
  observable behave alike, which is a congruence lemma for every kernel function. Instead the
  operation `snapshot` replaces the kernel by the one its image restores, and the shard goes
  on with that. The shard that keeps running and a shard started from the saved image then
  hold equal values, and equality needs no theorem. The cost is rebuilding the tables at each
  save, which is of the order of writing them. The gain besides the proof: recovery is
  exercised at every save, in production, and not only after a crash.
- *The snapshot is a memo of the replay.* The journal marks a save with an entry that carries
  its index in the shard's history. `Journal.resume` starts from a saved kernel and the entries
  after its mark. `Journal.resume_eq_recover`: that gives exactly what replaying the whole
  history from boot gives, kernel and outputs to hand over again, however many entries before
  the mark the file has lost. So everything that was true of recovery by replay stays true, and
  cutting the journal is justified by a theorem about lists.
- *What is refused.* A cut journal whose snapshot is gone, or a snapshot whose mark is not in
  the journal, does not start: replaying a cut journal from boot would give a state that never
  was. A snapshot is written whole and renamed into place, so one that does not read back
  entirely is refused, not repaired (`Journal.saved?`).
- *The order of a save* is: mark the journal, put the snapshot in place, replace the journal by
  one that starts at the mark. It is a pure function, `Journal.saveWrites`, over a model of the
  two files (`Lanes/Actors/Disk.lean`): a journal that is appended to, where the death of the
  process leaves any number of the first bytes of the append, and files that are replaced
  whole. What a start computes from the files is `Disk.load`: `open?`, `saved?`, `resume`.
  `Disk.Holds.save_crash`: if the process dies at any byte of the mark or between any two of
  the three writes, the files load as the kernel the shard had or, once the mark is wholly
  written, as the kernel the saved image restores, which is the one the shard goes on with.
  Never a refusal, never another kernel. `Disk.Holds.append_crash` says the same of a turn's
  append: the entries wholly written, and no others. `Disk.Holds` is what the files of a
  running shard are, and `Disk.Torn` what its death may make of them. A start mends the second
  into the first (`Disk.Torn.mend`) and a finished turn or save keeps the first, so the
  theorems hold over any number of starts, saves and deaths. The adapter runs the list of
  writes and decides nothing about them. A new journal's header and the cut of a write that
  did not finish are writes of the same kind (`Disk.mend`), so the adapter has two ways to
  write and no other: append and flush, or write beside and rename. What stays trusted is that
  the model is the operating system: a rename is atomic, bytes flushed survive the process, an
  append that did not finish leaves some of its first bytes. There is no `fsync` in Lean's
  `IO`, so loss of power is not covered. The model is also run on the compiled code at every
  cut. That test fails when the last two writes are swapped, which the states built by hand on
  real files cannot notice, since they are built in the right order.
- *Request ids after a cut.* The HTTP server used to find a fresh id by reading every input in
  the journal, which a cut journal no longer holds. Ids now start at the number of entries in
  the shard's history, which a cut does not lower, and go up by one per request the shard
  admits, in the order of admission. Every request that leaves a trace has an entry of its own,
  so the history at the next start is longer than the last such id. A request the shard refuses
  takes no id.
- *What an application gives.* Three codecs (`Kernel.Image.Codecs`): an identity, each actor's
  state, each actor's messages. `Codec.sigma` puts them together, and `Codec.struct%` and
  `Codec.sum%` write each in a line. `Http.gatedActors` adds the gate's own.

Not done: actors that are idle are still kept in memory, and upgrading the step functions
across a snapshot has no story yet beyond the `system` name that refuses the old files.

