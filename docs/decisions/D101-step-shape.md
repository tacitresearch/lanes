# D101. The step's final shape: a context, quarantine, restarts and totality

Status: Partly superseded by new-volatile-actors.md (`now` and `seed` taken from the journal, and quarantine through the journal)

*A proposal for tacitresearch/lanes#99, items 8 and 9 of the design direction (#93). It moves no
code. Every fact below about the code was checked on `main`; the experiments were run on Lean
v4.37.0-rc1.*

A step sees its state and its message, and nothing else. It cannot read the time or draw a
random number, and it does not know who sent the message. The runtime's clock is not the wall
clock. A step that kills the process kills it again at every start. An actor driven by timers
never comes back once it stops. And a compiled panic carries on with a default value. This
proposal fixes the step's signature once, before there are users, and settles the failure path
around it.

## What there is today

- **The step.** `Actor.step : S → Msg → S × List Eff` (`Lanes/Core/Actor.lean`). The semantics
  knows each message's sender (`Envelope.src` in `Lanes/Core/System.lean`), but
  `SysState.handle` does not pass it on (`Lanes/Core/World.lean`).
- **The clock is the sum of the process's uptimes.** The shell starts the kernel's clock at the
  clock the journal last recorded and adds the monotonic time since the start
  (`Lanes/Runtime/IO/Shell.lean`, lines 200 to 202: `since := start.clock_ms`,
  `clock := since + (monoMsNow - epoch)`). A new journal starts at 0 (`Kernel.clock_ms`). D24
  says it: "Timers do not advance while the process is down." So the clock stands still while
  the process is down. Restore the 7-day-old volume snapshot that `docs/DEPLOY.md` keeps
  (`SnapshotRetainCount`, 7), and every deadline is a week late: sessions and lockouts that ended
  are live again.
- **No randomness and no sender.** Secrets and nonces are made in IO at the edge and come in as
  input. A reply-to travels in the message (`replyTo` in `examples/kv-cache/KV.lean`).
- **Time is stamped by hand.** Each web app writes the arrival time into a header in IO, before
  the journal, and reads it back in its bridge: `stamp` in `examples/videos/Videos/Web.lean`
  and `examples/reminders/Reminders/Web.lean`, and the shelf's `arrive` in
  `docs/TUTORIAL-WEB.md`. This is rough spot 3 of #78: the bridge has no clock. The scheduler
  knows only the times its schedulings carry and its own timers' deadlines (D79,
  `Schedule.now_le_step`), so a job may be late by the time the process was down.
- **A step that kills the process.** `Batch.run` works out a whole batch, purely, before the
  shell appends anything (`Lanes/Runtime/IO/Shell.lean`: the `Batch.run` call, then the loop over
  its acts). A poisoned input is therefore not journalled, and the client's retry kills the
  process again. A poisoned timer or message between actors is in the kernel's state, so it is due
  again after the restart, and the process dies at every start. The deploy restarts the app every
  2 seconds without limit (`Restart=always`, `RestartSec=2`, `StartLimitIntervalSec=0` in
  `infra/app/app-instance.sh`).
- **Stopped actors.** `EnvModel.restarts` exists, and the semantics uses it: `start i` is enabled
  when `i` has mail or `env.restarts i` (`SysState.step`, `.start`). The runtime never does.
  `Kernel.env` is `{}`, so `restarts` is false. The kernel starts an actor only in `Kernel.boot`,
  and in `Kernel.run1` when a message for it is at the head of the queue. Replay starts from
  `Kernel.boot` and replays the stop (`Journal.recover`), so a stopped actor stays down across
  process restarts too. No shipped actor emits `stop` today; only tests do (`Tests/Kernel.lean`,
  `Tests/Split.lean`). But quarantine needs a restart (below).
- **Totality.** Lint `trusted-listed` refuses `partial`, `unsafe`, `panic!`, `implemented_by`
  and `extern` outside the files `TRUSTED.md` names (`trustedWords` in `LanesCli/Lint.lean`). The
  `!` operators are not linted: `xs[i]!`, `.get!`, `.head!`, `.toNat!`, `.set!`. In `Lanes/` they
  appear five times, none in a step: `Lanes/Testing/S3.lean` and the macros of
  `Lanes/Data/Declare.lean` and `Lanes/Data/Codec.lean`. `examples/raft-kv/Harness.lean` has two
  `set!`.

## 1. A step context

### The shape

```lean
/-- What the environment gives at the moment of a step: the time and some entropy. -/
structure Moment where
  /-- Wall time, in milliseconds since the Unix epoch, as the journal recorded it. -/
  now_ms : Nat := 0
  /-- 64 bits nobody outside can predict, the same at every replay. -/
  seed : UInt64 := 0

/-- What a step is told besides its state and its message. -/
structure Ctx (Src : Type) extends Moment where
  src : Src

/-- Who sent the message a step handles. -/
inductive Sender (σ : Signature) where
  | outside
  | actor (i : σ.Id)
  /-- One of the receiver's own timers. -/
  | timer

structure Actor (S Msg Eff : Type) (Src : Type := Unit) where
  init : S
  step : Ctx Src → S → Msg → S × List Eff
  recover : Moment → S → S × List Eff := fun _ _ => (init, [])
  fresh : S → Bool := fun _ => false
  fresh_recover : ∀ m s, fresh s = true → recover m init = (s, []) := ...

abbrev Signature.Actor (σ : Signature) (i : σ.Id) (S : Type) : Type :=
  Lanes.Actor S (σ.Msg i) (Effect σ i) (Sender σ)
```

- **The field is `src`, not `from`.** `from` is a keyword in Lean: `structure C where from : Nat`
  does not parse (tried). `src` is the name `Envelope.src` already has (rule 1.7).
- **`recover` gets the time and a seed, not a sender.** A start has no message. With the time, a
  recover can re-arm a timer for what is left of a stored deadline, `after (deadline - now)`,
  instead of the whole delay again.
- **A library actor stays generic in `Src`**, as it is in `Eff`, and so needs no map to enter a
  system. A join maps the sender of each side: a message the wiring routes from the other side
  reaches a side as `.outside`, as it does in `Lanes/Proof/JoinSound.lean`'s projections. So a
  system's actors see the same `src` alone and in a join.

**`now`** is wall time. The shell starts the kernel's clock at each start at
`max (the journal's clock) (the wall clock)`, then adds monotonic time, as now. It records the
clock in the `advance` entry of each turn, as now, and every step of a turn sees that turn's
clock. A replay reads the same entries, so it sees the same times. The clock never goes back
(`Kernel.advance` takes the maximum). A wall clock set back while the process runs changes
nothing. A wall clock set back before a start loses to the journal's. Restoring an old snapshot
now moves the clock forward to today, so sessions that should have ended are over. After a long
stop, every timer that fell due meanwhile fires at once, taking turns with the messages
(`Kernel.timerTurn`). `Clock.Wall` in `Lanes/Outside/IO/Clock.lean` already reads the wall clock
this way, for the clock adapter.

Existing journals hold summed uptimes, so at their first start under this rule the clock jumps
to the wall clock, and every pending timer is overdue. There are no users yet. The fragment
says so.

**`seed`** is derived, not stored. The kernel counts the units of work it has done since boot
(a new field `Kernel.steps`, kept in its image). That count is the step's position: replay gives
the same count, and so do waves, because a parallel run is the sequential one value for value
(`Kernel.runWaves_eq`). When a journal is created, the runtime draws a secret of 128 bits
(`IO.getRandomBytes`) and writes it in the journal's header, which becomes the manifest under
#91. The seed is the first 64 bits of HMAC-SHA-256 under the secret of the position
(`Lanes/Lib/Crypto/Hmac.lean`, or `Native`). Nothing is written per entry. The secret is kept in
the journal and not with the deployment's keys, because a replay must give the same seeds: a
journal whose secret lived elsewhere could not be read without it.

A seed is for unpredictability: a token made with the application's key from a seed, jitter, a
sample. It is never for uniqueness. The semantics lets the environment give any seed, so nothing
proved can assume that two seeds differ. Uniqueness comes from a counter.

**`src`** is the envelope's sender for a delivery, and `.timer` for a timer. It lets a step
account per sender, refuse a sender, or tell a timer from a message. It does not let a step
reply to an actor it does not know the type of: `send to msg` still needs `msg : σ.Msg to`.

### Actors that need none of it stay as they are

`Actor.Plain S Msg Eff` is today's `Actor`, unchanged, with its `Reachable`, `Inductive`,
`Invariant` and `actor_invariant`. `Actor.Plain.toActor` ignores the context:

```lean
def Actor.Plain.toActor (p : Actor.Plain S Msg Eff) : Actor S Msg Eff Src where
  init := p.init
  step _ s m := p.step s m
  recover _ s := p.recover s
  fresh := p.fresh
  fresh_recover _ s h := p.fresh_recover s h

instance : Coe (Actor.Plain S Msg Eff) (Actor S Msg Eff Src) := ⟨Actor.Plain.toActor⟩
```

An actor that reads no context changes one word, its type, `Actor` to `Actor.Plain` (and
`σ.Actor i S` to `σ.Plain i S`). Its definition, its proofs and its use in a `System` stay as
they are, since the coercion is found where an actor is expected. `Plain.invariant_toActor`
carries an invariant of the plain actor to the actor, and `simp` sees through `toActor`
(`toActor_step`, `rfl`).

### How the semantics and the checker model `now` and `seed`

As inputs chosen by the environment, the way D42 weighed a clock the environment supplies:

```lean
structure SysState (sys : System σ) where
  ...
  clock : Moment := {}

inductive Event (σ : Signature) where
  ...
  /-- The environment moves the clock forward and draws a new seed. -/
  | tick (m : Moment)

-- in SysState.step
  | .tick m => if c.clock.now_ms ≤ m.now_ms then some { c with clock := m } else none
```

A step reads `c.clock` and its sender: `handle` takes the sender and builds the context. The
kernel reports a tick before each unit of work, with its clock and the unit's seed, so its
events are still a run (`Kernel.exec_reachable`). A tick is internal: refinements see no
`Visible` label for it.

The alternative, a moment in each event that runs a step (`deliver e m`, `timeout i msg m`),
was rejected. It changes the arity of four constructors used about 300 times, fairness would
have to speak of "a delivery at some moment", and "the time never goes back" could not be stated.

What proofs gain: along a run, `now` never decreases (a lemma), so a property can be stated
against it: "a session is used only before its expiry by the clock". What they do not gain:
timers still fire at any moment, whatever their delay (D42). That a timer fires no earlier than
its delay is a premise of the runtime (`TRUSTED.md`, as D79 has it). With `now` in the state, a
later decision can order timers by their deadlines against it without changing the step again.

The checker gets the moments the environment may choose: `Options.moments : List Moment`, empty
by default. With none, nothing ticks: the clock stays at `{}` and every step sees time 0 and seed
0, which is today's model. A scenario that cares lists times, and the checker ticks only forward
along them, so the space stays finite. `Fuzz` picks ticks from the same list. A system that
relied on two seeds differing would be found out by the default, which is the point.

### What changes in the proofs, and the migration

Every step's signature changes, so every generic statement about steps changes. The counts
(grep, rough):

| What | Where | How many |
|---|---|---|
| `actor` fields of systems | `Lanes/`, `examples/`, `integrations/`, `Tests/` | 21, 19, 3, 46 |
| Definitions typed as an actor | the same | 9, 13, 0, 14 |
| An actor's `.step` used in a definition or a proof | `Lanes/`, in 28 files | 123 |
| An actor's `.recover` used | all | 92 |
| A match arm `\| .crash` (each gains a `\| .tick`) | `Lanes/`, `examples/`, `Tests/` | 71, 2, 3 |
| `SysState.ext'` | `Lanes/`, `examples/`, `Tests/` | 90, 11, 4 |

So nearly all the work is in `Lanes/`, in the proof toolkit, the runtime's soundness and the
behaviours. Applications' proofs go through the toolkit's lemmas and are barely touched. The
plan, each step mechanical:

1. In `Lanes/Core/`: `Moment`, `Ctx`, `Sender`, the new `Actor`, `Actor.Plain` with its
   coercion and lemmas, `SysState.clock` with its default, `Event.tick`, and `handle` with the
   sender. `actor_invariant` takes both kinds: for an `Actor` it introduces the context with
   the state and the message.
2. `SysState.ext'` gets its clock premise as an automatic argument,
   `(hclock : a.clock = b.clock := by simp)`, so its 105 uses mostly stay as they are.
3. Every case analysis on an event gains `| .tick m`. A tick changes only `clock`, so in every
   statement that does not mention the clock it is closed by one lemma (`SysState.step_tick`)
   and `simp`. Proofs that close all cases with `<;>` need nothing.
4. Generic proofs pass the context on: `(sys.actor i).step s m` becomes
   `(sys.actor i).step (c.ctx src) s m`. This is the part that takes reading.
5. Applications: every actor becomes an `Actor.Plain`, until it wants the context.

This is one large pull request, because the semantics cannot have two step types at once. My
estimate is a few days of an agent's work, nearly all of it steps 3 and 4, and no change to any
theorem's statement but those about steps themselves.

### What the scheduler and the bridge get

- **The bridge.** `Gate.step` passes its step's `now_ms` to `Bridge.decode`. The arrival time is
  then the time the journal recorded for the turn, the same at every replay, with no header.
  `stamp`, the header, its filter in `prepare` and the test that a client's header is not
  believed (`examples/videos/Videos/EndToEnd.lean`, "the time a request arrived is the
  server's") go away, in videos, reminders and the tutorial. Rough spot 3 is closed.
- **The scheduler.** `Lanes.Schedule` reads `now` at every step. The time it knows no longer
  lags behind after a quiet spell, `schedule` no longer needs to carry `now_ms`, and with the
  wall clock a job is no longer late by the time the process was down (D79's limit).
- **Videos' transcode deadline.** D91 left a round without a deadline: "The scheduler's outcomes
  carry no time, so the site cannot set one from the moment a check succeeds." With the
  context, the site's step that takes the check's success records
  `deadline := now + transcode_ms` and arms a timer. When the timer fires, the step fails the
  round if `now ≥ deadline`, and arms the timer again if it fired early. This is provable in the
  model: a round is failed only once the clock has passed its deadline. It also gives
  `Videos.report_settles` a companion that needs no report: every round ends by its deadline.
  That matters once a report can be quarantined (below).

## 2. Quarantine

### The mechanism

What kills the process inside a step: a panic, once panics abort (section 4); a stack overflow;
the kernel's out-of-memory killer. Each start then dies at the same unit of work, because the
kernel is deterministic and the journal brings it back to the same state.

1. **Every start appends a `start` entry**, made durable: one sync per process start.
2. **A turn's inputs are written before its work is worked out**, flushed to the operating system
   but not synced; the rest of its entries are appended and synced after, as now. So a poisoned
   input is in the file after the death, and the next start brings it back as it brings back a
   poisoned timer. The entries after the last `batch` entry are the *frontier*: nothing they
   caused has been handed over. A file cut anywhere is a journal (`Journal.open?_cut`), and one
   that ends in a turn's inputs describes the kernel that accepted them, which is a state of the
   run.
3. **A start after a start that made no progress runs carefully.** "No progress" means there is
   no `batch` entry after the previous `start`: only inputs and notes. A careful start does
   one unit of work per turn. Before each unit it writes a note `attempt u` naming the unit: an
   input accepted, the message at the head of the queue, a timer, or an actor's start. The kernel
   says which unit comes next, purely (a new `Kernel.next?`). The note is flushed to the
   operating system but not synced: a death of the process keeps it, and a loss of power may lose
   it, which only puts the quarantine off.
4. **Two starts in a row whose last note names the same unit at the same position quarantine
   it.** The runtime appends `quarantined u`, durably, applies it (below), reports it, and goes
   back to full batches once past.
5. **A planned stop writes a note `stopped`**, which resets the count. A drain on `SIGTERM`
   (#53) during a careful start never counts as a death.
6. **The front refuses an arrival equal to a quarantined input**, compared by its decoded value
   without its request id (#91 journals `(ReqId, σ.In)`), as it refuses when the gate is full. A
   client that retries a request of death then gets a refusal, not another death. A re-drive
   lifts the refusal.

In normal running the cost is the `start` entry per process start and one more flush per turn.
A careful start is needed only after a start that died before it wrote a `batch`. With the
deploy's restart every 2 seconds, a poisoned unit is usually quarantined after four deaths (the
death in the first life, a start that replays to it and dies in its first turn, two careful
starts): about 8 seconds plus the replays.

`Kernel.run1` changes so that starting a receiver that is down and delivering to it are one unit,
with a note before each half. Then quarantining an input also undoes the start it caused, and
the note says whether `recover` or `step` died.

**Only the frontier is quarantined.** A careful start replays the past as now and works through
the frontier one unit at a time. An entry before the frontier may have had its outputs handed
over, so skipping it would contradict what the outside saw. A replay of the past can still die
where the live run did not: stack depth is not part of the semantics, and replay runs on another
thread than the live step, or than a wave's pool thread. Then the start refuses and reports, and
an operator decides.

### What a quarantine is in the semantics

- **An input.** The kernel removes its envelope from the queue. Its own `input` entry stays where
  it is, so positions and output ids do not move. The run is the run without that input, which
  is a run under every environment, as the runtime contract says (draft #86, "A quarantined input
  counts as one that never arrived"). Two things make that exact. The input never stepped, so it
  caused no output, and it was never acknowledged (the contract's clause 3). And with the change
  to `Kernel.run1` above, it caused no start either: without it, the start it caused would be
  left in a run that no longer has the mail that enabled it. A request quarantined is answered
  at the front, as a refusal is.
- **An actor's start** (its `recover` dies). The actor is held down and its mail waits. No event
  is needed: the run does not take `start i`. Fairness is broken for that actor, which the
  restart policy below counts.
- **A message between actors, or a timer.** This is the case the contract leaves open. Skipping
  only that message would lose a message, which the semantics allows only on a lossy link. A
  timer has no event that removes it at all. I propose that it is a **crash of the receiver**,
  `Event.crash i`: `SysState.down` loses its mailbox and its timers, the poisoned unit with
  them. The restart policy then starts it through `recover`, which re-arms its timers. Why a
  crash: the semantics and the checker already have it, rule 3.3 already says any actor may
  crash at any step, and a poisoned state is cleared at once, through `recover`, not one message
  and two deaths at a time. The cost: the receiver's other mail is lost with it. One actor per
  entity, which the runtime contract already advises, keeps that small.

Behind today's gate a request reaches the application as a message from the gate's actor (the
wiring of `Http.fronted`, `Lanes/Web/Http/Front.lean`), so a request of death is the crash case:
the application's actor crashes, and the gate, which did not, answers the requests it had
forwarded with `504` at their deadlines. With the gate off the hot path (#86) it is an input, and
the first case.

An application whose proofs need an actor never to crash more than it needs the site up can
turn quarantine off for that actor. A poisoned unit there keeps the process down, reported,
until a fix is deployed. The ledger is the example: `Ledger.implements_timed`, a refinement, is
proved with `env.mayCrash .ledger = false`.

### What it does to applications' liveness theorems

**A quarantined input.** The run is a run under the same environment, and it stays fair: no
event that the input's absence enables is left untaken, and the queue behind it moves on. So
every theorem still holds of the deployed run, and it says nothing about that input. Examples:

- `Http.served_pending_answered`: every request the gate admits is answered. A quarantined
  request was never admitted. It is answered at the front.
- `Videos.report_settles`: a report the worker signed, *arriving at position `m`*, is followed by
  a position where its round is no longer transcoding. A quarantined report never arrived, so its
  round may stay transcoding. It ends when the worker reports again, which the worker's model
  allows (`Lanes/Outside/Transcode.lean`: late, again or never), or at the round's deadline from
  section 1.
- What the input would have started never starts: a job it would have scheduled is never held,
  so `Videos.job_ends` has nothing to say about it.

So a theorem that promises something *after an input arrives* keeps its statement and loses that
one input. A client who must be served has to try again after a fix and a re-drive. Recovery
belongs to the endpoints anyway (rule 1.5).

**A quarantined message or timer at actor `i`.** The run now contains `crash i`. Every theorem
that assumes `i` does not crash (the contract's set `Up i`) is no longer about the deployment
from that point on: `Videos.job_ends`, `Reminders.delivery_ends` and
`Reminders.delivery_answered` (the scheduler must not crash), `Videos.report_settles` (the site
must not crash), the theorems of `Lanes/Semantics/Schedule.lean`, and `Ledger.implements_timed`,
which is a safety theorem. The default runtime then provides `Up i` only until its first
quarantine at `i`, and the report says so: "the assumption `Up i` was broken at position n".
What holds under every environment still holds: each actor's invariants, lifted by
`System.invariant_of_actor`, and every theorem proved with `mayCrash` allowed.

### Reports and re-drive

- **Told.** A line at error level at the start that quarantines, a counter on the metrics page,
  and `lanes journal quarantined <journal>`: each quarantine's position, time, actor, kind
  (input, message, timer, start), the message decoded with the journal's schema (#91's dump),
  and how many starts it killed. The panic's text is on standard error and in the system's log,
  not in the journal.
- **Re-drive.** `lanes journal redrive <journal> <position>` appends the quarantined input again,
  as a new arrival at the end of the journal, with new output ids, as the contract says. It runs
  with the app stopped (it takes the journal's lock), which a deploy of the fix does anyway.
  Only inputs can be driven again. A message or a timer went with its actor's crash, and its
  actor's `recover` has re-armed what it needs. Putting a message between actors back on the
  queue would be a message nobody sent: no event of the semantics.
- **Across an upgrade.** The list of quarantines is carried into the new version's journal by the
  migration, so `lanes journal quarantined` still shows them.

## 3. A restart policy for stopped actors

Checked above: the runtime ignores `EnvModel.restarts`. An actor that stops starts again only on
a message; one driven only by timers, such as the scheduler (`Lanes/Behaviours/Schedule/Basic.lean`
boots it) or the keeper of `examples/watchdog`, which pings on a timer of its own, stays down
for good, across process restarts too. Quarantine as a crash makes this matter.

- `System.restarts : σ.Id → Bool`, which by default holds for the actors of `boot`: what the
  system starts without mail, it starts again without mail.
- After a stop or a crash, the kernel starts such an actor again after a backoff, capped and
  exponential, by an entry in its agenda next to the timers. The start is a `start i` event,
  enabled because `env.restarts i` (`SysState.step`). `Kernel.env` becomes
  `{ restarts := sys.restarts }`, and `Kernel.exec_reachable` gains that case.
- Bounded (rule 2.6): after `maxRestarts` within `window_ms`, the actor is held down and reported
  as a quarantine is. That is OTP's restart intensity, without a supervisor to escalate to.
- A proof under an environment with `restarts := false` that relies on "a down actor starts only
  with mail" does not cover these starts. Each per-actor invariant covers `recover` already, so
  this is about system-level proofs only, which I have not found.

Two small fixes go with it: `Actor.recover`'s docstring says that by default "all state is
volatile", which the journal made untrue, since under it all state survives a process restart;
and adapters restart with a backoff of their own (#93, item 9), which is a separate change.

## 4. Totality

### The lint

- **The `!` operators.** A new lint, `bang`: `]!` and every word ending in `!`, except `s!`,
  `m!` and `f!`, which build strings. Exempt as `trusted-listed` is, plus `Tests/`,
  `Lanes/Testing/` and `LanesCli/`. Today it finds the four in the two macro files, which become
  `[k]?` with an error, and the two `set!` in `examples/raft-kv/Harness.lean`. `assert!` is found
  too: rule 4 allows it at an adapter, which is a trusted file.
- **`partial`** is refused already outside trusted files. Since steps are never in those files,
  no step is `partial` today.
- **The precise check comes later.** A step can call a function of another package that panics.
  The exact check is on the environment: from each actor's `step` and `recover`, no reachable
  constant is `panicCore`, `partial`, `unsafe` or `implemented_by`. It belongs with a check of
  the built environment such as the one #102 asks for, which reads constants the same way.

### What a compiled `panic!` does: the experiment

A program of its own, built with Lake on Lean v4.37.0-rc1 on x86-64 Linux. A step-like function
over a structure (`count := 7` by default, as its derived `Inhabited` gives) indexes an array out
of range; another calls `panic!`; then `Option.get!` on `none`, `String.toNat!` on `"x"` and
`List.head!` on `[]`.

| Run | What happened | Exit status |
|---|---|---|
| no setting | Each panic prints `PANIC at <declaration> <module>:<line>:<col>: <message>` (`Error: index out of bounds` for `xs[i]!`) and a backtrace on standard error, returns `default`, and the program goes on. The state after `panic!` was the type's default: `count` went from 27 back to 7. `get!`, `toNat!`, `head!` gave 0. | 0 |
| `LEAN_ABORT_ON_PANIC=1` | The first panic prints, then aborts (`SIGABRT`) | 134 |
| `LEAN_ABORT_ON_PANIC=0`, `=no`, or empty | The same abort: the variable counts if it is set at all, whatever its value | 134 |
| `setenv` of the variable from inside the program, before the panic | Aborts: it is read when the panic happens, not at start | 134 |
| `lean_set_exit_on_panic(true)` (`lean.h`, no Lean binding in `Init`) | Prints, then exits | 1 |
| `lean_set_panic_messages(false)` | Nothing printed; carries on with `default` | 0 |
| a panic on a dedicated task's thread, with the variable set | The whole process aborts | 134 |

In the logic a panic *is* `default`: `panicCore` is `fun msg => default`, and both
`(panic! "x" : Nat) = default` (`rfl`) and `#[1, 2, 3][10]! = 0` (`decide`) are theorems. So
carrying on runs exactly the function the proofs are about, and every theorem about the step
still holds of what runs. That is not a reason to carry on. The proofs cover what the author
wrote, not what was meant: `default` for a state is usually `init`, and the experiment lost the
state's work silently. And a panic in trusted IO code (the shell, the server, an adapter's
handler) is covered by no theorem at all.

**Recommendation: abort.** A panic should kill the process, the journal keeps what was durable,
and quarantine deals with a panic that comes back. The runtime sets `LEAN_ABORT_ON_PANIC=1`
itself at its start, through a one-line binding in `native/lanes.c`, before it starts its
threads: the variable is read when the panic happens, so setting it then works. The deploy's
unit (`infra/app/app-instance.sh`, its `Environment=` line), CI and the test runners set it too,
so that a process that panics before the runtime starts aborts as well. A check or a test that
passes by carrying on with `default` is not a pass. `lean_set_exit_on_panic` is not used: its
status 1 cannot be told from other failures, and
`exit` runs exit handlers while the other threads still run. The docs must not say "set it to 0
to turn it off": that turns it on.

### A stack overflow

Also tried: a non-tail recursion of one line, `deep (n + 1) = deep n + 1`. At 3·10⁷ levels it
returned on the main thread; at 10⁸ it printed `Stack overflow detected. Aborting.` and aborted
(status 134), on the main thread and on a dedicated task's thread alike. It cannot be caught. So
an overflow is a death like an aborted panic, and quarantine handles it the same way: the note
before the unit names it, and two deaths there quarantine it. A step that overflows on one
thread may not on another, which is why a death during replay is refused and not quarantined.
Total is not bounded: rule 4 asks for structural recursion, and a step over a large list should
fold or recurse in tail position.

A step that runs for an hour is no death, and quarantine never sees it. A watchdog that kills
the process when a unit takes longer than a budget would turn it into one. That is for later.

## 5. Perspectives

- **Erlang and OTP** (Armstrong's thesis, *Making reliable distributed systems in the presence of
  software errors*, 2003). Processes share nothing, a process that meets an error it does not
  handle crashes, and a supervisor restarts it by a strategy (one for one, one for all, rest for
  one), within a restart intensity beyond which the supervisor itself gives up. A restart helps
  there because the restarted process starts from a clean initial state and has lost the state
  that met the error, and because many errors depend on timing or on the outside. A Lanes step is
  deterministic and its state is durable: a restart replays the same journal to the same state,
  and the same next unit, so the same error happens again. A restart helps only if something
  changes: the input (quarantine), the state (`recover`, after a crash) or the code (a deploy).
  So this proposal quarantines, and restarts through `recover`, and does not just restart.
- **Crash-only software** (Candea and Fox, HotOS 2003). The only way to stop is to crash and the
  only way to start is to recover, so the recovery path is the one that is exercised. Lanes is
  built this way already (rule 3.3, D5). Quarantine adds a decision to the recovery path, not a
  second path. Their later microreboot (Candea and others, OSDI 2004) restarts the smallest
  component that failed. A crash of one actor, instead of a stopped site, is that.
- **Fail-fast** (Gray, *Why do computers stop and what can be done about it?*, Tandem, 1985). A
  module either works or stops at once. Gray found that most faults seen in production went away
  on a retry (Heisenbugs), which is why his process pairs worked. Aborting on a panic is
  fail-fast; carrying on with `default` is its opposite. In Lanes every fault of a step is the
  other kind, a Bohrbug, by construction: hence quarantine, not retry. Heisenbugs remain on the IO
  side, where adapters retry with a backoff.
- **TigerStyle** (TigerBeetle's style guide). It separates operating errors, which are expected
  and handled, from programmer errors, which an assertion catches and on which the program
  crashes, so that a correctness bug becomes an availability bug. And it puts a limit on
  everything. Lanes maps it: the outside's failures are inputs a step handles; a step's own bug
  aborts and is quarantined; restarts, quarantines and their windows are bounded.

**Supervision trees stay a later library.** In Lanes a supervisor would be an actor that learns
when another stops and decides what to do. That needs an effect to watch another actor, which
the model does not have: no actor can learn that another stopped. The flat policy of section 3,
one actor and an intensity, is what OTP's one-for-one gives, and it is enough until an
application needs more.

## 6. Costs

- **The one large change**: the step's type, through the proof toolkit and the runtime's
  soundness. A few days, mechanical, but large to review.
- **The journal's format** gains `start`, `attempt`, `stopped` and `quarantined`, and the
  secret. It should land with #91's format change, so that there is one change before the first
  tag.
- **At run time**: one sync per process start; one more flush per turn, for the inputs written
  before their work; an HMAC per step for the seed, to be measured against `Tests/Scale.lean`;
  a flush per unit, and units one at a time, during careful starts only.
- **The checker's state** gains the clock. With no moments listed (the default) it never
  changes, and the counts do not grow.
- **Behaviour**: overdue timers fire at once after a long stop; a panic aborts where it used to
  carry on; a quarantine of a message or a timer loses the rest of its actor's mail.
- **Trusted code**: the shell's careful start, its notes, and the abort setting. The kernel's
  side (the unit, its removal, the restarts) is pure and proved with the kernel.

## The order of work

Each a small pull request, the first three independent of the rest:

1. **Totality**: lint `bang`; the macro uses rewritten; abort on panic in the runtime, CI, the
   test runners and the deploy's unit; `recover`'s docstring.
2. **The wall clock**: the kernel's clock starts at `max (journal) (wall)` (the shell only). It
   fixes the restored-backup bug by itself, before the context exists.
3. **Restarts**: `System.restarts`, restart entries in the agenda, backoff and intensity,
   `Kernel.exec_reachable` extended.
4. **The context in the semantics**: `Moment`, `Ctx`, `Sender`, `Actor.Plain`, `Event.tick`,
   `SysState.clock`, the toolkit's proofs, every application's actors made plain. The large one.
5. **The context in the runtime**: `Kernel.steps`, the seeds, the journal's secret (with #91),
   the ticks the kernel reports; the checker's `moments`.
6. **Time where it is needed**: the bridge reads `now`, and the stamps go; the scheduler reads
   `now`; videos' transcode deadline.
7. **Quarantine**: the entries, a turn's inputs written first, the careful start, `Kernel.next?`
   and the one-unit start and delivery, the kernel's operation and its proof, the front's
   refusal of a quarantined input, `lanes journal quarantined` and `redrive`.
   The contract (#86) states it with the named sets.

## Details settled

Each detail below is settled at the default it states (the owner's rule: small and reversible choices are taken at their default, and changed later if needed).

Each has the default I would take.

1. **A quarantined message between actors, or a timer**: a crash of its receiver, then a restart
   through `recover`? *Default: yes.* The alternatives are a new event that drops only that unit
   under a new assumption, or no quarantine for them and the process kept down.
2. **Quarantine per actor**: on for every actor, with a way to turn it off for one whose proofs
   need it never to crash? *Default: on, with the switch.*
3. **The seed**: 64 bits, HMAC-SHA-256 of the position under a 128-bit secret kept in the
   journal? *Default: yes.* And a `lanes journal reseed` for a copy of a journal (a staging
   restore), so it does not draw production's seeds? *Default: yes.*
4. **`now`**: the wall clock taken at each start, monotonic time within a run? *Default: yes*, not
   the wall clock at every reading, which would stall timers when it is set back.
5. **A forward jump at a start** (a wall clock set to the wrong year): accept it and log it?
   *Default: accept and log*; a bound would refuse to start for a reason an operator cannot fix
   quickly.
6. **Names**: `src` and `Sender`, `Moment`, `Ctx`, `Actor.Plain`? *Default: these.*
7. **On a panic**: abort, set by the runtime itself? *Default: abort.*
8. **The restart policy's default**: the actors of `boot`, a backoff from 100 ms to 60 s, held
   down after 5 restarts in 10 minutes? *Default: these.*
9. **Re-drive**: inputs only, with the app stopped? *Default: yes.* An administrative input to a
   running app can come later.
10. **The checker's clock**: no ticks unless a scenario lists moments? *Default: yes.*
11. **A turn's inputs written before its work**, at one more flush per turn, so that a request of
    death comes back at the next start and is quarantined? *Default: yes.* Without it, a client
    that retries kills every start that has made progress, and quarantine never sees it twice in
    a row.
