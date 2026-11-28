# D123. A step's effects in linear time, and a bound on the mail between actors

Status: Accepted

Issue #228 (its two lines on the runtime, first filed as #159 and #162), on
`docs/decisions/D116-free-running.md` and `docs/decisions/D121-step-context.md`.

## A step's effects

The scheduler's write-back (`Sched.Slot.put`) and the kernel's (`Kernel.performAll`) gathered a
step's sends, outputs and timers by appending each to the list so far, so a step with `n` of them
took time quadratic in `n`. They now put each at the front and turn the lists round once at the
end. Each is proved equal to the fold that appends (`Sched.Slot.put_eq`, `Kernel.performAll_eq`),
which the soundness proofs were already about, so every theorem is unchanged. The commit keeps
its lists (`Sched.Commit`), so the shell is unchanged.

The time for one step with `n` outputs and `n` sends, the best of three, on the shared four-core
container under a load of about 6 (`Tests/Scale.lean`, printed by `lake exe lanesCheck`):

| `n` | `Slot.put` before | after | the kernel before | after | the runtime, until all are handled, before | after |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1,000 | 3–12 ms | 0.04 ms | 3 ms | 0.14 ms | 7 ms | 1.8 ms |
| 10,000 | 453 ms | 0.5 ms | 559 ms | 1.6 ms | 490 ms | 20 ms |
| 100,000 | 73 s | 7 ms | 133 s | 23 ms | 72 s | 282 ms |

The check in `lake exe lanesCheck` fails if ten times the effects take more than 25 times as long
(plus 50 ms): linear is ten, quadratic a hundred.

Not changed: arming a timer looks through the actor's pending timers for one with the same
message (`Sched.arm`, `Kernel.perform`), so a step that arms `n` different timers is quadratic in
`n`. A map keyed by the message would need `Hashable` or `Ord` on every actor's messages, which
`Signature` does not ask and every system would then have to give. An actor rarely has many timers
pending; this stays a limit of the design.

## The mail between actors

The inbox is bounded (rule 3.8, `Sched.Ledger`): at most `inboxCapacity` inputs wait for their
actor. Nothing bounded the messages between actors. One input can cause any number of them, and
actors that send each other more than they take need no input at all. Rule 2.6 asks for a maximum
and for what happens at it.

What the bound may do is fixed by two things. The links of a running system are reliable: every
message is delivered, once, and in order on its link (`Sched.Reliable`), and every application's
proofs assume it. And a step is pure and has already returned when its messages are pushed: it
cannot be made to wait.

1. **Drop a message past a bound.** Only a lossy link may lose a message (`Link.lossy`). The
   runtime would leave the semantics, and every theorem about delivery with it. Rejected.
2. **Make the sender wait** for room in the receiver's mailbox. The sender is the worker pushing
   the step's messages. Two actors whose mailboxes are full and that send each other wait on each
   other forever, each holding its worker; enough such pairs stop every worker. Nothing in the
   semantics stands for this, and nothing could prove it does not happen. Rejected.
3. **Crash the receiver** past a bound (`Event.crash`). The scheduler's model has no crash of an
   actor that another worker may be stepping, and adding one is the work D121 put off (its
   option 2). It would also hold only for applications whose environment lets that actor crash
   (`EnvModel.mayCrash`), which few allow. Not now.
4. **Refuse inputs while the mail is high** (chosen). While `Runtime.Config.mailHighWater`
   (65,536) messages between actors wait, `tryInput` refuses and `input` waits
   (`Sched.Ledger.offer`). An input not taken is no event: the semantics allows it at any moment,
   so neither the model nor any application's proofs change. It is rule 3.8 carried from the
   inputs to what they cause, and the server already answers a refused request with `503`. It
   bounds the mail inputs cause, to the mark and what the inputs already taken send. It does not
   bound actors that send each other more than they take.
5. **Restart past a capacity** (chosen, for what 4 cannot bound). A step whose sends leave more
   than `Runtime.Config.mailCapacity` (1,048,576) messages waiting is handed to
   `Runtime.Config.onOverflow`, which by default reports it and ends the process with status 75,
   as the watchdog does (D121). This is the semantics' restart (`Event.restart`,
   `Sched.Step.restart`), which an environment allows with `EnvModel.mayRestart`: all the mail
   goes with the rest of memory, as the semantics' restart takes it, and no message is lost alone.

The mail is counted from what the ledger already kept to know when the system is idle: the items
in mailboxes less the inputs (`Sched.Ledger.mail`), which counts timers gone off as well. So the
mark costs one comparison when an input is offered, and the capacity one when a step that sends
updates the ledger, which it already did. Senders that waited are woken when the mail falls below
the mark (`Sched.Ledger.done`).

The bound is on all the mail together, not on each mailbox. Memory is what it protects, and memory
is shared. A bound per mailbox would cost a count at every push and a mark per actor, and still
not bound the total. The price: an actor far behind holds up every input, not only those to it.

Weighed by rule 1.8: every application gets memory bounded for its mail, and back-pressure from
its own load as well as from its inbox, with no change to its code; the cost is three fields of
`Runtime.Config`, two functions and a few theorems of the ledger, and one more thing trusted, that
the process ends. A program that never nears the mark sees no difference.

## What is proved and trusted

Proved (`Lanes/Runtime/SchedSound.lean`): the ledger takes an input only while fewer than the
inbox's capacity wait, the mail is below the mark and it is open, and taking it leaves the mail as
it was (`Sched.Ledger.offer_taken`); an input refused leaves no trace (`offer_refused`); none is
taken at the mark (`offer_of_mail`); a step's sends are reported exactly when they pass the
capacity (`sent_over`); and the waiting senders are woken when the mail falls below the mark
(`done_wakes`). The model is unchanged.

Trusted (`TRUSTED.md`, the shell's row): that the shell asks the ledger as written, and that the
process ends, as for the watchdog.

Tested (`Tests/Runtime.lean`): a hub fans an input out to a sink whose first output the handler
holds, so its mail cannot drain; at the mark an inbox with room refuses, `input` waits and is taken
once the sink drains, every message arrives and the trace replays through the semantics. A step
past the capacity is reported once with the mail it left, and a handler that returns lets the
runtime go on. Actors that each send two messages for one are reported, and take no input.

## What remains

- Inputs taken in a turn count as mail until the turn ends, since the ledger is given a turn's
  counts at once (D116). The mark is off by at most a budget's inputs per worker.
- An application whose proofs assume no restarts (`EnvModel.mayRestart = false`) has no guarantee
  past the capacity. It may raise the capacity, or give an `onOverflow` that only reports.
- A crash of the receiver instead of the process (option 3), if restarts prove too costly.
