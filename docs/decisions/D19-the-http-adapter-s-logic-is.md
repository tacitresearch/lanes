# D19. The HTTP adapter's logic is a gate actor

Status: Partly superseded by D31 and D43 (the gate is a system joined in front, not `gated`)

`Lanes/Web/Http/Gate.lean` defines `gate`, an actor that parses each request into an input, keeps
the list of waiting requests, and answers each one: with the system's response, with `504` when
its timer fires, or with `503` beyond `maxPending`. `gated sys` is `sys` with the gate in
front; the inner actors' outputs become messages to the gate. `Lanes/Web/IO/Server.lean` serves
`gated sys` and only moves bytes.

Why: the first adapter kept the waiting table in a mutex and the deadline in a per-request
`select`. A review found two defects there. As an actor the logic is checked and proved
together with the application. `Tests/Gate.lean` explores every race between a response and its
deadline on two requests and shows each is answered exactly once. `gate_bounded` proves the
table's bound. `Lanes/Http/GateSound.lean` (removed) proves the safety half for every system, bridge and
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
