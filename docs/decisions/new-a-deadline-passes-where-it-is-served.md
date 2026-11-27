# D?. A deadline may pass where a message is served

The ledger did not refine its timed spec (`systems/ledger/README.md`, friction log; D42's
limits). `user n` decides a view while its session is live, the session's timer fires at
`user n`, the administrator's payment is served at the ledger, and then the view is served
there and shows the payment: the spec orders view, session end, payment, and the view cannot
see it. A deadline passed at the actor that decides, and the request it bounds took effect at
the actor that serves. D42 named the cure: let the deadline pass where requests are served.

*What names a deadline.* `Deadlines σ T` maps a timer, by actor and message, to the deadline it
is. A system now names a second map of the same type, `delivered`, for messages an actor is
handed from the network: `Event.timed deadlines delivered` shows `.deliver e` and
`.duplicate e` as `fire t` when `delivered e.dst e.msg = some t`. A message handed over a second
time on a duplicating link is the actor handling it again, so it passes the deadline again,
which the spec refuses where the deadline is no longer armed: a notice of a deadline belongs on
a link that does not duplicate. The map reads the receiver and the message, not the sender, so
a message that passes a deadline names whose it is; the system's invariants say who sends it.

Two other shapes were weighed. A `Deadlines` that is a structure of two maps, or a map from
events, would change the type of every system's deadlines and of every statement that names
one. A deadline passing on an output (the ledger emitting a notice) would make the notice
visible to clients, which the spec does not have. A second map, defaulting to none everywhere
it is taken, changes no statement: every theorem that held for `deadlines` holds for
`deadlines` and `delivered`, and with `delivered` left out it is the theorem of before.

*Where it is taken.* `Event.timed`, `System.Refines`, `System.Implements` and
`Service.monitored` take `delivered` after `deadlines`, with the default none.
`Check.refines_sound`, `refines_traces`, `Service.monitored_respects` and
`Monitor.eq_after_of_run` take it implicitly, as they take `deadlines`; `Monitor.ok_iff` is about
observations and does not change.

*The monitor.* It must see the deliveries, so a `Driver` has a `deliver` hook, called on
`.deliver e` and `.duplicate e` (default: no change), beside `observe` and `timeout`;
`Driver.Respects` asks it to keep `==`, and `World.next` calls it. A delivery is therefore no
longer an internal event of `Scenario.Reachable`: it has its constructor, like a timer firing.
A monitored driver's `deliver` passes the deadline exactly as its `timeout` does.

*Proof rules.* `System.Refines.of_timed_events` is `of_events` with each delivery, duplicate and
timer answered by a step of the spec with that event's label: internal steps, or a deadline
passing between them. `of_events` is it with no deadlines. For the standard simulation,
`Account.Fires` says a step passes deadline `t`: some inputs take effect, `t` is then armed, and
it passes; `Account.implements_timed` is `implements` with each delivery and timer either a
`Moves` or, where the map names it, a `Fires`.

*The ledger.* A user's timers no longer pass deadlines. When `user n`'s session timer fires and
the session is live, the user ends it in its record and tells the ledger `ended n session`, on
the ordered link that carries its decisions; the ledger serving that message is the session's
end. A lock lifting is the same (`unlocked n`). The spec's record of a user is then, as in the
untimed proof, the user's record with the decisions still on the link undone, and a deadline
passes in it when the ledger reaches its notice: requests the user decided before it are
served before it, and requests decided after it, which saw the session ended, after it. The
user sends a notice only if the deadline is armed in its record, so the spec has it armed when
it passes.

Limits:

- *A notice lost is a deadline that never passes, though the user acted on it.* A session the
  user ended, whose notice a lossy link or a crash of the ledger lost, stays live in the spec:
  the spec serves what the user refuses. The timed refinement is proved for environments whose
  links from the users to the ledger are ordered, lose and duplicate nothing, and in which the
  ledger does not crash; users may crash, requests may be lost and reordered on the way in. In
  a deployment the ledger and its users are one shard, which a crash restarts from its journal
  whole, so a notice in flight is not lost; the semantics crashes one actor at a time.
- *How long a deadline lasts is still not checked* (D42).

Used: `systems/ledger`, whose timed refinement is model-checked and proved
(`Ledger.implements_timed`), and the old design kept as `Ending.atUser`, in which the checker
still finds the race.
