# D56. A deadline may pass where a message is served

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
it is taken, changes no statement but by that argument: the monitor's and the refinement
rules' theorems hold for every `deadlines` and `delivered`, and with `delivered` left out each
is the theorem of before.

*Where it is taken.* `Event.timed`, `System.Refines`, `System.Implements` and
`Service.monitored` take `delivered` after `deadlines`, with the default none.
`Check.refines_sound`, `refines_traces`, `Service.monitored_respects` and
`Monitor.eq_after_of_run` take it implicitly, as they take `deadlines`; `Monitor.ok_iff` is about
observations and does not change.

*The monitor.* It must see the deliveries, so a `Driver` has a `deliver` hook, called on
`.deliver e` and `.duplicate e` (default: no change), beside `observe` and `timeout`;
`Driver.Respects` asks it to keep `==`, and `World.next` calls it. A delivery is therefore no
longer an internal event of `Scenario.Reachable`: it has its constructor, like a timer firing.
A monitored driver's `deliver` passes the deadline exactly as its `timeout` does. The hook
takes the receiver and the message, as `timeout` takes the actor and its timer, not the
envelope: a statement about a monitored driver whose maps are left to unification then
unifies them, as it did `deadlines`, because each is applied to bound variables in the
driver's fields.

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
- *The kernel's theorem of what can be seen is stated for timers.* `Kernel.exec_visible` and
  `Released.visible` take `deadlines` only, so they say nothing yet of a deadline a delivery
  passes; their proofs read only that a start is not visible, and carry over.

Used: `systems/ledger`. A view racing the end of its session passes (22,109 states, and 95,966
with a user crashing), and the abuse scenario with timers firing at any moment (108,105 states,
527,757 with a user crashing); the old design, kept as `Ending.atUser`, still fails in 43 steps,
and a notice lost fails in 16 steps on a lossy link and in 17 with the ledger crashing. The
timed refinement is proved (`Ledger.implements_timed`). A lease in `Tests/Lease.lean` that is
freed as the server handles its timer's notice refines its spec with that delivery named, and
does not with the timer named instead.
