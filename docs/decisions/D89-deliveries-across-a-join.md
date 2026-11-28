# D89. What one side of a join sends the other is handled there, in every fair run

Status: Accepted

`Lanes/Semantics/FairJoin.lean` (section `Across the wiring`), `Lanes/Semantics/Liveness.lean`
(`System.Run.Fair.handled`), `Lanes/Core/Run.lean` (section `Kept`), `Lanes/Semantics/Schedule.lean`
(`Schedule.attach_end_handled`). D87 could not prove that a deleted video's object is deleted or
the deletion reported, because nothing carried `Schedule.held_ends` across `Schedule.attach`:
the scheduler hands its end over, and in the join that end is a message to the site, which no
theorem delivered. This is that step.

## The statements

- `System.Run.Fair.handled`, of every system: in a fair run, a message in flight is delivered or
  handled as a duplicate at a later position, when its link loses nothing, the environment does
  not crash its receiver and the receiver never stops, in a step or in a start.
- `System.Run.Fair.routed_right`: in a fair run of `a.join b w`, if at position `n` an actor `i`
  of `a` handles a message (`ev.leftDeed = some (.handle i msg)`), its step emits `out` and
  `w.toRight out = some x`, then at a later position the actor `(b.accept x).1` is delivered
  `⟨some (.inl i), .inr (b.accept x).1, (b.accept x).2⟩`, or handles it as a duplicate. The
  premises are those of `handled`, of that link and that actor. `routed_left` is the same from
  `b` to `a`. `handled_right` and `handled_left` start from the message in flight.
- `Schedule.attach_end_handled`: in a fair run of `attach sys config use` in which the scheduler
  is not crashed, a job held while the scheduler is up that is not periodic has its end, the
  input `use.answer key o` or `use.notice key p t`, delivered to the actor of `sys` that takes
  it, at a later position. The links from the scheduler to `sys` lose nothing, and no actor of
  `sys` is crashed or stops.

## Fairness

`System.Run.Fair` is weak fairness, for each obligation on its own: an obligation that is due at
every position from some point on, and that no step starts again, is taken. The delivery of one
envelope is one obligation, due while its receiver is up and it is deliverable. Weak fairness is
enough. On a link that loses nothing, a message to an actor that stays up stays in flight, and
the oldest message on its link stays deliverable until it is delivered; each delivery ahead of
it brings it nearer (`System.Run.Fair.delivered`). Strong fairness is not needed, nor fairness per
actor, which would let one message wait forever while others go.

A receiver that is down needs no premise of its own. It has mail, so starting it is an
obligation, due until it is taken; nothing else brings it up, and nothing else takes the
message out (`SysState.mem_net_of_step`). Once started it stays up. `env.restarts` is not used.

## The premises, and what each excludes

- *The link loses nothing.* Dropping a message is the environment's event, and no fairness is
  assumed of the environment. On `Link.network`, the link `EnvModel.distributed` gives between
  actors, the end may be lost; a requester that must see it asks again, as rule 1.5 says.
- *The environment does not crash the receiver.* A crash takes its mailbox with it on a link that
  loses nothing (`SysState.down`), and on a lossy link the message can be dropped.
- *The receiver never stops.* A stop takes it down as a crash does (`SysState.settle`), and loses
  the message the same way. A start that stops does too, so `recover` is covered as well as
  `step`. The premise is of every state, not only those reached: an actor that stops only in a
  state its spec does not cover (rule 3.1) does not meet it, though it may never stop in a run.
  A premise over reachable states would be weaker; it is not done, since the scheduler and the
  video site never stop in any state.
- *Not premises.* The sender may crash after it sent: its crash takes only the messages to it.
  Links may duplicate: a duplicate handled counts. Links may be ordered: what is ahead goes first.

`attach_end_handled` keeps the scheduler's own premise, no crash of the scheduler, which
`Schedule.held_leaves` needs. It asks the premises of the receiver of every actor of `sys`,
which is simpler than naming the actors `use.answer` and `use.notice` reach; the video site has
one actor.

## Why not through the views

The views of D41 and D86 each hide this message. Seen from `a` it is an output handed over, which
`Wiring.shown` does not show; seen from `b` it is a message from outside, which `thinRight` leaves
out. Composing the two would need a link between the hand-over in the run of `a` alone and the
input in the run of `b` alone that neither projection keeps. In the join the message is simply in
flight, so the lemma is `System.Run.Fair.handled` of the join itself. What is particular to the
join is the step that puts it in flight (`SysState.mem_net_of_leftDeed`, `Wiring.mem_sends_left`)
and that an actor of a side never stops in the join if it never stops alone
(`Wiring.isStop_left`, `Wiring.isStop_right`). The views are still how the job is shown to end:
`Schedule.attach_held_leaves` is `held_leaves` through `System.LeadsTo.join_left`.

`attach_end_handled` takes the position at which the job leaves; the step there is the scheduler
handling a message, since a start leaves its jobs as they are (`SysState.step_left_state`); that
step emits the end (`Schedule.ends_of_leaves`), the wiring routes it to `sys`, and
`routed_right` delivers it.

## How D87 would use it

The site is `Videos.alone config`, one actor whose step and start only emit (`outs.map .emit`),
so it never stops. D87's claim is of runs with no crash. With the links between the scheduler and
the site losing nothing, both ways, the videos PR could prove:

> In a fair run of `Videos.system config` in which no actor is crashed and the links between the
> scheduler and the site lose nothing, a delete the site answers for `v` is followed by the site
> handling the end of the delete of `v`'s object: an answer `o` to `.delete v` that the
> scheduler's step leaving the job emitted. Where `o.givenUp`, the site emits `Out.orphan v`
> (`Videos.Site.delete_reported`); where `o` is a success, the scheduler said so only in the
> step that took the store's answer to an attempt (`Schedule.succeeded_replied`).

The chain: the site's answer emits the scheduling (`Videos.Site.delete_schedules`), and
`routed_left` delivers it to the scheduler. The scheduler's step on it either holds a new job,
whose end `attach_end_handled` delivers; or refuses it at `maxJobs`, an answer that
`routed_right` delivers and the site reports; or answers `already`, because a delete of `v` is
held, whose end `attach_end_handled` delivers from that state. Two steps are left to the videos
PR. `attach_end_handled` does not say which answer ends the job, and `scheduled` and `already`
are answers to the same key: that a job leaves with `succeeded`, `failed` or `cancelled` is true
of `onJob` but not stated by `Schedule.ends_of_leaves`. And the end may be a notice, which a call
job never gives but the statement allows.

## Consequences

- Liveness of a requester beside a behaviour now crosses the join: what `Jobs.attach` answers can
  be delivered the same way, which `docs/status/areas/behaviours.md` (removed) lists as not yet carried.
- `routed_right` covers outputs emitted as an actor handles a message, not as it starts.
  `handled_right` covers any message in flight, so a start's output is delivered once it is
  known to be in flight.
