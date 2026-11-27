# D?. A fair run of a join is a fair run of its right side too, by the join with its sides exchanged

*Supersedes the limit of D41 that the right side is not done.*

`Lanes/Proof/JoinSound.lean` (section `ThinnedRight`), `Lanes/Semantics/FairJoin.lean` (`The
right side`). D41 proved that a fair run of `a.join b w`, seen from `a` without the messages from
outside, is a fair run of `a` alone, and left `b` open because `b` boots after `a`. The exact
mirror holds: every fair run of the join, seen from `b` without the messages from outside in
flight (`SysState.thinRight`), is a fair run of `b` alone under `EnvModel.right`, state for state at
corresponding positions and with the same deeds up to them (`System.Run.Fair.right`), and what `b`
alone leads to of its actors it leads to in every join (`System.LeadsTo.join_right`).

- *The boot order is no obstacle to the thin view.* What the boot of `a` sends `b` is a message
  from `a`, and seen from `b` every message from `a` is from outside. The thin view leaves those
  out, so until `b` boots the view is blank, and the join's start is `b`'s start alone followed
  by handing over the outputs the wiring routes to `a`
  (`SysState.init_thinRight`). No prefix of the run has to be skipped, and no statement weakened.
  The view that keeps the messages from outside would differ here (`System.Reachable.right` is up
  to `SysState.Equiv` for this reason), but it is no view of fair runs anyway (D41).
- *A step is carried through the swap, not proved again.* `SysState.step_swap` gives each step of
  the join as a step of `b.join a w.swap`, whose left side is `b`. The step-by-step simulation of
  D41 (`SysState.exists_block`) asked for a reachable state of the join; it uses only two facts
  of it: no output that the wiring routes to the other side waits, and every message from outside
  is an input the side accepts. Its cases now take those two facts (a private `Tidy`), so they run
  on `c.swap`, which is not reachable in the exchanged join. On the right the two facts come from
  `System.Reachable.right_unwired` and from `System.Reachable.accepted` through
  `System.Reachable.right`, since `SysState.Equiv` keeps what is in flight. The swapped run's
  view, timers armed and events are those of the right side (`SysState.exists_blockRight`).
- *Copying the left-side proof was the alternative.* It is about 500 lines of cases by event,
  and two copies would have to be kept in step. The swap costs a few lemmas about what `Event.swap`
  shows and arms.

Consequences:

- What the right side of a join leads to alone, it leads to in the join, with no premise about
  the boot of the left side. Raft behind its front is on the right; its liveness, when proved
  alone, carries over by `System.LeadsTo.join_right`.
- `SysState.exists_block` keeps its statement; the generalized form is private.
