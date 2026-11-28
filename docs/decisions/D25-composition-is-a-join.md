# D25. Composition is a join, and what survives it is projection

Status: Accepted

`Lanes/Core/Join.lean`, `Lanes/Proof/JoinSound.lean`. `System.join a b wiring` is one
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
- `SysState.Equiv` started in the checker; it is in the core now (`Lanes/Proof/Equiv.lean`),
  since theorems about systems put together are stated up to it.
