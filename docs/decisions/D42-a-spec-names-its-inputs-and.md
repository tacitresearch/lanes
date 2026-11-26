# D42. A spec names its inputs and outputs, and time passes in it as deadlines the system's timers are

The ledger (`systems/ledger/README.md`, friction log) found two limits of `Service`.

*A spec of inputs and outputs.* `Service In Out S` replaces `Service σ S`: a spec reads only
the inputs and outputs, so it is written before the actors exist, and the system-level notions
take the signature's: `System.Implements sys env svc` asks `svc : Service σ.In σ.Out S`, the
monitor is `Check.Monitor In Out S`, and `Visible In Out` is what the outside world sees. Every
statement is the old one with `σ` read as `σ.In` and `σ.Out`. One thing is lost at call sites: a
spec no longer fixes the signature, so where nothing else in the arguments does before a
hypothesis about a check is unified, the signature is named (`Check.refines_sound (σ := sig K V
F) spec ...` in `Tests/SystemSound.lean` and `systems/raft-kv/RaftKVProofs/Checked.lean`);
without it the elaborator unfolds the check itself and runs out of time.

*Time.* The semantics has no clock: an armed timer may fire at any moment, in any order with the
others, whatever its delay (`SysState.step`, `.timeout`). Time shows in a run only as timers
firing. Three ways of giving a spec time were weighed.

- *Time passing as internal steps of the spec.* A deadline would pass by a `τ` step, which the
  system's timer firing is answered by. This is stuttering refinement, and TLA+ refinement
  allows it, but it says nothing a client can see: the spec may let a deadline pass at once, so
  a lockout that never locks is one the spec allows, and so is a session that ends at once.
  For safety it is the spec without the deadline.
- *A clock the environment supplies (`now`).* This is Abadi and Lamport's recipe for real time
  in TLA (*An old-fashioned recipe for real time*, 1994): time is a variable, deadlines are
  variables compared with it, and a step that advances time is a step like any other. It needs
  the system's timers to fire at the time they were armed for, which the semantics does not
  model, and every proof about timers would change. It is the right model for a system that
  reads the time (`Lanes/Env/Clock.lean`): there the time is an input, and a `Service` already
  sees it.
- *Deadlines passing, visible, matched to the system's timers.* In timed I/O automata (Lynch and
  Vaandrager, *Forward and backward simulations, part II: timing-based systems*, 1996; Kaynar,
  Lynch, Segala and Vaandrager, *The theory of timed I/O automata*, 2006) the passage of time
  is a visible action: the implementation may take internal steps, but time passes in both at
  once. With no clock, the moments a run has are its timers firing, so a spec names its
  deadlines and a system says which of its timers are which deadline.

The third is taken. `Service In Out S T` has a type `T` of deadlines, which state they are
armed in (`armed`) and what one passing does (`fire`); with `T := Empty`, the default, it is the
service of before. `Service.spec` has a visible label `fire t`, enabled when `t` is armed, that
takes effect at once: inputs pending may take effect before or after it, as they may around any
step, but nothing can put it later, so after a session's deadline the session is over, and
before a lock's deadline the account is locked. A deadline passing that took effect later,
like an input, would allow a session that never ends. Which deadlines are armed is read from
the state, not kept beside it: a deadline is in force exactly while what it ends is, and the
spec holds no timers of its own (rule 1.1).

A system's side is `Deadlines σ T`, which of its timers, by actor and message, are deadlines of
the spec; any other timer (a retry, an election) is internal, as before. `Event.timed deadlines`
shows a timer firing as `fire t`, `Event.visible` is `Event.timed` with no deadlines, and
`System.Implements sys env svc deadlines` is refinement along it. The driver sees timers fire
(`Driver.timeout`), as it sees outputs: the clock is part of the outside world.

A system's timer that a run fires is seen by the driver and the checker as an event of the
outside world (`Driver.timeout`, `Scenario.Reachable.timeout`), like an output, so the merging of
worlds keeps the monitor's state apart for each (`Driver.Respects.timeout`).

The monitor stays exact and finite. The spec's internal steps are still only pending inputs
taking effect, so the closure is the one of before; a deadline passing keeps the candidates in
which it is armed, fires it, and closes again, since inputs pending after it may take effect
after it. `Check.Monitor.sound`, `complete`, `ok_iff`, `Service.monitored_respects`,
`Check.refines_sound` and `refines_traces` hold for every `T` and every `deadlines`.

Limits:

- *How long a deadline lasts is not checked.* The spec says which deadlines there are, when they
  are armed and what their passing does; that a lock lasts five minutes is the delay the system
  arms its timer with, which the semantics ignores. A system that arms the lock's timer at the
  first failure instead of the last refines the spec, though its lock is short. Checking delays
  needs a semantics in which timers fire in the order of their deadlines.
- *A deadline lost in a crash may never pass.* The spec then keeps it armed for ever, which is
  safe: a lock that is never lifted, a session that is never ended by time. That it passes is
  liveness, which is fairness of the system's timers (`Obligation.timeout`).
- *A system's timer that is no armed deadline is a violation.* A timer that fires after what it
  ends is over (a session's expiry after its log-out) must be cancelled, or not be named a
  deadline.
- *A deadline passes where its timer fires.* A system that decides a request at one actor and
  serves it at another, as the ledger does (the user checks the session, the ledger serves),
  refines a spec without deadlines, but not one whose deadline is seen at the deciding actor:
  a request decided before the deadline and served after it can see a request that arrived
  after the deadline (`systems/ledger`, found in 43 steps). The cure is to let the deadline pass
  where requests are served, by naming the delivery of a notice as the deadline; `Deadlines`
  names timers only, and extending it to deliveries is the next step.

Used: the ledger's spec (`systems/ledger/Ledger/Spec.lean`) has a lock lifting and a session
ending as deadlines, and its system is checked against them with its timers firing at any
moment (12,577 states, pass); a lockout that does not lock is found in 26 steps. A lease in
`Tests/Lease.lean` refines its spec with its timer named the lapse, and does not when the timer
is not named or the lease is freed before the timer fires.
