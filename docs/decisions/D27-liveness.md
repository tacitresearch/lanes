# D27. Liveness: infinite runs, weak fairness per obligation, leads-to

Status: Accepted

`Lanes/Semantics/Liveness.lean`, `Lanes/Semantics/FairRuns.lean`,
`Lanes/Semantics/GateLive.lean` (removed). Everything proved before this was safety. "Every request is
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
  makes (`Lanes/Core/FairScheduler.lean`, executable, checked on runs in `Tests/Fair.lean`):
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
- What the change buys is a theorem (`Examples/WatchdogProofs.lean` (removed)). A dog arms its `silence`
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
