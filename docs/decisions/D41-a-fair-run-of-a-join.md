# D41. A fair run of a join is a fair run of its left side, seen without the messages from outside

`Lanes/Semantics/{Projection,FairJoin,FrontLive}.lean`, `Lanes/Actors/{JoinSound,MapIOSound,Run}.lean`.
D31 left `gated` in place because its liveness theorem is about its own fair runs and nothing
carried a fair run of a join to a fair run of one side. This is that theorem, and with it the
liveness of `fronted`.

- *Projection of fair runs, in general.* A `System.View` relates states of `sys` to states of
  `sys'`, lifts each obligation of `sys'` to one of `sys`, and says what events of each show.
  It projects (`View.Projects`) when every step of `sys` from a reachable state is a finite run of
  `sys'` between related states (`View.Block`) that shows what the step shows, takes the
  obligation whose lift the step takes, starts the wait for it again wherever the step starts
  the wait for its lift again, and passes only through states that agree with the state before
  or after the step; and when what `sys'` owes in a related state, `sys` owes too, as its lift.
  Then every fair run of `sys` is seen as a fair run of `sys'` (`View.Projects.fair_run`):
  position `n` at `f n` with `f` strictly increasing, related states there, the same deeds up to
  there, and every state between agreeing with a state of the run of `sys`; and leads-to carries
  over (`View.Projects.leadsTo`). The run of `sys'` is the finite runs one after the other, each
  followed by one stutter, so it is infinite where `sys` stutters forever
  (`System.Run.ofBlocks`); it is chosen step by step, so the proof uses choice.
- *The join, seen from the left.* The suggestion of D31 was right, and the thinnest view is
  needed: the join seen from `a` with the messages from outside in flight left out
  (`SysState.thinLeft`). Each step of the join from a reachable state is then a run of `a`
  alone with nothing left to choose (`SysState.exists_block`): a message from outside is put in
  as an input just before the join delivers it (and an outside message's mail for a start is
  put in, the actor started and the message dropped again), and after each step of an actor of
  `a` the outputs the wiring routes to `b` are handed over. Two invariants of the join make it
  exact: no output routed to `b` waits in the join (`System.Reachable.left_unwired`), and every
  message from outside is an input `a` accepts (`System.Reachable.accepted`, of every system).
  The view that keeps the messages from outside, `c.left`, is no such view: two equal messages
  from different senders are two messages in the join and one kind alone, and when the join
  delivers the newer of `[u, v, u]` it leaves `[u, v]` where `a` alone leaves `[v, u]`.
- *Fairness carries over, with no assumption.* An obligation of `a` that is due in the view is
  due in the join as `Obligation.inl`: a message between actors of `a` is deliverable in both or
  neither (`SysState.deliverable_of_thinLeft`), a stopped actor with mail in the view has mail
  in the join, an output waiting in the view waits in the join. A message from outside is never
  in the view, so `a` never owes its delivery. The one obligation of `a` alone that is not one of
  the join is an output the wiring routes to `b`, a message to `b` in the join, which the run
  alone hands over in the same block; so the join cannot starve it: delivering it to `b`, or
  never delivering it, leaves `a` alone owing nothing. A step of the join that arms a timer of
  `a` is a run alone that arms it. `System.Run.Fair.left` is the theorem D31 asked for, for every join and every
  environment model, and `System.LeadsTo.join_left` carries leads-to about the states of `a`'s
  actors into every join.
- *Behind hidden inputs and outputs.* A fair run of `sys.filterMapIO input output` is seen as a
  fair run of `sys` event for event, with each hidden output handed over in the step that emits
  it (`System.underView_projects`), when `output` shows different outputs differently. Without
  that, handing over a shown value hands over any of the outputs shown as it, and an arbitrary
  choice can leave one output of `sys` waiting forever while its twins go. A choice that always
  takes the oldest would be fair again, by a counting argument over many steps; it is not done,
  since `frontedOutput` is injective where it shows.
- *The liveness of `fronted`.* The argument of `GateLive` is made once more, on the gate alone,
  with one actor and any link from outside (`Gate.pending_leaves`, `Gate.pending_answered`), and
  carried through the two projections: `fronted_pending_leaves` and `fronted_pending_answered`
  are the statements of `pending_leaves` and `pending_answered` for `fronted sys`, for every
  `sys`, with the same one assumption, that the environment does not crash the gate. Nothing in
  their proofs looks at a step of `fronted sys`. The answer the gate hands over alone is found
  in `fronted sys` through the deeds the projections keep (`View.Sees.shown_after`).
- *Checked first.* `Tests/Fronted.lean` checks the premises of the leads-to rule on the gate
  alone under the link from outside that a join gives it (`EnvModel.left`, which loses,
  reorders and duplicates), to depth 9, and that a request leaves the gate only in a step that
  emits its answer.

Consequences and limits:

- *The right side is not done.* For the right side the boot order of D25 is in the way: `b` boots
  after `a`, so `c.swap` is not a reachable state of `b.join a w.swap`, and the two invariants
  above must be stated for it directly; the start of the view is `b`'s boot, after `a`'s has put
  messages for `b` in flight, which the thin view leaves out (so the view is exact there, unlike
  `System.Reachable.right`); and the obligations and arms must be carried through
  `SysState.step_swap`. Raft behind its front is on the right, so its liveness needs this.
- *What retiring `gated` takes.* Every theorem of `GateSound.lean` has its counterpart for
  `fronted` already (`fronted_answered_le_arrived`, `fronted_answered_nodup`,
  `kernel_fronted_answered_le_arrived`, `fronted_deadlines_armed`), and every theorem of
  `GateLive.lean` that is not a premise has one now. `Gate.lean` keeps `Bridge`, `GateConfig`,
  `GateMsg`, `Gate.step` and loses `gatedSig`, `liftEffect`, `gate`, `gated`, `gatedActors`
  and `outside`; `GateSound.lean` and `GateLive.lean` go; `serve` and `serveWith` in
  `Lanes/Env/Http.lean` run a fronted system; `Tests/{Gate,Fair,SystemSound,Web,Axioms}.lean`,
  `TRUSTED.md` and the docs follow. The served system can keep `gated`'s signature from outside
  as `(fronted sys bridge config).filterMapIO .inl Sum.getLeft?`: requests in, responses out,
  outputs that are no response dropped as the gate drops them now, and its theorems follow from
  those of `fronted` by `run_filterMapIO`, `Invariant.filterMapIO` and `LeadsTo.filterMapIO`
  (`Sum.getLeft?` is injective where it shows). Then a journal's input records are written as
  now. Actor ids become `Unit ⊕ σ.Id` for `Option σ.Id`; `Codec.sum Codec.unit` writes them as
  `Codec.option` does, so a snapshot's ids and messages read back. The two systems still differ:
  in `gated` an output of `sys` that is no response is a message to the gate, in `fronted` it is
  an output, so a snapshot taken by `gated` can hold such a message, which `fronted` never sends,
  and is then not a state `fronted` reaches. A journal written by `serve` before the change should
  therefore be refused rather than read (a new `ServerConfig.system`), or cut fresh by the old
  server first.
