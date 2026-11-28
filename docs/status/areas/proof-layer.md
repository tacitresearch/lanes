### Proof layer

Where: `Lanes/Semantics/`.

- A fair run of `a.join b w`, seen from `a` without the messages from outside in flight, is a fair run of `a` alone under `EnvModel.left`, state for state at corresponding positions and with the same deeds up to them (`System.Run.Fair.left`), so what `a` alone leads to of its actors it leads to in every join (`System.LeadsTo.join_left`).
- A fair run of `a.join b w`, seen from `b`, is a fair run of `b` alone under `EnvModel.right`, though `b` boots after `a`: what the boot of `a` sends `b` is from outside, so the view leaves it out and starts where `b` alone starts (`System.Run.Fair.right`, `System.LeadsTo.join_right`).
- A message in flight on a link that loses nothing, to an actor that stays up, is handed to it (`System.Run.Fair.delivered`, by what is ahead of it on its link).
- A receiver that is down has mail, so fairness starts it (`System.Run.Fair.handled`).
- Every run of a system that implements a service has a sequential history of the service's acts that produces each output handed over, takes each input after it arrives and respects real-time order, a deadline passing in it exactly in the block of the position at which the run shows it (`System.Implements.history`, `System.Implements.Explains.fired`, `fires`, `System.Implements.produced`), so what is proved of the service's functions holds of the system's outputs.
- Fair runs and leads-to carry over to a system behind hidden inputs and outputs, when the output map is injective where it shows (`System.underView_projects`, `System.LeadsTo.filterMapIO`).
- Fair runs exist: every finite run extends to a fair run, for every system and environment model (`System.exists_fair_run_of_run`), so every reachable state is on one.
- Fair runs project: a view under which each step of one system is a finite run of another and the obligations match carries fair runs to fair runs and leads-to with them (`System.View.Projects.fair_run`, `leadsTo`).
- Lemmas about sums.
- Liveness: infinite runs with stuttering (`System.Run`), weak fairness for each `Obligation` of the system on its own (deliveries, timers, starting an actor that has mail, outputs; never the environment's events), where a timer is obliged to fire only if it stays pending and no step arms it again, as in the runtime (`Obligation.Restarted`; a watchdog that is pinged forever never barks in a fair run, `examples/watchdog/Watchdog/Proofs.lean`), `System.LeadsTo` with its proof rule (`LeadsTo.ensures_of_invariant`), transitivity and monotonicity.
- The standard simulation of a service behind actors (`Account`: inputs pending and outputs owed on messages, in states and in a witness, the value as a relation), with which an application proves only what each step of an actor does to it (`Account.Handles`, `Account.implements`), and with deadlines what a step that passes one does (`Account.HandlesFire`, `Account.implements_timed`), each case knowing where its message came from (`System.Sent`, `System.Armed`: every message in flight is an input or one some step sends, every timer one some step arms, `System.traced`, for every system), the messages on one link in order (`linkMsgs`) with what sending, delivering the oldest, losing and a crash do to them, and refinement case by event with only the losses the environment has (`System.Refines.of_timed_events`, `of_events`; `docs/decisions/D52-standard-simulation.md`).
- The system semantics as a CSLib `LTS`.
- What one side emits and the wiring routes to the other, which neither view shows, is handled by the other side, on a link that loses nothing, by an actor the environment does not crash and that never stops (`System.Run.Fair.routed_right`, `routed_left`, `handled_right`, `handled_left`).
- `Service.once`, the spec of a service whose clients name their requests, where a key takes effect at most once and an answer may be handed over again, and `System.Refines.of_handles`, the proof rule for a simulation that reads messages in flight as a set, which holds in every environment.
- `Service.spec`, over inputs and outputs (`Service In Out S T`, written before the actors), with deadlines `T` that pass as visible steps, and `System.Implements sys env svc deadlines delivered`, refinement with the system's timers that `deadlines` names firing them and the deliveries that `delivered` names passing them where a message is served (`docs/decisions/D42-a-spec-names-its-inputs-and.md`, `docs/decisions/D56-a-deadline-passes-where-it-is-served.md`; how long a deadline lasts is not modelled).
- `Spec`, `Refines` (weak simulation with a label map), `of_map`, `trans`, trace inclusion.

Known limits:

- Liveness theorems are about fair runs of the semantics. That the runtime's runs are fair is not proved, and "eventually" carries no bound.
