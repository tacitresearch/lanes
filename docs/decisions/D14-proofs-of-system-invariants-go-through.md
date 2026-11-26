# D14. Proofs of system invariants go through per-event lemmas

`Lanes/Actors/Step.lean` states, for each event, when it is enabled and the exact next state
(`step_deliver`, `step_drop`, …). A system invariant proof cases on the event and rewrites with
these; conservation proofs add `sum_update` and `sum_map_erase` from `Lanes/Semantics/Sums.lean`.
`Examples/BankProofs.lean` is the worked example and the shape `lanes prove` will generate.
`Lanes/Actors/Run.lean` has the step in closed form (`SysState.settle_eq`: what the effects
send, arm and emit, added at once), for proofs that follow a state through a step.
