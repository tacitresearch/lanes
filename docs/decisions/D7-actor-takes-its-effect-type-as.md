# D7. `Actor` takes its effect type as a parameter

Status: Accepted

`Actor S Msg Eff`. Actors in a system use `Eff = Effect σ i` (`σ.Actor i S`). Library actors
keep `Eff` abstract and are placed in a system with `Actor.mapEff`.

Why: a reusable actor (a rate limiter, a Raft node) must not mention the signature of the system
it ends up in. Invariants transfer along `mapEff` (`Actor.Invariant.mapEff`).
