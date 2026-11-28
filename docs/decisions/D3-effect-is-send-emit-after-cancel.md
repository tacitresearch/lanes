# D3. `Effect` is `send | emit | after | cancel | stop`; no `io`, no `reply`

Status: Accepted

*Departs from the DESIGN sketch of `Effect`.*

- `io (req) (onDone : ExtResponse → Msg)` is gone. An external system is an actor identity whose
  behaviour in the semantics is its model and whose behaviour in production is an adapter
  (DESIGN Phase 5 already says this). Calling it is a `send`; its answer is an ordinary message.
- `reply` is `emit (out : σ.Out)` for answers leaving the system, and `send` between actors.
- `cancel` is new. A timer is identified by its message: `after` on a pending timer restarts it,
  `cancel` disarms it.

Why: a function inside an effect (`onDone`) cannot be stored in a state that must be hashed and
compared. Timers without cancel leave stale timers pending, which multiplies model-checker
states for protocols such as Raft that reset election timers.
