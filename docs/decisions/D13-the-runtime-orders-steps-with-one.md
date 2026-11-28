# D13. The runtime orders steps with one logical clock

Status: Superseded by D18

Every step takes a number from a global counter and each message carries its sender's number.
When an actor stops, messages numbered at or before the stopping step are dropped with the
mailbox and later ones are carried into the next mailbox.

Why: `SysState.down` says precisely which messages a stopping actor loses. Without the clock,
"sent before the stop" depends on thread timing and recorded traces do not always replay.
With it, the recorded trace ordered by step number is a run of `SysState.step`, which is what
`Tests/Runtime.lean` checks.
