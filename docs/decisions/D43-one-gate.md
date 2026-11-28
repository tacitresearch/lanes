# D43. One gate: `serve` runs the gate joined in front

Status: Accepted

`Lanes/Web/Http/Gate.lean`, `Lanes/Web/Http/Front.lean`, `Lanes/Web/Http/FrontSound.lean`, `Lanes/Semantics/Front.lean`, `Lanes/Web/IO/Server.lean`.
D41 ended with a plan to retire the hand-built `gated`; this is it.

- *What `serve` runs.* `served sys bridge config` is
  `(fronted sys bridge config).filterMapIO .inl Sum.getLeft?`: requests in, responses out, and an
  output of `sys` that is no response not put out, as `gated`'s gate dropped it. So from outside
  nothing changes: `serve` and `serveWith` take the same arguments, a journal's inputs are
  written with the same codec, and a caller that only uses the `Server` it gets back changes
  nothing. Running `fronted sys` itself, as `serveFronted` does, with its other outputs dropped,
  would be thinner, but its inputs are `(ReqId × Request) ⊕ σ.In`, and `serve` has no codec for
  `σ.In` to write a journal with; nor should a server that takes only requests have a type that
  admits other inputs.
- *Its theorems are theorems about it.* `served_answered_le_arrived`, `served_answered_nodup`,
  `kernel_served_answered_le_arrived` and `served_deadlines_armed` follow from those of `fronted`
  by `SysState.run_filterMapIO` and `System.Invariant.filterMapIO`; `served_pending_leaves` and
  `served_pending_answered` by `System.LeadsTo.filterMapIO` and `System.underView_projects`,
  since `Sum.getLeft?` shows different outputs differently. The statements are those of
  `gated`'s theorems with the gate at `.inl ()` instead of `none`, under the same assumptions.
- *What went.* `gated`, `gatedSig`, `GatedMsg`, `liftEffect`, the actor `gate`, `gate_bounded`
  and `gatedActors` from `Gate.lean`; `GateSound.lean` (431 lines) and `GateLive.lean` (226
  lines). `Http.outside` is now `Http.servedOutside`, the same assumption stated for the
  signature of `served`. The tests of `gated` (`Tests/{Gate,Fair,SystemSound,Web}.lean`) check
  `served`, each property they checked: in `Tests/Gate.lean` the hostile environment crashes
  every actor, not only the gate, since `gated` gave no other way to say "the gate".
- *Old journals of served systems are refused.* A journal's inputs would read back, and a
  snapshot's ids too (`Unit ⊕ σ.Id` is written as `Option σ.Id` was), but in `gated` an output of
  `sys` that is no response was a message to the gate, so a snapshot of `gated` can hold a state
  `served` never reaches. `serve` now names its journal `ServerConfig.journalName`: the
  application's `system` and the configuration of the gate, whose step function reads it (as
  raft-kv's journal names already did). So a journal written by `serve` before this change, or
  under a gate with another timeout or bound, is refused and left as it was. To make the refusal
  say what happened, a foreign journal's refusal carries the name its header gives
  (`Refusal.foreign`), and the message names both: `it is the journal of "bank 1", not of "bank
  1, behind a gate of 30000 ms and 1024 requests"`. Such a journal cannot be carried over: the
  application starts afresh, or keeps the old version until its state is moved by other means.
  `Tests/Web.lean` writes a journal byte for byte as the old `serve` did and checks that it is
  refused so.
