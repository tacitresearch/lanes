# D31. The gate is a system, joined in front; what a join keeps of a run is its deeds

`Lanes/Http/{Gate,Front,FrontSound}.lean`, `Lanes/Actors/{Deed,MapIOSound}.lean`,
`Lanes/Env/{Http,Node}.lean`. `gated sys` (D19) turns every output of `sys` into a message to
the gate, so a system whose outputs are not all responses cannot sit behind it: a shard's
parcels would be swallowed, and a process could not have both an HTTP front and peers.

- *The gate alone.* `gateSystem bridge config` is one actor. Inputs: a request with its id, or
  an output of whatever is behind. Outputs: a response with its id, or an input for what is
  behind. Its decisions are `Gate.step`, which the gate actor of `gated` now calls too: the
  function takes the four things a gate does (respond, pass on, arm, disarm) as effects of the
  place where it sits, so there is one statement of when a request is admitted, refused,
  answered and timed out. `Gate.step_bounded` is proved once for both.
- *The composition.* `fronted sys bridge config` is
  `((gateSystem bridge config).join sys (frontWiring bridge)).filterMapIO frontedInput
  frontedOutput`. The wiring sends what the gate passes on to `sys`, and to the gate each
  output of `sys` that `bridge.encode` reads as a response. Inputs are
  `(ReqId × Request) ⊕ σ.In` and outputs `(ReqId × Response) ⊕ σ.Out`: `.inl` goes through the
  gate, `.inr` passes it by. The gate is on the left because the left side of a join has the
  exact projection theorem and boots first, as the gate does in `gated`.
- *Hiding.* A join's signature keeps the inputs and outputs it wires. The inputs are open: from
  outside one could hand the gate a forged output of `sys`. `frontedInput` leaves that input
  out. The wired outputs are never put out, but `System.mapIO` maps outputs with a total
  function and has nowhere to send them, so `System.filterMapIO` was added: `mapIO` whose
  output map may answer `none`. `SysState.run_filterMapIO` and `System.Invariant.filterMapIO`:
  a system behind hidden inputs and outputs does nothing it does not do in the open, event for
  event. `mapIO` is now defined as `filterMapIO` that hides nothing, so both theorems are
  about it too.
- *At most once, by projection.* `Gate.answered_le_handled`: alone, in every environment and
  whatever arrives on its two inputs, the gate hands over no more answers to an id than it
  handles arrivals of that id. `fronted_answered_le_arrived` is that statement carried into
  `fronted sys` for every `sys`: no id is output more often than it was input, where the link
  from outside to the gate does not duplicate. Every other link may lose, reorder and
  duplicate, and every actor may crash.
- *Deadlines, by projection.* `Gate.deadlines_armed` is an invariant of the gate's state, so
  `System.Invariant.join_left` carries it as it stands: `fronted_deadlines_armed` is one line.

What the projection theorems could not carry, and what was added:

- `System.Reachable.left` is about states, and "no more often than" counts events. A state
  holds no count of what has been handed over. So the induction behind it now carries what the
  run shows: `Deed` is an actor handling a message or an output handed over, and
  `SysState.run_left` says a run of a join, seen from the left system, is a run of that system
  alone that shows the same deeds in the same order. The change to the proof is an index on the
  relation it already carried; no step of it is new. The outputs the wiring routes to the
  other system are handed over in the run alone and are not among the deeds compared.
- The two runs do not share inputs. Seen from the left system every message from outside and
  from the other system is an input on one link, modelled as `Link.network` (D25), so alone the
  system may handle one input twice. "No more often than it arrived" is therefore false of the
  gate alone under that link: one refused arrival, duplicated, is answered twice
  (`Tests/Fronted.lean`). The statement that survives projection is about handling, and the
  link assumption is discharged in the join, where the link from outside to the gate is still
  its own: `System.handled_le_put`, a kind of message that no actor sends and no timer carries
  is handled no more often than it is put in, if the links it arrives on do not duplicate.
  This is the general shape: prove of the part what holds per message handled, and of the
  whole who can send that message.

The server. `Lanes/Env/Http.lean` has one loop, `serveOn`, for any system with a gate in it.
`serve` and `serveWith` run `gated sys` on it as before. `serveFronted` runs `fronted sys`: an
output that is no response goes to the caller, and `Server.tryInput` takes an input that is no
request, typed so that a request cannot be handed in that way and ids stay the server's.
`Http.serveShard` (`Lanes/Env/Node.lean`) is the process `systems/raft-kv` needs:
`fronted (sys.shard hosts)` on one runtime, with `Peers` carrying the parcels.

Consequences and limits:

- *A response has to be put out where the request came in.* Request ids are each process's
  own. A response put out by an actor on another shard reaches that shard's gate, which drops
  it or, worse, has another client waiting under the same id. A system spread over processes
  must bring the answer back to an actor of the process that took the request. Nothing
  prevents the mistake yet. `Tests/Fronted.lean` shows the mild case: a balance asked through
  the front of the shard that does not host the account is answered `504`. Giving each front
  its own range of ids would make every case the mild one.
- *`gated` is still there.* Its theorems (`GateSound`, `GateLive`) are about its own steps.
  Liveness is what keeps it: `Http.pending_answered` is about fair runs, and there is no
  theorem yet that a fair run of a join, seen from one side, is a fair run of that side.
  `run_left` is the finite half. Nor is `gated sys` a case of `fronted sys` on the nose: in
  `gated` an output the bridge does not read is a message to the gate, which ignores it, and in
  `fronted` it never reaches the gate. An equivalence would be a simulation up to those
  messages. Redefining `gated` would also change its actor identities from `Option σ.Id` to
  `Unit ⊕ σ.Id`, and with them every journal a served system has written.
- *`fronted` on a journal.* `serveFronted` takes a `log` the caller opens, with
  `frontedActors` for snapshots (`Tests/Fronted.lean` restarts the bank that way);
  `ServerConfig.journal` is read by `serve` only, since a codec for the inputs that are no
  request is the application's to give.
