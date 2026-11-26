# Trusted code

Everything Lanes asks you to trust rather than proves, listed in one place (rule 5.5). A property
of an application is only as strong as this list. Keep it short, and add an entry in the same
change that adds trusted code.

## Trusted by every Lean program

The Lean kernel, compiler and runtime, `Std.Async`, `Std.Sync`, `Std.Http`, libuv, the C
toolchain, the operating system and the hardware.

## Trusted in Lanes

| What | Where | Why it is trusted | How it is checked |
| --- | --- | --- | --- |
| The runtime shell | `Lanes/Actors/Runtime.lean`, 334 lines | It takes everything that has arrived in its inbox, reads the clock, calls the kernel once for each input and hands the kernel's outputs to the adapter. Who is refused, who waits for room and who is woken is `Mailbox`, pure and tested; the shell keeps one in a reference and resolves the promises it is handed. That it hands them on unchanged, all of them and in order, is not proved. Nor is its ending: that `stop`, or a journal that cannot be written, ends the shard and leaves no caller waiting. With a journal, it is trusted to append the entries of the turns of a batch, in order and in one write, before it hands any of their outputs over, to hand over at start the outputs `Journal.resume` says were not marked as handed over, and to save the kernel only after a turn's outputs are handed over and to go on with the kernel the save restores. What a turn asks of the kernel and which entries describe it are not the shell's: they are `Journal.turn`, proved (`Journal.turns_kernel`). | `Tests/Runtime.lean`: one input's several outputs and the boot outputs compared exactly; recorded events replayed through `SysState.run`; timers, back-pressure, stopping an idle and a busy shard. `Tests/Scale.lean`: a message costs the same at 1,000 and 100,000 actors. `Tests/Durable.lean`, on a journal held in memory: every input is in the journal before an output it caused is handed over; outputs not marked as handed over are handed over after a restart and marked ones are not; when a write fails the shard ends, reports the error and releases every caller, also those whose commands it had not yet taken; a shard started on a journal as long as the distance between two saves saves at once. Each of these fails on the mutant that breaks it. |
| The router between shards | `Lanes/Actors/Cluster.lean`, 106 lines | It starts one runtime per shard and carries each parcel a shard puts out to the shard that hosts its receiver. That a parcel arrives once, at the right shard, in the order sent, is not proved. What is proved is the model it has to implement: two shards joined, with each parcel one emits an input of the other, behave as the one system (`System.SplitReachable.merged` in `Lanes/Actors/ShardSound.lean`). Still trusted: that the runtimes and this router together are that join, and the same for more than two shards (`PLAN.md` B.1). | `Tests/Cluster.lean`: the bank on four shards with transfers crossing between them, floods across three shards that all arrive, counts sent both ways between two shards that arrive in the order sent (the one live test that fails when a mailbox hands parcels on newest first), and the same results from one shard and from four. |
| The transport between processes | `Lanes/Env/Peers.lean`, 189 lines | It listens, connects, sends, receives and closes, as the courier tells it, and tells the courier what happened. It reads every connection, also those it made, so that a peer that has left is noticed; it does not send a parcel larger than the receiver would take, and says so once; there is no timeout on a connection being made or on a write. It decides nothing: when to connect, what waits and what is dropped, one write at a time on a connection, what a stream of bytes is as parcels and what `stop` ends are `Peers.Courier.step`, a pure function. What the link promises is no more than `Link.network`: a parcel may be lost, arrive twice, or arrive out of order across connections, and nothing arrives that was not sent. Trusted: that an event is reported when the thing happened, that an action is done as asked, and the last of those promises. There is no authentication. | `Tests/Courier.lean`: the courier run by the model checker against a network that fails at any moment (connections not made, writes that fail, a peer that leaves, bytes in pieces, `stop` anywhere): one write at a time, nothing written twice, a bounded queue, nothing open after `stop`; three mutants of the courier fail it. `Tests/Peers.lean`: the bank on three shards joined by TCP, every credit arriving; a shard stopped and another started on the same port found again; a shard with peers on a journal, stopped and started. And the transport alone, one end sending and another keeping what arrives: three hundred parcels in the order sent; parcels that arrive in one piece handed on in order; the socket of a peer that left closed; a parcel over the limit not sent and those around it sent; a peer that leaves a connection nothing is being sent on noticed, so that the next parcel reaches whoever listens there now; a peer that was not there tried again and found. `systems/raft-kv`'s `raftProcs` uses it through the death of two leaders. Not tested: an accept that fails, a socket that cannot be made, an address that is not IPv4, that the first parcel over the limit is reported, a write that fails on a connection whose reader has not noticed, and loss on a real network. |
| The journal's files | `Lanes/Env/Journal.lean`, 117 lines | It takes a lock beside the journal before it reads anything, reads the journal and the snapshot, and does the writes it is given, one by one: an append to the journal, flushed, or a file written beside its target and renamed over it. What the files mean, which are refused, and what is written at a start, for a turn and for a save, in what order, are not its decisions: they are `Journal.Disk.read`, `Disk.mend`, `appendWrites` and `saveWrites`, pure functions over a model of the two files (`Lanes/Actors/Disk.lean`), proved to leave files that load as the kernel the shard had wherever the process dies (below). Trusted is that the model is the file system: bytes appended and flushed stay when the process dies, an append that did not finish leaves some of its first bytes and nothing else, and a rename replaces a file at once. Also trusted: that it counts the entries it writes, which gives a save the index of its mark; that it checks that entries and records fit a frame before it writes them; and that it hands the shell what `Disk.read` found. A flush reaches the operating system, not the disk: Lean's `IO` has no `fsync`. | `Tests/Durable.lean`: restart from the journal; a journal cut at eight places; a second opener refused while the first holds the journal; another system's journal, one written with another codec and one with a flipped bit each refused and left byte for byte as they were; a child process killed with SIGKILL while working, after which every request it had answered is in the journal and the state is the one the journal describes; a shard restarted from a snapshot and a cut journal; each state a save can leave the files in, built by hand; the model of the two files run on the compiled code, with a turn's append and a save's mark cut at every byte and the save stopped between any two of its writes, from each state an earlier save can leave (this is the test that fails when the snapshot and the journal are replaced in the other order); a cut journal without its snapshot refused; a process killed four times while saving every forty entries, after which its state, which is its own history, has every acknowledged input once and in order; a journal whose last entry was not wholly written, cut back to the entries before it with exactly the bytes cut off in `.cut`; and two saves with entries of every kind between them, after which the second mark has the index of all that was written before it. |
| The HTTP adapter's IO | `Lanes/Env/Http.lean`, 224 lines | It reads requests from sockets, gives each an id no other has (ids start at the length of the shard's history and go up by one per admitted request, so they stay fresh after the journal is cut), hands them to a system with the gate in it and writes the gate's one response for each. There is one loop (`serveOn`) for both such systems: `gated sys` (`serve`, `serveWith`) and `fronted sys` (`serveFronted`), where an output that is no response is handed to the caller's handler and `Server.tryInput` takes an input that is no request; a request cannot be handed in that way. It answers `HEAD` as `GET` without the body, `405` for other methods and, when the inbox is full, `503` itself. When the shard ends on an error it answers the requests in flight `503` and shuts down, and `wait` throws. It keeps one entry for each request in flight and none for a request that is answered or refused (`Server.inFlight`). | `Tests/Web.lean`, over a socket: fifty requests at once, `HEAD`, `405`, `413`, links with awkward text decoded by the real server, stopping with a request in flight, the bank restarted on a journal that was cut, with no request id used twice, a port already taken (the journal is left free and the process can exit), and a journal that stops taking writes (every request is answered and the server ends with the error). `Tests/Fronted.lean`: `serveFronted` under `serveShard`, the recorded run of each front checked against `Http.frontedOutside`, and `serveFronted` on a journal that is cut, restarted, with no request id used twice; with a handler that holds the shard and an inbox of one, the request that finds it full gets `503` at once and is not in flight, and the two that waited are answered. In `Tests/Web.lean` none is in flight once each of fifty is answered, nor after ten have run into their deadline. |
| A process with a front and peers | `Lanes/Env/Node.lean`, 47 lines | `Http.serveShard` starts `Peers` and `serveFronted` on `fronted (sys.shard hosts)` and ties them: a parcel that arrives is handed to the server as an input that is no request, and of the shard's outputs a parcel is sent to its peer and anything else that is no response goes to the caller. That each goes where it should is trusted. A parcel that finds the inbox full is dropped. Request ids are each process's own, so a response has to be put out by an actor of the process that took the request: one put out elsewhere reaches that process's gate, which may be waiting on the same id for another client. | `Tests/Fronted.lean`: the bank on two shards joined by TCP, each behind its own front; a transfer posted to one front between accounts on different shards is answered and the credit shows through the other front, both ways; each credit is seen entering the other shard as a parcel. The test fails when parcels are not sent. It also shows the limit: a balance asked through the front of the shard that does not host the account is answered `504`. One process alone: an output that is neither a response nor a parcel comes to the caller; a process whose HTTP port is taken does not start and leaves its port for parcels free; on a journal, stopped and started, it is in the state it was in. |
| The clock adapter's handler | `Lanes/Env/Clock.lean`, 77 lines | It reads the wall clock and hands the time back as an input, never a time earlier than one it gave, nor, started on a journal, earlier than the last one in it. | `Tests/Clock.lean` checks a recorded run against `Clock.outside`, the model the checker explores, with a clock started on a journal whose last time is in the future. |
| The HTTP client adapter's handler | `Lanes/Env/HttpClient.lean`, 95 lines | It opens a socket, sends a request and reads until the answer is whole or cannot be one, or until the deadline, whichever comes first; then it closes the socket, whoever won, and hands the answer back as an input. What to send, when the answer is whole, the size limit and what the bytes mean are not its decisions: they are pure code, the next row. That a call given up on leaves no socket and no task behind rests on `close` failing the read still pending, which is `Std`'s. | `Tests/HttpClient.lean`: real calls to a real server, a closed port and a bad address, and the recorded run checked against `Client.outside`. Against servers written in the test: one that never answers is given up on at the deadline, and twenty such calls leave no more files open than before; one that sends a whole response and keeps the connection is answered at once; one that sends more than the limit is refused. A connection that never opens is not tested. |

| The HTTP wire format | `Lanes/Http/Wire.lean`, 411 lines | Pure code: the bytes of a request (`Request.wire`), and what the bytes received so far amount to (`Response.read`). The reader is tested, not proved: that it reads a response as the server meant it, and says rightly when one is whole. Of the writer this is proved, for every request and host: of the headers that frame a message only its own are written, so one `Content-Length`, one `Host`, one `Connection` and no `Transfer-Encoding` (`Request.fields_framing`); every name written is a token (`Request.fields_token`); no line of the head has a control character other than tab, so none has a CR or an LF, and the target has no blank (`Request.head_plain`, `Request.target_visible`). These are theorems about the lines; that the bytes are those lines, each ended by CRLF, is the definition of `Request.wire` and is tested. Of the reader one thing is proved: once the connection has ended it never asks for more (`Response.read_ended`), so the adapter's loop ends. | `Tests/HttpClient.lean`: requests with hostile names, values, hosts and bodies, each read back leniently and found framed once; each response the reader must refuse (two lengths that differ, a length or a status that is not digits, another version, another transfer coding, a chunk or a last chunk without its CRLF, a folded header, a blank before the colon); `1xx` skipped; for every prefix of a response, with a length or chunked, that it is whole at its last byte and not before; the size limit; 20,000 one-byte chunks in under 200 ms. || The template macro | `Lanes/Html/Syntax.lean`, 113 lines | It turns template syntax into `Html` values. What it produces is type-checked, but that it produces the element the template shows is not proved. | `Tests/Html.lean` compares rendered templates with the expected text. |

`lanes lint` fails when one of these files grows past the line count given here (rule
`trusted-size`), so trusted code cannot grow without this file changing.

What a journal file means is not in this table either. Proved in `Lanes/Actors/Journal.lean`
and `Lanes/Data/Frame.lean`: a file reads back as the entries written (`Journal.open?_file`); a
file cut at any byte opens, is never refused, and gives exactly the entries wholly written
before the cut (`Journal.open?_cut`); recovery rebuilds exactly the kernel those entries lead to
(`Journal.recover_kernel`); what is handed over again is exactly what was produced after the
last mark (`Journal.recover_handed`); a kernel restored from its image is the same system state
with the same timers (`Kernel.abs_image_kernel`, `Kernel.WellFormed.image`); a snapshot file
reads back as the kernel saved (`Journal.saved?_saved`); and starting from a snapshot gives
exactly what replaying the whole history gives (`Journal.resume_eq_recover`). Proved in
`Lanes/Actors/Disk.lean`, over a model of the two files in which an append may stop at any byte
and a rename is atomic: if the process dies at any byte of a turn's append, the files load as
the kernel that the entries wholly written lead to (`Journal.Disk.Holds.append_crash`); if it
dies anywhere in a save, they load as the kernel the shard had or, once the mark is wholly
written, the one the saved image restores (`Journal.Disk.Holds.save_crash`,
`Journal.Disk.Torn.load`); and a start mends what a death left into the files of a running
shard (`Journal.Disk.Torn.mend`), so this holds over any number of starts, saves and deaths.
A file that is not a cut journal of this system is
refused, not repaired: a frame that is all there and does not check, an intact entry the codec
cannot read, a header that names another system. Two things are not excluded. A checksum makes
it unlikely, not impossible, that a damaged entry is taken for a good one. And damage to the
length field of the last frames can look like a write that did not finish; what is cut off
then is kept in the `.cut` file, not deleted.

The runtime's decisions are not in this table: routing, start, stop, which mail a stopped
actor loses, which timer is due, how long to sleep, how much to do before looking at the inbox
again, and when the shard is idle. They are in `Lanes/Actors/Kernel.lean` and proved in
`Lanes/Actors/KernelSound.lean` and `Lanes/Actors/KernelTimers.lean`. Nor are the HTTP adapter's (which requests are waiting, when
one times out, when too many are pending): they are `Gate.step` in `Lanes/Http/Gate.lean`,
the one function behind the gate of `gated sys` and the gate of `fronted sys`, proved in
`Lanes/Http/GateSound.lean` and `Lanes/Http/FrontSound.lean` to answer each arrival at most once
and model-checked in `Tests/Gate.lean` and `Tests/Fronted.lean`.

## Assumptions the runtime makes

- **The shell passes things on unchanged.** `Kernel.exec_reachable` proves that any sequence
  of kernel operations, in any order, with any inputs, any clock readings, batches of work of
  any size and timers fired early, late, twice or never armed, leaves the kernel in a state the
  semantics can reach, and that the events it reported are a run reaching it.
  `Kernel.exec_outputs` proves the outputs it hands the shell are exactly the outputs of that
  run. The operations are the calls the shell makes (`Kernel.Op`: `input`, `advance`, `batch`),
  so the theorems are about the shell's loop as it is written, and `Kernel.exec_append` says a
  list of operations run in two parts is the same run. So no property of reachable states
  depends on the inbox, the clock or the scheduler. What is assumed is that the shell gives
  outputs to the adapter as the kernel gave them, and that an input it reports is the one that
  arrived.
- **Progress.** That a queued input is eventually handled and a pending timer eventually fires
  is not proved as a statement about time. It rests on the inbox delivering, the clock advancing
  and the shell calling the kernel again when its sleep ends, which are assumed. The kernel's
  part is proved. `Kernel.exec_wellFormed`: after any sequence of kernel operations the agenda
  holds exactly the pending timers. From that (`Kernel.WellFormed`): while a pending timer is due
  the kernel does not tell the shell to sleep (`wait_of_due`); whenever it says there is work, a
  step does some (`step_events_ne_nil`); it says to sleep until exactly the earliest pending
  deadline (`wait_for_ms`), and without limit only when no message is queued and no timer is
  pending (`wait_forever`); and it reports idle exactly then (`quiet_iff`). A timer that is due
  and a message that is queued take turns, so neither starves the other. The oldest queued
  message is delivered, or its receiver started, by the next step or the one after
  (`step_of_queued`); the exception is that the timer which went first stopped the receiver,
  whose mail the semantics drops. While a pending timer is due, a timer due no later is fired
  by the next step or the one after (`step_of_due`, `runBatch_of_due`); the exception is that
  the message which went first cancelled that timer, armed it again or stopped its actor. So a
  due timer may wait for one message, and the oldest message for one timer. No bound is proved
  for a message that is not the oldest, or from the start of a receiver to its delivery.
  Liveness theorems are stated of fair runs of the semantics (`System.Run.Fair`); that the
  runtime's runs are fair is this assumption, not a theorem. Fairness asks of a timer what the
  kernel does: one that stays pending and is not armed again fires, and one that is armed
  again starts its delay again, so a liveness theorem does not assume that a timer fires
  while its actor keeps arming it.
- **What the gate guarantees, and under what.** *At most once* is proved. In every run of
  `gated sys`, for every system, bridge and configuration, no request id is output more often
  than it was input (`Http.answered_le_arrived`). The environment may crash and restart every
  actor, the gate included, and may lose, reorder and duplicate messages on every link but
  one: the link from the outside world to the gate must not duplicate. `Kernel.env` meets
  that, so the theorem holds of the events the kernel reports
  (`Http.kernel_answered_le_arrived`). "No id is answered twice" follows when the ids that
  arrive are distinct (`Http.answered_nodup`). That they are is trusted: `Lanes/Env/Http.lean`
  allocates them. *At least once* is proved of fair runs, for a request the gate has admitted:
  in any environment that does not crash the gate, an answer to a waiting request is handed
  over, when its deadline fires if not before (`Http.pending_answered`). What is assumed is
  that the runtime's runs are fair, which is the progress assumption above, and that the gate
  does not crash, which holds on one shard. That an arrival reaches the gate is not proved.
  `Tests/Gate.lean` checks exactly once on two requests and shows each precondition is
  needed: a reused id is answered twice, a duplicating link from outside answers one arrival
  twice, and a gate that crashes leaves a request unanswered. Of `fronted sys`, the gate joined
  in front of a system that has other inputs and outputs, *at most once* is proved under the
  same assumption on the same link (`Http.fronted_answered_le_arrived`,
  `Http.kernel_fronted_answered_le_arrived`), and that deadlines stay armed
  (`Http.fronted_deadlines_armed`). *At least once* is not proved of it, only checked
  (`Tests/Fronted.lean`).
- **Durability.** Without a journal, the kernel keeps actor state in memory and it is lost with
  the process. With one, the shard returns in the state the journal describes: it survives the
  death of the process, not loss of power, since nothing is synced to disk. Outputs handed over
  shortly before the death may be handed over again. An output counts as handed over when its
  handler was called: a handler that throws is not called again for it. A journal is a list of
  requests and means what the step functions that answered them make of it: replayed through
  changed step functions it gives another state, silently, unless the application changes the
  `system` name it opens the journal under, which makes the old file refused.
- **Environment model.** One shard stays within `Kernel.env`: reliable ordered links, no
  crashes other than an actor stopping itself. Properties proved under a stronger model than
  that do not apply to a running system.
- **Unbounded queue.** The kernel's message queue has no bound of its own. The inbox is
  bounded, which limits inputs waiting to enter, but one input may cause any number of
  messages between actors, and those are not limited. Nor is what other shards send: their
  parcels are never refused for want of room, so that two shards cannot block each other, and
  a shard that falls behind its peers holds what they sent. The transport's queue to another
  process is bounded by the number of parcels, not by their size, and its queue of events is
  not bounded.

## Not trusted

Actor `step` functions, `SysState.step`, the kernel (`Kernel.run1_sound`), the model checker's
exploration of a state (`SysState.mem_successors_iff`), its search (`Check.search_sound`), what a
complete PASS of `Check.system` means (`Check.system_sound_of_respects`: for actor states whose
`==` is equality, a driver state whose `==` is an equivalence, with a matching hash, that the
driver respects, and properties that do not tell merged worlds apart; `Check.system_sound` is
the case where `==` on the driver's state is equality), what a complete PASS of a refinement
check means (`Check.refines_sound`, `Check.refines_traces`: under a monitored driver the
inputs and outputs of every run of the instance are a trace of the spec, for a spec state
whose `==` is equality),
the refinement theory and every theorem in `Lanes/` and `Examples/`: these are checked by Lean. No `sorry`, `axiom`, `unsafe`, `@[implemented_by]` or
`@[extern]` appears in them.
