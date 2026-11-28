# D108. Reads from the state

Status: Partly superseded by D110-volatile-actors.md (its reasons: a read no longer skips a journal's sync, and waves are gone) and by new-free-running.md (the actors of a peek read at one boundary)

`Lanes/Runtime/Batch.lean`, `Lanes/Runtime/PeekSound.lean`, `Lanes/Runtime/IO/Shell.lean`,
`Lanes/Web/Http/View.lean`, `Lanes/Web/IO/Server.lean`, `Lanes/Web/Http/Loopback.lean`,
`examples/videos/Videos/Web.lean`, `examples/videos/Videos/Proofs/Reads.lean`. This carries out
the reads of the default runtime in `docs/decisions/D96-runtime-contract.md` (issue #93, clause
2): a read is answered from the state by a peek at a batch boundary, over several actors, with a
deadline, and declared by a `view` beside the bridge. It redoes the design of the closed draft
#58 on the gate before the shard (D106). Issue #106, its sixth item.

## Why

Every request was an entry of the journal and a step of an actor, a page view as much as a like.
So every read was synced to disk, and every read touched the actor it read. D107 measured what
that costs waves: with reads journalled, the work of the video site spreads over at most about
four actors a wave, and only with reads, the feed's among them, answered from the state does it
reach seven to forty-two.

## What changed

- **A peek reads several actors at once, at the end of its batch.** `Batch.Command.peek` takes a
  list of ids, and its answer is a `Batch.Peek`: the states of those actors, read together. A peek
  no longer splits the batch where it falls: it is answered after every other act of its batch,
  with the states of the kernel the whole batch leaves. The shell puts the peeks after the other
  commands before it groups inputs, so a read never parts inputs that would be accepted together.
- **`Runtime.tryPeek`** asks for one if the inbox has room, as `tryInput` does, and hands the
  states to a task of its own; the inbox's bound is the reads' back-pressure.
- **A `View` beside the bridge.** `Http.View sys` is the actors a request reads and its response
  from their states. `serve`, `serveWith` and `serveFronted` take `view : Request → Option (View
  sys)`, none by default. A request it names, once prepared (after `arrive`, so the sign-in and
  a time stamp are done), is a read: it never enters the system.
- **A read's deadline.** A read waits behind a gate of its own: `Gate.step` over `readSig`, where
  a read enters as its id and its answer is its response, with its own bounds
  (`ServerConfig.reads`: `requestTimeout_ms`, `maxPending`). So it is answered once, `503` beyond
  its bound or when the inbox is full, and `504` when the shard has not answered by its deadline,
  as the gate answers a request. The view's response is rendered on the task that receives the
  peek, off the shard's thread. A read takes its id from the same table as every request; it
  leaves no trace in the system, so its id may be given again after a restart, as a refused
  request's may.
- **`Loopback`** answers reads the same way, from the kernel's states at the end of its next batch
  of work.
- **The video site** answers its feed, its watch pages and its channel pages so (`Web.read?`,
  `Web.view`). Its site is still one actor, so each of them reads that actor; the feed read over
  the members' states waits for the split of the site into an actor per member (#106).

## What is proved

- **The read is linearizable at its boundary.** `Batch.run_peeks`: a batch's acts are those of
  the batch without its peeks, followed by the answers, each the states, in the kernel that the
  batch's whole journal describes, of the actors it names. So a read sees every entry before the
  boundary and none after it: what a read applied as an entry there would return.
  `Batch.run_sound` adds that every output that journal produced is handed over before the answer,
  so a read never shows a state a crash could take back. Over the whole history
  (`Batch.chain`), every answer is the states of the kernel the journal before it describes
  (`Batch.chain_peek`), and a read asked after an output was handed over sees a world the
  semantics reaches by a run that put that output out first (`Batch.chain_peek_after`): a read
  asked after a write's response sees the write. The boundary falls between the read's arrival in
  the inbox and its answer, which is what linearizability asks of the read's place.
- **Leaving reads out of the journal changes nothing else.** `Batch.run_erase_peeks`: a batch with
  its peeks taken out has the same kernel, the same count, the same waiters, and the same acts
  but for the answers. The journal, the outputs and their ids (`Batch.run_ids`), and the saves are
  those of the writes alone, wherever the reads fell; replay and recovery are untouched, and the
  journal's format is unchanged.
- **The view answers what the system would.** That is the application's claim. Of the video
  site, `Videos.Web.view_answers`: for every request the view names, every id and every state, the
  bridge decodes the request as an input that leaves the site as it was, with one output, which
  the bridge encodes as the view's response from that site. With `run_peeks`, the read answered
  from the state is the answer the request would get as the next entry at that boundary, delivered
  at once. The bank's balances in `Tests/Reads.lean` have the same theorem, by `rfl`.

CSLib's `Computability/Distributed/Consistency` defines linearizability over abstract executions
with visibility and arbitration (after Burckhardt). A shard has one order of entries, so the
claim is stated over the journal directly; using it would add a translation and no strength, and
runtime modules import `Std` only (rule 1.6).

## Trusted

`TRUSTED.md`, the shell's row and the server's: that the shell performs an answer as the batch
gives it, that the server never hands a read to the shard as an input, that it does what the gate
of reads decides under the same lock as the gate's, and that it answers a read from the peek of
the actors its view names. `Http.Front.World` (D106) does not model reads.

## Costs and limits

- **A read waits for the batch in progress**, and for the journal's sync of it: it is answered
  once what was taken before it is durable and handed over. Batches are bounded
  (`Runtime.Config.batch`), and its deadline bounds the wait.
- **States are shared with the reading task.** The peek hands the actor's state itself, not a
  copy; an actor stepped before the task lets go of it starts from a copy (D84's in-place step is
  lost for that step). The view's work is the reading task's, not the shard's.
- **A boundary is not a quiet point.** A batch can end with messages still queued between actors
  (`Kernel.runBatch` is bounded by fuel), so a read over several actors sees each at the same
  boundary, which may be inside a protocol between them. An application whose view needs a
  quiet state says so in its view's claim; the bank's transfers end within their turn.
- **Reads have no order among themselves beyond their boundaries**: two reads of one connection
  are answered in the connection's order, as every response is (`Conn.step`), each from the
  boundary of the batch that took it.

## What remains

- The feed read from the members' states, once videos is split into an actor per member (#106);
  `Videos.Site.deleted_never_served` then becomes a claim about reads at batch boundaries.
- A benchmark of reads from the state against journalled reads on the warm runner.
- Reads in `Http.Front.World`, so that the server's model covers them.
