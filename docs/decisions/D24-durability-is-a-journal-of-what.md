# D24. Durability is a journal of what the kernel was asked, replayed

*Departs from `DESIGN.md`, which backs `Actor.recover` with stored state.*

A shard keeps a journal: every input, every clock reading and every batch of work it asks of
the kernel, appended to a file and synced before any output of that work is handed over. After
the process dies, the shard replays the journal through the same kernel and is in the state it
was in.

Why this and not storing actor states:

- The kernel is a pure function of the requests made of it, and `step` cannot do IO, so replay
  gives the same state by construction. Other systems that replay a log have to trust that
  handlers are deterministic; here the type of `step` says so.
- A process restart is then not a crash in the semantics at all. The run simply continues, so
  everything proved for a faultless environment, such as conservation of money, still holds
  across restarts. Storing states and losing the messages in flight would have made every
  restart a crash of every actor with message loss, and most such properties false.
- Only inputs need a codec, not every actor's state.
- It is the shape replication needs: a replicated shard is a replicated journal.

What it costs:

- One sync per batch before outputs leave. Batching more inputs per sync is the lever.
- The journal grows and replay takes longer until there are snapshots. Snapshots need a codec
  for states and are the next step, together with releasing idle actors.
- Outputs produced after the last sync mark may be handed over again after a restart: outputs
  are delivered at least once, and an adapter that must not repeat itself needs to deduplicate.
- Replaying a journal with changed code gives a different state. Upgrades will go through a
  snapshot. Until then the journal's header carries a name the application chooses for the
  system and its version, and a file with another name is refused.
- Opening a journal never repairs it. A write that did not finish is cut off, because that is
  what the death of the process leaves and it is proved to be all it leaves
  (`Journal.open?_cut`). Anything else that is wrong is refused and left alone: the first
  version cut the file at the first entry it could not read, which deleted a journal that was
  opened with the wrong codec.
- Time is the kernel's time. Timers do not advance while the process is down.

What a shard does in one turn (take an input if there is one, do a batch of work, and say what
to journal) is one pure function, `Journal.turn`. A turn in which nothing happens leaves the
kernel untouched, clock included, and journals nothing, so the journal describes the kernel
exactly at every moment (`Journal.turns_kernel`), with no assumption about the clock.

`Actor.recover` keeps its meaning: it runs when an actor starts again after stopping itself or,
under an environment model with crashes, after a crash.

What is proved: nothing new is needed for the kernel. `Kernel.exec_reachable` and
`Kernel.exec_outputs` already hold for any list of requests, so they hold for the replayed one.
What has to be proved is that the file gives back the list that was written
(`Lanes/Data/Frame.lean`, and the law every `Codec` carries), including when the last write was
torn. What stays trusted is that the shell syncs before it hands outputs over.
