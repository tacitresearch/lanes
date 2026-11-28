# D29. A snapshot is a restart without the crash

Status: Superseded by new-volatile-actors.md

`Lanes/Runtime/Kernel.lean`, `Lanes/Durable/Journal.lean`, `Lanes/Durable/Snapshot.lean`, `Lanes/Durable/Disk.lean`, `Lanes/Durable/IO/Journal.lean`. A journal that only
grows makes a restart take as long as the shard has lived. A snapshot saves the kernel, and the
journal is cut at the point of the save.

- *Saving is a kernel operation.* A kernel has an image (`Kernel.image`: cells, queue, agenda,
  clock) and can be restored from it. The restored kernel is the same system state
  (`Kernel.abs_image_kernel`) and has the same timers on its agenda (`WellFormed.image`), so
  every kernel theorem covers it. It is not the same value, because a hash map built again is
  laid out differently. The usual way out is a theorem that kernels alike in everything
  observable behave alike, which is a congruence lemma for every kernel function. Instead the
  operation `snapshot` replaces the kernel by the one its image restores, and the shard goes
  on with that. The shard that keeps running and a shard started from the saved image then
  hold equal values, and equality needs no theorem. The cost is rebuilding the tables at each
  save, which is of the order of writing them. The gain besides the proof: recovery is
  exercised at every save, in production, and not only after a crash.
- *The snapshot is a memo of the replay.* The journal marks a save with an entry that carries
  its index in the shard's history. `Journal.resume` starts from a saved kernel and the entries
  after its mark. `Journal.resume_eq_recover`: that gives exactly what replaying the whole
  history from boot gives, kernel and outputs to hand over again, however many entries before
  the mark the file has lost. So everything that was true of recovery by replay stays true, and
  cutting the journal is justified by a theorem about lists.
- *What is refused.* A cut journal whose snapshot is gone, or a snapshot whose mark is not in
  the journal, does not start: replaying a cut journal from boot would give a state that never
  was. A snapshot is written whole and renamed into place, so one that does not read back
  entirely is refused, not repaired (`Journal.saved?`).
- *The order of a save* is: mark the journal, put the snapshot in place, replace the journal by
  one that starts at the mark. It is a pure function, `Journal.saveWrites`, over a model of the
  two files (`Lanes/Durable/Disk.lean`): a journal that is appended to, where the death of the
  process leaves any number of the first bytes of the append, and files that are replaced
  whole. What a start computes from the files is `Disk.load`: `open?`, `saved?`, `resume`.
  `Disk.Holds.save_crash`: if the process dies at any byte of the mark or between any two of
  the three writes, the files load as the kernel the shard had or, once the mark is wholly
  written, as the kernel the saved image restores, which is the one the shard goes on with.
  Never a refusal, never another kernel. `Disk.Holds.append_crash` says the same of a turn's
  append: the entries wholly written, and no others. `Disk.Holds` is what the files of a
  running shard are, and `Disk.Torn` what its death may make of them. A start mends the second
  into the first (`Disk.Torn.mend`) and a finished turn or save keeps the first, so the
  theorems hold over any number of starts, saves and deaths. The adapter runs the list of
  writes and decides nothing about them. A new journal's header and the cut of a write that
  did not finish are writes of the same kind (`Disk.mend`), so the adapter has two ways to
  write and no other: append and flush, or write beside and rename. What stays trusted is that
  the model is the operating system: a rename is atomic, bytes flushed survive the process, an
  append that did not finish leaves some of its first bytes. There is no `fsync` in Lean's
  `IO`, so loss of power is not covered. The model is also run on the compiled code at every
  cut. That test fails when the last two writes are swapped, which the states built by hand on
  real files cannot notice, since they are built in the right order.
- *Request ids after a cut.* The HTTP server used to find a fresh id by reading every input in
  the journal, which a cut journal no longer holds. Ids now start at the number of entries in
  the shard's history, which a cut does not lower, and go up by one per request the shard
  admits, in the order of admission. Every request that leaves a trace has an entry of its own,
  so the history at the next start is longer than the last such id. A request the shard refuses
  takes no id.
- *What an application gives.* Three codecs (`Kernel.Image.Codecs`): an identity, each actor's
  state, each actor's messages. `Codec.sigma` puts them together, and `Codec.struct%` and
  `Codec.sum%` write each in a line. `Http.gatedActors` adds the gate's own.

Not done: actors that are idle are still kept in memory, and upgrading the step functions
across a snapshot has no story yet beyond the `system` name that refuses the old files.
