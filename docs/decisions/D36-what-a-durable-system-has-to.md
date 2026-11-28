# D36. What a durable system has to say for itself: a map with a codec, a journal begun on purpose, a name that covers the replay

Status: Superseded by D110-volatile-actors.md

The fifth review ran `raftNode` as three processes and found three things the framework had
left for the application to get right, and the application had not.

- *A snapshot holds values, so a map in an actor's state is the extensional one.* A `Codec`
  carries `read (write a ++ rest) = some (a, rest)`, an equality. A `Std.TreeMap` or `HashMap`
  built again from its entries holds the same and is another value, so neither can have a
  codec, and a node whose machine kept a `TreeMap` could not save: its journal only grew.
  Weakening the law to "holds the same" was the alternative, and it would have gone through
  `Journal.saved?_saved` and every theorem on it. `Std.ExtTreeMap` is equal when its contents
  are, and `Codec.extTreeMap` writes its entries in key order. Std has no
  `ofList (toList t) = t`; it is fifteen lines from `ext_getElem?`, in `Lanes/Data/Codec.lean`.
  The kernel's own hash map never needed this, because a save goes on with the restored kernel
  (D29).
- *A journal is begun on purpose.* `Journal.Store.open` begins a journal where there is none,
  which is right for a first start and for the bank. For a shard that has made promises to
  others it is a way to forget them: a mistyped path gave a Raft node that voted again. The
  store now says whether it may begin a journal (`create`, true by default), the decision is a
  pure function over the model of the files (`Disk.start`, which goes on only with what
  `Disk.read` found), and `raftNode` asks for `new` on the command line and refuses it on a
  journal that is there. A journal that is really lost is still outside the model: the
  semantics' crash keeps what an actor had.
- *The name of a journal covers everything a replay reads.* A journal records what the kernel
  was asked and the clock's readings, not what the step functions answered. A timer is due at
  the reading plus the delay the step function gave, so a replay under another timeout fires
  timers in other turns and rebuilds a node that voted otherwise. The clock readings in the
  journal do not make the timeouts irrelevant; they are what the timeouts are added to. So
  `RaftKV.journalName` holds every field of `Config`, through its `Repr`, so that a field
  added later is covered without anyone remembering, and `raftNode` adds the gate's. The cost
  is that a setting of a node that has run cannot be changed. The way out is known and not
  built: after a save the journal is one mark and the state is in the snapshot, so nothing is
  replayed, and the two files could be given a new name there.

`snapshotEvery` counts journal entries. For `raftNode` it is 65,536, with the measurements
beside it in `examples/raft-kv/Main.lean`: a save writes the whole state, Raft's log included,
so it is as rare as a journal of a few megabytes allows. A rule that saves when the journal
has outgrown the last snapshot would need no number, and is the better default.
