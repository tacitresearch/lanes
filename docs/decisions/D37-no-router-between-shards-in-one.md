# D37. No router between shards in one process

Status: Superseded by new-volatile-actors.md

`Lanes/Actors/Cluster.lean` (removed) is deleted. It started a runtime per shard in one process and
carried parcels between them on a lane of the inbox that was never full. It came before the
transport between processes (D30) and was never given a journal; its 106 lines were trusted,
and what it did, the transport does with its decisions proved and model-checked and with
journals. A machine's cores are used by running a process per core, joined by the transport
on the loopback interface, which costs a copy and a system call per parcel and needs nothing
more to be trusted. If one process with several shards is wanted again, it should be the
transport's courier over an in-memory link, not a second router.

The inbox's lane that was never refused (`Mailbox.urge`, `Runtime.peer`) was there for it,
and has gone too: the transport hands a parcel to `tryInput`, which may refuse it, as
`Link.network` allows. The inbox is one bounded lane, and `Mailbox.batch_since_take` says a
take returns what it took in since the last, in order.
