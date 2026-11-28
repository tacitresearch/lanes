# D30. Shards in different processes are joined by a link that promises little

Status: Superseded by new-volatile-actors.md

`Lanes/Net/IO/Peers.lean`, `Lanes/Runtime/Shard.lean` (`Parcel`). A process runs `System.shard` on
the ordinary runtime. A parcel its shard puts out is framed and sent over TCP to the process
that hosts the receiver; a parcel that arrives is an input.

- *The promise is `Link.network`, on purpose.* The adapter never blocks the shard: a parcel is
  queued, and dropped when the queue is full, when the other process cannot be reached, or
  when the receiving shard's inbox is full. A shard started again from its journal hands over
  again the outputs it had not marked, so a parcel may also arrive twice. Making the link
  reliable would mean acknowledgements, retransmission and deduplication in trusted IO, and
  any system that runs on several machines has to survive loss and duplication anyway, since a
  machine can fail. So the adapter stays small, and the system's checks and proofs are the
  place where loss is dealt with: they assume `Link.network` between shards.
- *The decisions are a pure function, the courier* (`Lanes/Net/Courier.lean`). The first
  version kept its queues, its reconnecting and its idea of `stop` in IO, and the first system
  run on it found the bug there: a stopped shard kept its accepted connections, so the others
  went on sending to nobody. The transport is now `Courier.step`: the handler reports events
  (a parcel to send, connected, written, broken, accepted, received, stop) and performs the
  actions it gets back (dial, write, close, adopt, refuse, deliver). The model checker runs
  the courier against a network that fails at any moment, 49,000 states, and checks: one
  write at a time on a connection, writes started in the order asked and none twice, a
  bounded queue, nothing lost unless a connection failed or the queue was full, nothing open
  after `stop`. It also refuted a claim: parcels are not delivered in the order sent, because
  a write on a connection that then fails may still go out while the next parcel takes a new
  connection. The link is unordered, which is what `Link.network` says.
- *Reading the stream is pure.* `Parcel.receive` takes what has arrived so far and gives the
  parcels wholly received and the bytes they took. `Parcel.receive_send`: a stream cut at any
  byte reads as exactly the parcels sent before the cut. The IO loop appends, calls it and
  delivers.
- *Durability needs nothing new.* A parcel that arrives is an input of the shard's system, so
  it is journaled like any input, and a shard with a journal comes back with what it had
  received.
- *Not there:* authentication and encryption (listen only where every sender is trusted);
  back-pressure between processes; the statement that processes joined this way implement the
  split system (`D28` proves the model for two shards; that the runtimes and this adapter are
  that model, over a lossy link, is trusted).
