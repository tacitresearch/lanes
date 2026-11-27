| Adapters | `Outside`: what something outside may do, explored by the checker and tested against recorded runs of the real thing (`Outside.allows`). The HTTP server passes against the gate's assumption; a transport that joins shards in different processes by TCP, promising no more than a lossy, duplicating link (`Peers`; its decisions are a pure function, the courier, proved for every limit and every sequence of events to keep one write at a time on a connection, write only where it dialed and only what it was sent, in order and at most once, bound its queue, close everything at `stop`, leave a process alone for `retry_ms` after a break and deliver what its reader makes of the bytes of a connection, in order (`Peers.Courier.written_between`, `write_dialed`, `written_sublist_sent`, `Reachable.queue_le`, `stop_closes`, `rest_after_break`, `delivered_read`), and model-checked with a handler and a network that fails; reading the stream is proved, `Parcel.receive_send`), the two together as one process with an HTTP front and peers (`Http.serveShard`: the bank on two shards joined by TCP, each behind its own front), a clock adapter (wall time that never goes back, also across a restart) and an HTTP client adapter (HTTP/1.1, no TLS), each with model, handler and conformance test. The client's reader is proved to read back a response written as a server writes it (framed by its length, in chunks, by the end of the connection, or after interim responses) as soon as its last byte is there and not before, to keep within its size limit and to end (`Response.read_wire`, `read_wire_extract`, `read_more`, `read_some`, `read_append`); what it makes of other forms, and what it refuses, is tested. A pool of workers behind the jobs actor (`Jobs.handler`), each attempt on a task of its own, a pure function (`Jobs.compute`) or an HTTP call with the job's key in `Idempotency-Key` (`Jobs.call`), with its model (`Jobs.pool`) and a conformance test against a local service that fails twice, a closed port and a service that never answers | `Lanes/Outside/Basic.lean`, `Lanes/Env/{Clock,HttpClient,Jobs,Peers,Node}.lean`, `Lanes/Http/{Wire,WireSound}.lean` |

- No TLS, WebSockets or database adapter. The HTTP client speaks plain HTTP/1.1 to IPv4
  addresses; call past the local network through a proxy.
- Several shards run as several processes joined by TCP (`Lanes.Peers`); there is no router
  between shards in one process any more (D37), so the cores of a machine are used by running a
  process on each. That shards behave as the one system is proved for the semantics, for two
  shards (`Lanes/Runtime/ShardSound.lean`) and for any number (`Lanes/Runtime/ShardsSound.lean`),
  with an actor's shard fixed for the whole run: an actor that moves, or a `Peers.Config.home`
  that is `none`, is outside it. It is not proved for the running program, where it is still
  trusted that the runtimes and the transport implement `System.shards` with links between
  shards no better than `Link.network`.
- A boot actor that stops as it starts does not behave the same on several shards: the shards
  boot one after another, so a message another boot actor sent it may be kept where the one
  system loses it (`Tests/Split.lean`, `fragile`). The theorem assumes it away
  (`System.SteadyBoot`); invariants of actor states proved for every environment are not
  affected.
