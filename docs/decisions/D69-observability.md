# D69. The server tells its operators how it is, and nothing it tells enters a system

An application deployed behind a load balancer needs three things the framework did not have:
metrics a Prometheus server or the CloudWatch agent can scrape, a liveness and a readiness check
the load balancer can ask, and an access log. This decision adds all three to the HTTP server,
each off by default (`ServerConfig.ops`, an `OpsConfig`), and keeps them out of every system.

## Where it is

- `Lanes/Lib/Metrics.lean`, pure and `Std` only: counters, gauges and fixed-bucket histograms as
  values, and the Prometheus text exposition format, version 0.0.4. A value is a natural number
  written with `Family.scale` decimal places, so a latency kept in microseconds is written in
  seconds with no floating point. A histogram keeps, for each bound, the observations at or below
  it, which is what the format writes, so its buckets are cumulative by construction.
- `Lanes/Web/Http/Ops.lean`, pure: which request is the operators' (`Ops.route?`), what each
  answers (`Ops.answer`), the server's counts (`Ops.Stats`) and their metrics (`Ops.families`), a
  request id taken from the client or made (`Ops.RequestId`), and a line of the access log
  (`Ops.Access`).
- `Lanes/Web/IO/Ops.lean`, trusted: a reference holding the counts, the clock readings, the
  random bytes of a new id, and the write of a log line. It decides nothing.
- The server is changed in four places: one field of `ServerConfig`; `submit`, the function a
  connection hands each request to, is wrapped by `Ops.front`; the journal's storage is wrapped by
  `Ops.journal`; a connection closed at `connections_max` is counted. `Server.drain` is new. The
  shell gains two readers, `Runtime.hasRecovered` and `Runtime.depth`; neither changes what its
  loop does.

## It does not change what a system does

Observability must not enter a step function, the kernel or the journal. With metrics, health
and the log on, a run writes the same journal as one with them off. Four facts give this.

1. **An operator's request never reaches the shard.** `Ops.front` answers it before the request
   is prepared, before `Http.Waiting` hands it an id and before the inbox sees it. So a probe takes
   no id, leaves no entry, and is answered while the shard is busy, recovering or gone.
2. **Any other request goes on as it came.** The request id is added to the response, never to
   the request. A client's `X-Request-Id` is in the request as it was sent, as it is with
   observability off.
3. **The journal's storage is given what it was given.** `Ops.journal` calls the storage's
   `append` and `save` with the same entries and images, and counts after they return.
4. **With nothing configured nothing is wrapped.** `Ops.front` returns `submit` and `Ops.journal`
   returns the storage when `OpsConfig.active` and `OpsConfig.counting` are false, and no path is
   the operators' (`Ops.route?_default`).

`Tests/Ops.lean` sends the same requests to two servers, one with everything off and one with
everything on and probed between requests, and compares the inputs their journals hold: they are
the same. The journals are not compared byte for byte, because a journal holds the clock's
readings (`Journal.Entry.advance`), which differ between any two runs.

What does change is on the wire: with `requestIds` every response carries an `x-request-id`
header, replacing one the application set (`Ops.RequestId.header_tag`).

## Metrics

`lanes_http_requests_total` by `method` and `status_class` (`2xx`, `5xx`);
`lanes_http_request_duration_seconds`, a histogram from 1 ms to 10 s; the gauges
`lanes_http_requests_in_flight`, `lanes_http_connections`, `lanes_runtime_inbox_depth` and
`lanes_ready`; and the counters `lanes_http_connections_refused_total`,
`lanes_journal_appends_total`, `lanes_journal_entries_total` and `lanes_journal_saves_total`.

- No label takes a path or a full status. A path is unbounded, and a label with unbounded values
  is a series per value in the scraper. An application that wants a route's latency counts it in
  its own adapter.
- Latency runs from the request read to its answer handed to its connection. It leaves out
  reading the request and writing the response, and it includes the shard's queue, the journal's
  sync and the gate.
- Counts live in the process and start at zero when it starts. A scraper's `rate` takes the reset
  as a reset.
- Counts are kept only with a metrics page configured. A request then costs one update of a
  shared reference and two readings of the monotonic clock.
- A refusal the connection makes itself (`400`, `408`, `413`, `431`, `501`) never reaches
  `submit`, so it is neither counted nor logged. The `503` of a full inbox is both.

## Health

Liveness answers `200` whenever the server answers at all. Readiness answers `200` exactly when
the shard has recovered and the server is not stopping (`Ops.answer_ready`). The shard has
recovered once it has replayed its journal and handed over what the journal owed; until then a
request waits in the inbox and readiness answers `503`. That the server is listening holds
whenever anyone can ask. Stopping is `Server.drain`, `Server.stop`, or a shard that ended on an
error. A deployment calls `drain` when told to stop, waits for the load balancer to take the
target out (its deregistration delay), then calls `stop`, which closes the listener. Neither
check enters the application's actors, so a shard stuck in a long step still answers liveness.

## The access log

One JSON object per line, written by `Json.compress`, with the fields in a fixed order as Go's
`slog` writes them: `time` (RFC 3339, UTC, milliseconds), `method`, `path`, `status`,
`duration_ms`, `bytes` (of the response's body) and `request_id`. A line is the JSON text of its
record (`Ops.Access.parse_line`).

Never logged: a request's or response's body, its query string, and every header but the request
id, so neither `Authorization` nor `Cookie` nor `Set-Cookie`. The path is written as segments
percent-encoded again, so a decoded line feed or quote is `%0A` or `%22`. The one value a client
chooses that reaches the log is its request id, and only when it is at most `requestIdMax`
characters of letters, digits and `-._` (`Ops.RequestId.accept?_eq_some`); otherwise the server
makes one from eight random bytes, sixteen hexadecimal digits (`Ops.RequestId.accept?_ofBytes`).

The sink is `off`, `stderr` or a function. On `stderr` a line is one write. A function is called
from the connections' threads, several at once, so it must be safe to call that way. A slow sink
slows the requests it logs, since a line is written before its response is handed on.

## Alternatives

- **Metrics as an actor of the system.** Counting in a step would put every count in the journal
  and make a scrape an input, which is what the decision rules out.
- **Counting in the shell's acts.** `Batch.run` could return an act per append. Wrapping the
  journal's storage counts the same without changing the shell's loop or `Batch`.
- **A separate port for the operators' endpoints.** It keeps the metrics page off the public
  listener; it is a second listener in trusted code. Today the paths are opt-in on the one port,
  and a load balancer's rules keep `/metrics` from the internet.
- **OpenTelemetry.** OTLP needs protobuf and an HTTP client with TLS; the text format is scraped
  by Prometheus, by Amazon Managed Service for Prometheus and by the CloudWatch agent.

Not done: the text format is not yet tested against Go's `expfmt` parser, which `docs/STDLIB.md`
names as its oracle; it is tested against text checked by hand.
