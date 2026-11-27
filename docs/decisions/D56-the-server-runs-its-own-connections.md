# D56. The server runs its own connections, and a pure function decides for each

The server read requests with `Std.Http.Server`: code of the standard library that Lanes
trusted without having written it, which framed requests by rules of its own and closed a
connection after a hundred requests. `docs/decisions/D49-the-server-reads-requests-by-a-strict-profile.md`
gave the server a reader of its own, proved; this decision puts it to work. The server now
accepts connections on `Std.Net` (TCP over libuv, as `Lanes.Peers` and the HTTP client do) and
runs a loop for each, and `Std.Http` is no longer imported anywhere in Lanes.

The loop decides nothing (D26, D40). Each connection is a value of `Http.Conn`, and
`Conn.step cfg now_ms c e` takes what happened (`Conn.Event`: bytes received, the end of them,
a socket that failed, the system's answer to the request numbered `seq`, a tick, `stop`) and
answers with the next value and what to do (`Conn.Action`: hand a request to the system, write
an interim or a final response, close). The loop asks it three things more: whether to read the
socket (`Conn.wantsInput`), how many bytes at most (`Conn.room`), and until when to wait
(`Conn.deadline`). How many connections are open is `Conn.Count`.

## What `Conn.step` decides

- **What the bytes are.** They go in one buffer; the request at `pos` is read by
  `Request.read`, and after it the next from where it stopped, so pipelined requests are read in
  turn. Consumed bytes are dropped when more arrive, not after each request. A body framed
  by its length is not read again until all of it can be there (`need`), so a body that arrives
  in many pieces costs one reading of its head per piece, not a reading of all of it.
- **Order.** Each request read gets the next number. Responses are written in the order of the
  numbers, each once, however the system answers: an answer waits in its slot until every
  earlier one is written. A refusal and a timeout take a number too and go out in turn.
- **Bounds.** No more than `inflight_max` requests are in flight on a connection; while there
  are that many, nothing more is read and no deadline runs. The buffer holds at most
  `message_max` bytes: the loop is asked for no more than `room`, and more than that closes the
  connection at once. `Request.read_more` says the reader never waits on that many, so a
  connection is never stuck on a full buffer.
- **Deadlines.** A connection with nothing in flight is closed after `idle_ms`. A head must be
  whole within `head_ms` of when the connection began to wait for it, and a body within
  `body_ms` of the end of its head; otherwise the connection answers `408` after what it owes
  and closes.
- **`100 Continue`** is written for an HTTP/1.1 head with `Expect: 100-continue` whose body has
  not all arrived, once every earlier response is written, before its own.
- **Closing.** After a refusal, a request that asks to close (or HTTP/1.0), the end of the
  client's bytes, a deadline or `stop`, nothing more is read; the responses still owed are
  written, then the connection closes. A socket that fails closes at once. A closed connection
  does nothing more.
- **What is written.** A response is written by `Response.wire`, `HEAD` by its head with the
  length of the body. Headers the client's reader would not keep, `Content-Length` and
  `Transfer-Encoding` among them, are left out; `Connection: close` is added to the last
  response; a response that cannot be written so (a status outside 200 to 999, a body for a 204
  or a 304) becomes a bare `500`.

## What is proved and what is checked

Proved for every configuration and every sequence of events (`Lanes/Http/ConnSound.lean`, on the
standard axioms, `Tests/Axioms/Http.lean`): the writes of a run are of the requests numbered
`written, written + 1, …`, none left out and none twice (`Conn.run_writes`); requests are handed
on in increasing order (`Conn.run_submits`); every request handed on is one `Request.read` reads
in the connection's bytes (`Conn.step_submit_read`); an answer to a request not waiting changes
nothing, and one to a request waiting is what is written for it (`Conn.answer_ignored`,
`Conn.answer_waiting`); the buffer stays within `message_max` and the requests in flight within
`inflight_max` (`Conn.run_buffer`, `Conn.run_slots`); a closed connection does nothing, one that
stopped reading takes no bytes and never reads again, and a deadline that has passed stops the
reading (`Conn.step_closed`, `step_notReading`, `step_reading`, `step_tick`); the loop is asked
to read only an open connection that reads, for at least one byte (`Conn.wantsInput_room`);
what is written for a response is read back by the client's reader as that response
(`Conn.read_encode`, from `Response.read_wire`); and no more connections are taken than the
bound, none while stopping (`Conn.Count.admit_le`, `Count.admit_stopping`).

Model-checked first (rule 5.1, `Tests/HttpConn.lean`), against a client that sends pipelined
requests in pieces of one, nine or all the bytes, leaves at any moment, and a system that
answers in any order, twice, and numbers nobody asked, with time passing and `stop` at any
moment, on two streams (one with a `100 Continue` and a `HEAD` that closes, one with a request
refused between others) and limits small enough that the room and the bound on requests in
flight both come into play: on top of the properties above, the requests handed on are exactly
those the reader reads in turn from the whole stream, whatever the pieces; each response written
is the system's first answer to its request or the refusal or timeout last; `100 Continue` goes
between the earlier responses and its own; the connection closes once and writes nothing after;
and once the client has sent everything and the system has answered every request, every
response is on the wire and the connection closed. The search found no counterexample; it was
written before the proofs and run on every change of `Conn`.

`Tests/Web.lean` runs the loop over real sockets: pipelined requests in one write, a request in
pieces, a hundred and one on one connection, a refusal followed by 200 KB still answered `400`
rather than reset, `408` for a slow head, an idle connection closed, one beyond the bound closed,
and `stop` closing a connection kept open.

## Departures

- An unknown method is answered `501`, as the reader decides (D49), not `405`.
- No `Date` header is written. RFC 9110, 6.6.1 asks an origin server with a clock for one; the
  bytes of a response are then a function of the response alone, which is what the proofs
  about them use. A proxy in front can add it.
- An expectation other than `100-continue` is ignored, not answered `417`.
- A connection beyond `connections_max` is closed as soon as it is accepted, without a
  response: the client sees the connection end (or reset, as its request is unread).
- There is no bound on the requests one connection may make in all; `Std.Http` closed a
  connection after a hundred.

## Trusted

What remains trusted is the loop in `Lanes/Env/Http.lean`, the IO that performs: that it tells
each connection what happened when it happened, reads only when asked and no more than asked,
does the actions in order, gives each answer to the connection and number it was asked under,
writes within `write_ms` or reports the socket broken, and on a close sends what was written,
then reads and drops what the client still sends for `linger_ms` before closing, so that a
client that pipelined more than was read gets its last response rather than a reset. And
`Std.Net`, the selection of `Std.Async` and libuv, as before. `Std.Http` leaves the list.

## Measured

Requests per second for a system that answers every request `ok`, from a Go client that sends
`GET /` on keep-alive connections and reads each response before the next, five seconds a run,
median of three, the two servers one after the other on a shared machine of four cores under a
load average of 7.5 to 11:

| Connections | `Std.Http.Server` | This loop |
| --- | --- | --- |
| 1 | 853 | 3,430 |
| 16 | 4,001 | 11,592 |
| 64 | 4,010 | 10,114 |

The machine was loaded by other work and the runs vary by a third; an hour earlier, under a load
of 15, the medians were 2,225, 6,000 and 6,252 against 3,483, 10,725 and 11,333. `Std.Http`
closes a connection after a hundred requests, so its client connects again about every hundred;
the loop keeps it.

## Known limits

- The head of a request is read again from its start each time bytes arrive until it is whole,
  so a head sent a byte at a time costs time quadratic in its length, within `head_max` and
  `head_ms`; a chunked body likewise within `body_max` and `body_ms`.
- The write deadline is the loop's, not `Conn`'s: a write that does not finish within
  `write_ms` is reported as a broken socket.
