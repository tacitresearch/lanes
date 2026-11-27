# D76. Bodies and responses stream through the gate, in pieces and parts, one at a time

A body had to fit `message_max`, and a response was one value: an upload larger than
`body_max` was refused, and rookery's timelines polled every five seconds
(`examples/rookery/README.md`, friction log 6). This decision lets a request's body reach the
system in bounded pieces and a response leave it in bounded parts, Server-Sent Events among them,
with `Conn.step` still pure and still the one that decides.

## Which requests stream

`ServerConfig.streams` (`Conn.Config.streams`) says, of a head with its body left out, whether
the request streams. One that does is handed to the system by its head alone (`Conn.Action.begin`,
answered by `Conn.Event.responded`), through the gate as any request, and gets an id there. Its
body, if it has one, follows in pieces; and the answer to its head may open a streamed response.
A request that does not stream is read and answered as before: `Request.read`, the strict reader,
with `body_max`. A body that streams may be framed by its length or in chunks, and is bounded by
`streamBody_max` instead (`413` beyond).

## Pieces and parts are requests of their own, through the gate

Each piece of a body, and each call for the next part of a response (a pull), is handed to the
system as a request of its own (`Stream.piece`, `Stream.pull`), which repeats the head and carries
headers whose names are not tokens: `:stream`, `:index`, `:after`, and `:head`, the id the head
entered with, which the server adds (`Stream.tag`). No request read from a client has such a
name. The system's bridge reads them with `Stream.msg?`.

Three other ways were weighed:

- **Pieces as inputs around the gate**, through `fronted sys`'s inputs that are no request. The
  head goes outside → gate → system, two hops, and a piece outside → system, one, so on one
  shard a piece reaches the system before its head. Through the gate, all take the same path, in
  the order they were handed on.
- **Parts as outputs around the gate**, pushed by the system for a connection to write. They
  would race the head, which goes through the gate, and the connection would hold what the
  system pushes faster than the client reads: a queue whose bound is the connection's, and whose
  overflow loses what the system said it sent. With pulls, the connection asks for the next part
  only once what it wrote has been sent, so a slow client slows the pulls, and what waits is the
  system's, bounded by the system's own state and spec.
- **A new message of the gate** for pieces and parts. It changes `gateSig`, `served` and every
  theorem of `Lanes/Web/Http/FrontSound.lean` and `Lanes/Semantics/Front.lean`. As requests, the
  gate is unchanged, and so is all that is proved of it: each piece and each pull has an id, is
  answered at most once, has a deadline and counts toward `maxPending`.

A piece or a pull is journalled like any request: an upload is in the journal, in its pieces.

## What the connection decides

- **One piece at a time.** A piece is taken from the buffer (`Inflow.gather`, at most
  `piece_max` bytes, across chunks) only once the system has taken the one before. While it is
  with the system, nothing more is taken, the buffer fills to `message_max`, the loop stops
  reading the socket (`Conn.wantsInput`), and the client's TCP window closes: back-pressure from
  the system to the client (rule 3.8). An answer of `503` (the gate's `maxPending` or the inbox
  full) offers the same piece again after `poll_ms`; another status of 300 or more refuses the
  rest of the body, and the connection closes after the head's response. An answer to the head
  before the last piece ends the body too. `100 Continue` is written before the first piece when
  the head asks for it and every earlier response is written. Each piece must arrive within
  `body_ms` of the one before being taken; while one is with the system, no deadline runs.
- **One pull at a time.** The answer to a head that opens a stream (`Transfer-Encoding: chunked`
  among its headers, and `Content-Type: text/event-stream` for events; `Response.stream`,
  `Response.events`) is written as the head of a chunked response once every earlier response is
  written. Then the connection pulls; each pull's answer is the next part (`Response.part`),
  nothing yet (`Response.nothing`, or `503` or `504`: pull again after `poll_ms`), or the end
  (`204`, `Response.finished`: the last chunk is written). A status of 300 or more, or a part
  larger than `part_max`, cuts the response short: the connection closes without the last chunk,
  so the client sees a body cut short. The next pull is made only once everything written has
  been sent (`Conn.Event.sent`, which the loop tells when its last write ends): what one
  connection holds of a stream is at most one part.
- **Events.** A part of a stream of events is the event `Sse.Event.ofResponse` makes of the
  answer: its body the data, its headers `event`, `event-id` and `retry` the other fields, line
  breaks as LF. The first pull carries the head's `Last-Event-ID` as `:after`, each later pull the
  id of the last event written, so a system answers "the events after this one" from its own
  state, and a client that reconnects resumes. An event with the id of the last one written is not
  written again, so a system can answer a pull from what it shows without remembering what it
  sent: rookery answers with the timeline, and its id is a hash of the posts in it. A comment
  (`:`) is written when nothing has been for `heartbeat_ms`.
- **Ends.** At `stop` or when the client ends its side, a stream of events ends with its last
  chunk, a stream of bytes is cut short, and a body that streams is no longer handed on.

Every bound is in `Conn.Config` and `ServerConfig` (rule 2.6): `piece_max` (64 KiB),
`streamBody_max` (1 TiB), `part_max` (1 MiB), `poll_ms` (1000), `heartbeat_ms` (15000), with
`message_max`, `inflight_max` and `body_ms` as before.

## What is proved, checked and trusted

Proved (`Lanes/Web/Http/ConnSound.lean`, `Lanes/Web/Http/SseSound.lean`), for every configuration:
every theorem of `docs/decisions/D57-the-server-runs-its-own-connections.md` with its statement
unchanged, through the new events and actions (`Conn.run_submits` now counts heads that stream
among the requests handed on in order); the bytes of a streamed response, its head, the chunk of
each part and its last chunk, are `Response.wireChunked`, which the client's reader reads back as
the head with the parts, in order, as its body (`Conn.read_streamed`); an answer that opens a
stream makes the head the first thing it writes (`Conn.respond_opens`), a part given for the pull
a stream waits for is to be written as its chunk after what came before (`Conn.pulled_part`),
any other answer changes nothing (`Conn.pulled_ignored`, `Conn.respond_ignored`), a part larger
than `part_max` cuts the stream (`Conn.pulled_large`); a stream writes only at the front, what
has come and then its last chunk (`Conn.flushStream_ended`), and pulls only when nothing written
is unsent and no pull is out (`Conn.flushStream_going`); a piece handed on is what
`Inflow.gather` reads at the connection's position in its buffer, or the one the system was too
busy for, offered again (`Conn.pump_piece`), and of a body framed by its length a piece is the bytes
from the connection's position, within what is left, the last exactly when nothing is left
(`Conn.gather_length`), so such pieces in turn are the bytes the strict reader takes; the client's reader of events reads back the events a
stream writes, in order, each once, whatever comments are between them (`Sse.parse_written`), and
an event made from an answer is one it reads back as it is (`Sse.Event.ofResponse_valid`).

Model-checked first and on every change (`Tests/HttpStream.lean`, in `lanesCheck`; rule 5.1),
against a client that sends in pieces of two bytes or all, and a system that answers heads,
pieces and pulls in any order, is too busy for a piece once, answers a pull with nothing, with an
event already sent, with a part or with the end, with time passing, sends acknowledged at any
moment and `stop` at any moment, on a body framed by its length and one in chunks, each followed
by a pipelined request, a download and a stream of events: the pieces the system takes make up
the body the strict reader reads, in order, all of it once the last is taken; the bytes written
for a streamed response are its head and the chunks of the parts given, which the client's
reader reads back with the parts as its body once it ends; events are read back as given, each
once; one piece and one pull at a time, none while something written is unsent; and the bounds,
the order of responses and closing once, as before.

Not proved: that the pieces of a whole run make up the body the strict reader would read (for a
body in chunks, `Inflow.gather` is not related to `Request.chunks` by a theorem), and
that the bytes written for a stream over a whole run are exactly the parts the system gave: the
theorems above are of each step, and the whole run is model-checked, not proved.

Trusted, in `Lanes/Web/IO/Server.lean`: that the loop gives each answer to a piece or a pull to
the number and index it was asked under, tags each with its head's id, and tells the connection
`sent` when its last write ends. In `Lanes/Web/IO/Client.lean`: `Client.events`, which reads a
stream of events for tests until enough have come or its deadline.

## Tested

`examples/upload` takes uploads of any size and answers each with its size and Adler-32
checksum; `curl -T` of 20 MB, framed by its length (after `100 Continue`) and in chunks, is
answered in 0.3 s with zlib's checksum. `Tests/Web.lean` over sockets, on 0 and 2 IO threads: an
upload of 1 MB framed by its length and one in chunks, a streamed response, one that has nothing
at first, a stream of events and one resumed with `Last-Event-ID`, a client that gives up on a
stream that never ends, and `stop` with a stream open. `Tests/Loopback.lean` the same with no
socket. rookery's timeline is a stream of events (`rookeryLive`).

## Known limits

- A response streams to an HTTP/1.0 client in chunks, which it does not read.
- A body that streams is no longer handed on once the client ends its side, though bytes of it may
  still be in the buffer.
- A system that answers pulls from what it shows is asked again every `poll_ms` while nothing
  changes: in-process polling, which a system that holds the pull until it has something avoids.
- A chunked body costs one gate request for each piece of up to `piece_max` bytes; tiny chunks
  are gathered into pieces, but each chunk's size line is read again until its data is there.
