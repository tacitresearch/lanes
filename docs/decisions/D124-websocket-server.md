# D124. WebSockets behind the gate

Status: Accepted

`docs/decisions/D122-stdlib-wave-2.md` added WebSockets as data: the handshake, the frame codec
and `WebSocket.Conn`, a server's side of a connection, all pure. It left the server out and
proposed a default: a request the application marks gets a `101`, its frames become a stream
like the streamed bodies (`Http.Stream`), messages enter the system as inputs keyed by the
request's id, and sends leave as outputs, reusing the streaming path. This decision connects the
protocol to the server (#219, part of #234). It keeps that default but for one part, how sends
leave.

## What an application sees

A request `WebSocket.Server.wants` opens a socket. The server checks its handshake
(`WebSocket.Server.bridge`, `400` or `426` before the system sees it) and hands its head to the
system, which answers it `WebSocket.accept`; any other answer refuses it. From then on the
socket is known by the id its head entered with:

- each message received is a request to the system through the gate (`WebSocket.Msg.message`),
  repeating the head, so routes, cookies and `prepare` apply to it as to the head. The system
  answers it `Response.taken`, and the next message is handed on only then. `503` offers it
  again after `poll_ms`; a `4xx` closes the socket `1008`, any other refusal `1011`.
- the system sends with outputs that answer the socket's id: `WebSocket.text`, `binary` and
  `close`. So a `Service` whose outputs are `(ReqId × Response)` can push without a new output
  type.
- when the socket ends, however it ends, the system is told once (`WebSocket.Msg.closed`), with
  the close code, and answers it as it answers a message.

`examples/chat` is a room built this way, and `Tests/WebSocket.lean` serves one to a client
written in the test and to Python's `websockets` client.

## Sends are outputs to the socket's id, not answers to pulls

Reusing the streaming path for sends would make each send the answer to a pull (`Stream.pull`):
the connection asks the system for the next message, and the system holds the pull until it has
one. That is wrong for a socket in three ways. A pull held past the gate's `requestTimeout_ms` is
answered `504` by the gate, and the system's later answer to it is dropped (`Gate.receive`), so a
message sent just after a deadline is lost while the socket is fine, unless every application
answers its pulls on a timer of its own. A held pull is a pending request for the socket's whole
life, so `GateConfig.maxPending` would bound the open sockets rather than the requests waiting.
And between an answer and the next pull a send waits, or is polled for every `poll_ms`. A
socket's sends are driven by the server's side; a pull models a client asking.

So a send is an output that answers the socket's id. The gate has answered that id already (the
`101`), so it would drop such an output; the server takes it to the socket instead
(`Gate.receive_absent`: an answer to an id the gate is not waiting on leaves the gate as it was
and does nothing). The gate is unchanged, so its theorems and its bound hold as they are, and
the proof that the server's front with the shard is a run of `served sys`
(`Lanes/Web/Http/AdmitSound.lean`) is untouched: messages still enter only as admitted requests,
under ids from `Http.Waiting`, and a send is an output `served sys` hides.

The server registers a socket under its id when the gate hands the `101` to the connection, on
the shard's output thread, before the shard's next output is read. An application that answers
the head and sends to the socket in the same step therefore never loses the send to a race with
the handover.

## How a socket counts

An open socket is a connection: it counts against `ServerConfig.connections_max` until it
closes. Against the gate it holds at most one place, and only while one of its requests is with
the system: the session hands the system at most one request in a step, and none while one is
with it but on that one's answer (`WebSocket.Session.step_submits`, `step_withSystem`). An idle
socket holds none. A system too busy for a message answers `503` or is answered `503` by the
gate; the session waits and offers it again, and reads nothing more meanwhile once a message is
waiting behind it, so back-pressure reaches the client's TCP window.

## A protocol the connection switches to, in the core

`Http.Conn` adds `Content-Length` to every response, and the server's loop knows only `Conn`.
Rather than teach either about WebSockets, the core has `Http.Upgrade`: a protocol a connection
may switch to, as a pure machine with events and actions like `Conn`'s, and `serve`'s `upgrade`
takes one. `Conn` hands a request the protocol wants on by its head, reads nothing after it, does
not write a `101` (the protocol writes it, without `Content-Length`), and hands the connection
over (`Conn.Action.switch`) once every earlier response is written (`Conn.flushSwitch_switch`).
The same loop then runs the protocol's machine as it runs `Conn`, but reads while it writes. So
write deadlines, the server's own threads, `stop` and the linger before a close are the ones
HTTP has, and there is no second socket loop in trusted code.

WebSockets stay a root of their own (`Lanes/Web/Http/WebSocketSession.lean`), as D122 made them.
With no `upgrade`, `Conn` never looks for one and the server never looks a socket up, so a
program that does not use WebSockets builds, links and runs as before (rule 1.8).

## The session's limits

Every limit is in `WebSocket.Session.Config` (rule 2.6), with defaults near `websockets`':
received frames and messages within `WebSocket.Limits` (1 MiB and 16 MiB); a message sent in
frames of at most `frame_max` (64 KiB); at most `outbox_max` (4 MiB) of frames waiting to be
written, beyond which nothing is read and a message that would exceed it closes the socket
`1008`; a ping after `ping_ms` (20 s) of silence, and the socket closed `1011` after `idle_ms`
(60 s); the peer's close waited for `close_ms` (5 s) after this side's. On `stop` every socket is
closed `1001`. Everything written after the `101` is frames a client reads back
(`WebSocket.Session.step_writes`): proving it found that a close's reason longer than 123 bytes
made a frame no client accepts, so `closePayload` now cuts the reason, on a character's boundary.

## Weighed (rule 1.8)

Reach: WebSockets are how browsers and many services talk both ways; a chat, a live counter, a
collaborative page or a feed that pushes could not be built on Lanes without a socket loop of
the application's own outside every proof. Cost: `Http.Upgrade` and its branch in `Conn`, a
table and about a hundred and fifty lines more in the trusted server loop, and the session with
its proofs; one concept a newcomer meets only when using it. Coupling: none forced on the core;
the gate and its proofs are unchanged, and the upgrade is generic, so another protocol switched
to after `101` takes the same path.

## Not done

A WebSocket client; extensions (permessage-deflate); `Http.Loopback` running a protocol switched
to (its exchange ends at the switch, so a front end's socket is tested live); a run of the whole
session against `websockets`' server on generated input (the session is tested against its
client live, and the frames it writes are proved).
