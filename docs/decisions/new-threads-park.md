# D?. Threads park, and a connection's loop runs where it is told something

The server of `docs/decisions/D57-the-server-runs-its-own-connections.md` spent about 300 µs of
CPU on a request that answers `hello`, on two cores. Nothing spun. Lean's
task manager ends every task with `notify_all` on one condition, on which every thread waiting
on a task sleeps, so a `main` in `server.wait.block` and the shard waiting for input woke for
every task in the process. And each turn of a connection's loop selected over the socket, its
inbox and a timer, about eight libuv calls, each a handshake with libuv's thread
(`bench/README.md`, "Where the time goes").

- **A thread that waits parks.** `Lanes.Parker` is a pthread mutex and condition with a
  timeout (`native/lanes.c`), which Lean has only without one. The shard parks while it has
  nothing to do, until a sender unparks it or its next timer is due, and hands outputs over on
  its own thread instead of on a task it waits for. `Lanes.block` runs an `Async` on the
  calling thread and parks until it is done; a `main` waits for its server with
  `Lanes.block server.wait`.
- **A connection's loop runs on the thread that tells it something** while it is not running:
  the task that sees a read end, a task started for an answer, a tick or `stop`. It handles
  what it was told, oldest first, and never waits. Only the loop touches its `Conn`; the others
  share a short queue under a mutex. It starts one read at a time, only while
  `Conn.wantsInput` holds and not while its last write is going on, so that what waits to be
  written is bounded by what is in flight. It does not wait for a write: one that fails is
  reported as `broken` with the next event.
- **One ticker thread keeps the deadlines** of all connections. Each loop leaves the time of
  its next deadline, `Conn.deadline` or the end of `write_ms` for a write still going on, and
  every `tick_ms` (25 by default) the ticker tells those whose time has passed. A deadline is
  acted on up to `tick_ms` late, which no timeout of an HTTP connection needs to be shorter
  than.

`Conn.step`, `Waiting` and the gate are unchanged, and so is what is proved of them. What the
loop does with them is trusted, as before, and listed in `TRUSTED.md`. A request now costs two
libuv calls and two task hops, about as much as `Std.Net` costs a bare echo; the handshakes and
the hops are Lean's runtime, and a loop of our own in C is what would remove them.
