# D?. A loop of C for the server's connections, off by default

On the warm machine (64 vCPUs, the server on 32) hello world on `lanes-io` served 45,088
requests a second at 64 connections, Go's `net/http` 139,730. Lean's runtime has one libuv loop a
process (`lean::global_ev`), binds without `SO_REUSEPORT`, and its bindings cannot be called from
libuv's own thread (D64), so connections cannot have a loop a core in Lean. D59 and
`bench/README.md` estimated that a loop of C would save the handshakes with libuv's thread and the
hop on each read, perhaps half the CPU. This decision is that loop, as a prototype behind a switch
that is off by default, to measure it.

## What it is

`ServerConfig.loop := .c` (`.lean` by default) runs the connections on `ioThreads` threads of C
(`native/loop.c`, declared in `Lanes/Web/IO/CLoop.lean`). Each thread has its own epoll, its own
eventfd and its own listening socket on the server's port, bound with `SO_REUSEPORT`, so the
kernel deals connections among the threads, and a connection stays on its thread for its life.
Sockets are non-blocking and edge-triggered; deadlines are swept every `tick_ms`, as the ticker of
D59 does. The C decides nothing (rule 3.9): for each thing that happens to a connection it calls
`turn` in Lean, which is `Conn.step` and the actions done as the server's own loop does them, and
does what the `Turn` it returns says: the bytes to write, how many to read at most (`Conn.room`
while `Conn.wantsInput`, else none), the next deadline (`Conn.deadline`), and whether the
connection has closed. A request is handed to the system by the same `submit` as before
(`Ops.front`, `Bridge.prepare`, `Http.Waiting`, `Runtime.tryInput`), so the gate, the ids, the
`503` of a full inbox and everything proved of them are unchanged. Which connections are taken is
`Conn.Count.admit`, through `open`.

## Lean's objects across threads

Lean counts references without atomics for an object only one thread can see, and with them once
`lean_mark_mt` has marked it shared; a `Mutex`, an `IO.Ref` and a task mark what they are handed.
So:

- The threads are C's (`pthread_create`); each calls `lean_initialize_thread` first and
  `lean_finalize_thread` last, and calls Lean's `@[export]` functions directly. No task, no
  promise and no lock of Lean's task manager is on the path of a request.
- Each thread has a `Handler` of its own, so no two threads count references to one object
  (with one shared, every call would bounce its count's cache line between cores). The handlers
  are marked thread-shared before the threads start, since what they hold, the configuration,
  `submit` and the server's tables, is shared.
- The state of a connection (`Line`: the `Conn` and its `submit`) is made on its thread, held by
  the C, and given to and taken back from each `turn`; no other thread sees it, so its counts stay
  plain and `Conn.step` updates its buffer in place.
- An answer comes from the shard's thread. Its continuation, made by `turn`, posts it to the
  mailbox of its connection's thread, a `Std.Mutex`, which marks it shared; the first letter into
  an empty mailbox writes the thread's eventfd. The thread reads the eventfd, then takes the whole
  mailbox, so a letter posted after the take writes the eventfd again.
- An exported function takes its arguments, so the C gives each call references of its own; it
  reads `Turn` and `Mail` by the layout Lean's compiler gives them.

The C is 0 lines (`TRUSTED.md`); the Lean beside it 0, and `Server.lean` grew by about 30 to
choose the loop.

## Measured

RESULTS

## Verdict

VERDICT

## Not done

- macOS: no kqueue; elsewhere than Linux `serve` refuses `.c` as it starts, and the tests check
  that.
- IPv6, TLS, and a bound on the copies made when answers arrive for a socket that is full.
- CBMC (`scripts/cbmc.sh`) is run by hand: it needs `cbmc`, which CI does not install.
