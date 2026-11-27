# D85. A loop of C for the server's connections, off by default

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
while `Conn.wantsInput`, else none), when to look again (`Conn.deadline`, `Conn.wakeAt`),
whether to say `sent` once nothing is unwritten (`Conn.unsent`), and whether the connection has
closed. Requests that stream, their pieces and their pulls go to the system as the server's own
loop sends them. A request is handed to the system by the same `submit` as before
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

The C is about 515 lines (`TRUSTED.md` has the count), over the 400 aimed at: the platform
stub, the error path of every system call and the set-up of sockets are a third of it; the loop
itself (accept, read, write, deadlines, mail) is about 250. The Lean beside it is about 200
lines, and `Server.lean` grew by about 40 to choose the loop.

## Measured

In the shared four-core container only (`bench/README.md`, "A loop of C", has the table and how
it was run): the server on two CPUs, the load on the other two, four rounds of 5 s, three of
them with two or three cores of other agents' work on the machine. The rates were measured before a short
read was taken to end the reads until the next edge, which took one `recv` a request off.

| at 64 connections | req/s, median (range) | CPU µs a request |
| --- | ---: | ---: |
| `go` | 110,605 (59,948–157,086) | 12 |
| `lanes-io`, 4 threads | 34,364 (28,756–37,975) | 35 |
| `lanes-cloop`, 1 thread | 51,444 (41,002–52,922) | 19 |
| `lanes-cloop`, 2 threads | 53,602 (51,209–56,261) | 20 |
| `lanes-cloop`, 4 threads | 50,533 (32,947–68,427) | 24 |

So about 1.5 times the requests of `lanes-io` at 16 and 64 connections, 1.6 times at one, for
40–45% less CPU a request; Go still serves about twice as many, for 12 µs. A request costs
5 system calls where `lanes-io` makes 15 (11 of them `futex`): a read, a write, under two futex
calls to hand the request to the shard and back, and a share of an `epoll_wait` and of the
eventfd's write and read. Of the CPU, at 16 connections on one thread, the loop's thread spends
about 10 µs a request (reading the request, `Conn.step`, encoding the response, the gate's
`Waiting`) and the shard's about 7.

## Verdict

Worth keeping as the opt-in it is, not yet worth making the default.

- It does what it was for: the handshakes with libuv's thread and the task hops are gone, and
  the CPU a request falls by about 40%, the share D59 guessed.
- It does not close the gap to Go, and cannot alone: what is left is Lean's own work, and one
  shard is one thread. The shard's batch, kernel and gate are about 7–11 µs a request, so a
  single shard tops out near 90,000–140,000 a second however many loop threads feed it; Go's
  `net/http` on 32 cores answered 139,730. Past that the next step is the shard's cost, or
  requests spread over several shards, not the IO.
- It is about 515 lines of C that every application using it trusts, and a second path through
  the server to keep in step with the first: streams had to be carried over the week they were
  merged. Each change of `Conn.Action` or `Conn.Event` is now two adapters.

Before adopting it as Linux's default: run `lanes-cloop` on the warm machine at 1, 2, 4 and 8
threads (`bench/README.md`); if it gains at least half over `lanes-io` there, make it the default
on Linux with the Lean loop kept for other systems, model-check its C (below), and move the
choice of thread for a connection into Lean.

## Not done

- macOS: no kqueue; elsewhere than Linux `serve` refuses `.c` as it starts, and the tests check
  that.
- IPv6, TLS, and a bound on the copies made when answers arrive for a socket that is full.
- Reading into the connection's buffer: the C copies what it reads into a fresh `ByteArray`,
  and `Conn.receive` copies it again onto the buffer.
- CBMC. A harness that checks each operation of a thread (drive a connection, accept, take the
  mailbox, sweep, stop) keeps an invariant of the table of connections, on stubs of Lean and the
  sockets that may do anything their contracts allow, ran out of 15 GB in CBMC 5.95 for every
  operation but the sweep; one drive from one fixed state checked in 12 s. It is in the history
  of this decision's branch, to be made to finish: fewer objects in the model of Lean's heap, or
  a harness for each operation from a smaller state.
