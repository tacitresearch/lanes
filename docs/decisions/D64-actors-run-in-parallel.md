# D64. Actors step in parallel within a wave, and connections run on threads of the server's own

Status: Partly superseded by D73 (`Runtime.Config.workers` turning parallel steps on, off by default) and by D110-volatile-actors.md (waves: steps committed in a journal's order)

One actor on one shard ran on one thread, and so did the kernel around it; the HTTP server ran
each connection's loop on whichever of Lean's task threads told it something. On the warm machine
(c7a.16xlarge, the server on 32 CPUs) hello world served 37,098 requests a second at 64
connections against Go's 137,938, on 3.2 cores against Go's 12.8, at 85 µs of CPU a request
against single-core Go's 15. This decision is a prototype of the two halves of using more cores
in one process, each behind a switch that is off by default: an IO thread per core for the
connections, and a shard's actors stepping in parallel with outputs merged in a fixed order.
Neither changes what anything does when it is off.

## What Lean's runtime allows for IO

- **One libuv loop per process.** `Std.Net` is libuv through `Std.Internal.UV`, and every
  binding uses one global loop, `lean::global_ev` (a symbol in the runtime's `.bss`, run by
  `lean::event_loop::run` on one thread). `Std.Internal.UV.Loop` has `configure` and `alive`,
  neither of which takes a loop; no binding creates or names another. So an event loop per core
  cannot be had in one Lean process.
- **No `SO_REUSEPORT`.** `lean_uv_tcp_bind` calls `uv_tcp_bind(handle, addr, 0)` (the
  disassembly of `tcp.cpp.o` in `libleanrt.a` clears the flags argument), though the libuv it
  links (1.53.0) has `UV_TCP_REUSEPORT`. Two listening sockets on one port, in one process or
  in several, are refused with `EADDRINUSE`. Several processes need several ports.
- **No libuv call from libuv's thread.** Every binding takes the loop's mutex with
  `event_loop::lock`, which tries the lock, and on failure wakes the loop (`uv_async_send`) and
  waits for it; it does not check `on_loop_thread`. The loop thread holds the mutex while it runs
  callbacks, so a binding called from a callback deadlocks. A connection's loop therefore cannot
  run on libuv's thread, as Node's does.
- **What can be chosen** is which threads run the connections' logic, and how they are woken.
  `BaseIO.mapTask (sync := true)` runs its function on the thread that resolves the task, which
  for a read or a write is libuv's thread, at once and without the task manager; there it may
  only hand the event on.

So the best Lean-only approximation of an event loop per core is a fixed set of threads that run
the connections, each connection on one of them for its whole life, woken directly.

## IO: lanes

`ServerConfig.ioThreads` (0 by default, which is the server as before). With `n` above 0 the
server starts `n` dedicated threads, its lanes, and deals each accepted connection to one in
turn (`next % n`). A lane is a parker and a queue of runs: telling a connection something whose
loop is not running posts the run to its lane and unparks it, whoever tells (the end of a read,
the shard handing over an answer, the ticker, `stop`). The continuations of reads and writes are
`sync`, so they run on libuv's thread, post and return; they never call libuv. A connection's
`Conn`, its buffer and its parse stay on one thread, and a request costs no task of the task
manager: the two task hops of D59 become two unparks of a thread that is likely warm. The
handshakes with libuv's thread for each read and write remain; only a loop of our own would remove
them.

## Logic: waves

`Runtime.Config.workers` (1 by default, which is the shard as before). With more:

1. **Inputs that arrive together are one turn.** The shell groups adjacent inputs of a batch
   (`Batch.group`) into `Command.inputs`, and `Journal.turnAll` accepts all of them, in order,
   before any work, with `fuel` for each. Its journal entries are `advance`, the inputs, and one
   `batch`: a sequence of operations the kernel already had, so replay, snapshots and
   `Batch.run_kernel` hold as they are (they are about every list of commands). Before, each input
   was a turn of its own and ran to quiet before the next was accepted, so the queue never held
   mail for two actors from two inputs at once and there was nothing to run in parallel.
2. **A batch is cut into waves.** A wave is the oldest `min fuel (max 1 queued)` messages queued
   when it starts, and as many units of work. Messages sent during a wave are queued behind it,
   where `runBatch`'s first-in first-out queue puts them, and delivered after every message of
   it: in a later wave of the same batch if fuel remains, else in the next batch, as before. They
   are not planned in the wave that sends them.
3. **The steps of a wave are worked out ahead** (`Kernel.plan`). The messages are grouped by
   receiver in queue order; for each receiver that is up, its state is taken out of the kernel
   and its steps on its messages computed one after another (`Kernel.ahead`). The receivers are
   cut into `workers` pieces, each a task of Lean's task pool (`Task.spawn` in pure code), the
   first on the shard's own thread. Lean's pool is one queue served by its worker threads, so a
   thread that is free takes the next piece: balancing among pieces, not stealing among
   per-thread queues. A wave with mail for one actor only is not planned.
4. **The kernel then does the wave's units of work as `runBatch` does them** (`runBatchAhead`):
   oldest message first, timers in their turn, a receiver that is down started, effects performed
   in order, released actors released, with one difference: delivering message `m` to `i`, it
   takes `i`'s next planned step if that step is for `m`, instead of calling `step`. It drops
   `i`'s plan when `i` is started, when a timer of `i` fires, when another message reaches it and
   when it is no longer up after a step, so a planned step is only ever taken from the state it
   was computed from.

The merge is in queue order, not in the order of actor identities. Queue order is the order the
sequential kernel already uses, so the parallel batch is not a different run that the semantics
also allows: it is the same run, value for value. Actor-identity order would deliver a later
message to a lower identity before an earlier one to a higher; the semantics allows that (links
are ordered per sender and receiver, not globally), but the kernel has no operation for it, so it
would need a new operation and journal entry, a proof that the kernel stays in the semantics
under it, and a theorem relating the two orders up to `SysState.Equiv`: outputs, sends and timer
tokens would come out in another order.

### What the semantics allows, and why the parallel batch is a sequential run

The kernel's `step` for actor `i` reads `i`'s state and the message, and nothing else; settling
its result writes `i`'s cell, the queue, the agenda and the outputs, and no other actor's state or
whether it is up. So the steps of distinct actors, and the steps of one actor on consecutive
messages, can be computed before any is committed, on any thread and in any order: what is
computed is the same pure value. Committing them in the order `runBatch` would have computed them
gives `runBatch`'s kernel, events and outputs. Nothing about the semantics is assumed beyond what
`Kernel.exec_reachable` already proves of `runBatch`.

## The theorems (`Lanes/Runtime/Wave.lean`)

- `Kernel.frame_handle`, `frame_startActor`, `frame_fire`, `frame_settle`: handling a message for
  `i`, starting `i`, firing `i`'s timer, settling `i`'s step leave every other actor's state and
  whether it is up as they were (`Kernel.Frame i k k'`). This is the per-pair commutation that
  makes working ahead sound: an actor's step computed before another actor's step is committed is
  the step it would have taken after.
- `Kernel.runBatchAhead_eq`: for every plan that fits the kernel (`Plan.Good`: what it holds for
  each actor starts from that actor's state, and the actor is up), `k.runBatchAhead p fuel =
  k.runBatch fuel`, the whole `Step`: kernel, events and outputs.
- `Kernel.good_plan`: the plan `Kernel.plan` builds fits, whatever the number of workers and
  however the actors are cut into pieces; each step carries its reason in its type (`Kernel.Done`),
  so the pieces' order and the threads they ran on do not enter the proof.
- `Kernel.runBatch_add`, `Kernel.waves_eq`, `Kernel.runWaves_eq`: `k.runWaves workers fuel =
  k.runBatch fuel` for every number of workers.
- `Journal.turnAll_eq_exec`: a turn of inputs together is what replaying its journal entries
  does, so `Batch.run_kernel`, `run_sound`, `run_peek` and `run_resolved` hold for batches with
  `Command.inputs` (their proofs take the new case).

All of it is proved, on the standard axioms (`Tests/Axioms/Runtime.lean`); there is no `sorry`
anywhere. A stronger statement, that handling two distinct actors' messages in either order gives
the same kernel, is false of this kernel: the sends of the two go to the one queue in the order
they were handled, and timers get tokens in that order. It holds only up to `SysState.Equiv` and
a renaming of tokens, and nothing here needs it.

## Trusted, before and after

Before: the shell (`Lanes/Runtime/IO/Shell.lean`) and the server's loop
(`Lanes/Web/IO/Server.lean`), `Std.Net` and libuv. After, besides: that the shell groups the
inputs of a batch when `workers` is above one; that the server's lanes run what is posted to them
and end when the server is down; that a `sync` continuation runs where Lean's documentation says
and the lane's queue is the only thing it touches; and Lean's `Task.spawn` and `Task.get`, which
the logic models as `⟨f ()⟩` and its projection, as every compiled Lean program trusts them. No
new C.

## Measured

Locally, in a shared four-core container: `bench/README.md`, "Parallel actors and IO threads".
In short: the kernel alone scales with workers where steps are costly (64 actors, steps of about
30 µs: 31, 17 and 9 µs a message on one, two and four workers) and costs about a microsecond more
a message where they are cheap (0.3 to 0.45 against 1.3 to 1.7), most of it Lean freeing objects
that tasks made, which it counts atomically. Over HTTP on two server CPUs neither switch gains,
because the two cores are already full; `lanes-heavy-par` costs 88 to 102 µs a request against
66 to 75, its waves being a few messages each. The numbers that decide are the warm machine's,
with cores to spare.

## Risks

- **Objects a task has seen are never updated in place again.** Lean marks everything a task's
  closure reaches as shared between threads, for good, and never updates a shared object in
  place. The plan hands a task an actor's state and its messages, not the kernel; but an actor
  whose state holds a large map then copies that map on every later step that changes it, where
  the sequential kernel could update it in place. Small states, as in the benchmark, do not see
  this; an actor with a large state should not be stepped ahead. Not measured yet.
- **The gate is one actor.** Behind `Http.serve`, every request is two steps of the gate, which
  are never in parallel with each other, and the kernel's commit is sequential. Only the steps of
  the system's own actors are worked out in parallel, so for small steps the waves cost more than
  they save; they pay where steps are costly and spread over many actors (`lanes-heavy-par`).
- **A planned step is compared with the message delivered** (`decide (m = msg)`), which costs as
  much as comparing the message, a request with its body for the gate.
- **Lanes are fixed at the start** and a connection never moves: a lane with many busy
  connections is not relieved by an idle one.
- **Grouped inputs change the journal's shape** (one `batch` for several inputs). It replays the
  same, but a journal written with `workers` above one and one written without differ byte for
  byte, and a batch of many inputs is one longer turn between two looks at the inbox.
