# HTTP benchmark

How fast Lean's IO stack and Lanes serve HTTP next to Go's `net/http`, and where the time goes.
Every server answers `GET /` with `hello\n`. A keep-alive load generator holds N connections,
each sending one request at a time, for a fixed time, and measures requests a second and
latency. Numbers from a shared or small machine are no results: run it on the warm runner
machine through the workflow.

## The servers

| Name | What | Source |
| --- | --- | --- |
| `go1` | Go `net/http`, `GOMAXPROCS=1` | `go/hello/main.go` |
| `go` | Go `net/http`, `GOMAXPROCS` the server's CPUs (Go's default) | `go/hello/main.go` |
| `tcp` | `Std.Net` TCP on libuv, a task per connection, a fixed response per request head; no HTTP parsing. The floor under `Std.Http` | `TcpHello.lean` |
| `tcp-park` | `tcp` with its main thread asleep rather than waiting on a task (below) | `TcpHello.lean` |
| `std` | `Std.Http.Server` with its default configuration, which Lanes ran before its own server (D57); it closes a connection after 100 requests | `StdHello.lean` |
| `std-unlimited` | `std` with no limit of requests per connection | `StdHello.lean` |
| `lanes` | `Lanes.Http.serve` with one actor (`Server.system`) that answers each request; no journal; one worker, so `Runtime.Config.parallel` is off | `LanesHello.lean` |
| `lanes-journal` | `lanes` with a journal: every request is appended and synced (`fsync`, `Lanes/Durable/IO/Journal.lean`) before it is answered; the journal only grows | `LanesHello.lean` |
| `lanes-snapshot` | `lanes-journal`, also saving the kernel and cutting the journal every 1024 inputs | `LanesHello.lean` |
| `lanes-io` | `lanes` with its connections on `IO_THREADS` threads of the server's own (`ServerConfig.ioThreads`) | `LanesHello.lean` |
| `lanes-cloop` | `lanes` with its connections on `IO_THREADS` threads of C, each with its own epoll and listening socket (`ServerConfig.loop := .c`, `native/loop.c`); Linux only | `LanesHello.lean` |
| `lanes-par` | `lanes` with `WORKERS` threads to work out actors' steps on every wave (`Runtime.Config.workers`, `parallel := .on`): one actor, so this measures what grouping inputs and planning waves cost | `LanesHello.lean` |
| `lanes-io-par` | both | `LanesHello.lean` |
| `lanes-many` | `K` (64) counters, request `n` to counter `n % K` | `LanesMany.lean` |
| `lanes-many-par` | `lanes-many` with `WORKERS`, `parallel := .on` | `LanesMany.lean` |
| `lanes-many-auto` | `lanes-many` with `WORKERS`, `parallel := .auto`: the shard chooses each batch from its timing | `LanesMany.lean` |
| `lanes-heavy` | `lanes-many` with `SPIN` (20,000) rounds of hashing in each step, about 20 µs | `LanesMany.lean` |
| `lanes-heavy-par` | `lanes-heavy` with `WORKERS`, `parallel := .on` | `LanesMany.lean` |
| `lanes-heavy-auto` | `lanes-heavy` with `WORKERS`, `parallel := .auto` | `LanesMany.lean` |

`IO_THREADS` and `WORKERS` are a quarter of the server's CPUs each by default (8 and 8 on the warm machine), `K` and `SPIN` as above; all four are read from the environment by `servers.sh`. `benchWaves` (`Waves.lean`) is the kernel alone, without IO: `benchWaves K spin workers inputs rounds`. `benchAuto` (`Auto.lean`) is the shard without IO in its three modes: `benchAuto [workers] [runs] [scale] [workload…]`.

`lanes*` run whatever `Lanes.Http.serve` is on the commit measured: a new HTTP server under
that name is measured by the same rows. `servers.sh` holds the commands.

## What is measured

For each server, at 1, 16 and 64 connections, three runs of 10 s after a 1 s warm-up, each run
a fresh server process on a fresh port and an empty journal. The table gives medians over the
runs and the spread of the rate (lowest, highest, and (highest − lowest) / median):

- requests a second; latency p50, p99 and max, from the load generator's clock around each
  request; reconnects (a server that closes a kept-alive connection) and errors;
- the server's CPU time over the measured window, as cores and as µs a request
  (`/proc/<pid>/stat`), its peak RSS (`VmHWM`) and its threads;
- other CPU: the CPU time spent on the server's and the load generator's CPUs by anything but
  the two and the kernel's threads, and how many other GitHub Actions jobs were on the machine.
  A run with another job, or with more than `IDLE_CORES` (1) cores of other CPU, is marked
  disturbed and the report says so above the table.

The server and the load generator are pinned with `taskset` to disjoint CPUs: by default the
first and the second half of the CPUs the script may use (32 and 32 on a c7a.16xlarge).
Go sizes `GOMAXPROCS` from its affinity mask, but Lean's runtime sizes its thread pool from the
machine's CPU count, so `run.sh` sets `LEAN_NUM_THREADS` to the number of the server's CPUs
unless it is set.

`run.sh` writes `results/<date>-<commit>.md` (the table, under the machine and the settings),
`results/<date>-<commit>.json` (the same, and every run) and `.jsonl` (one line a run, as the
load generator gave it). `results/` is not committed.

## Running it

Locally (Lean's toolchain, Go 1.24 or later, `taskset`):

```bash
mkdir -p bench/.lake && ln -sfn ../../.lake/packages bench/.lake/packages   # once: the repository's packages
bench/run.sh                                          # everything, about 20 minutes
RUNS=1 SECONDS_EACH=2 bench/run.sh go std lanes       # a quick look at some servers
SERVER_CPUS=0-7 LOAD_CPUS=8-15 CONNS="16" bench/run.sh lanes-journal
```

The settings are in the head of `run.sh`: `RUNS`, `SECONDS_EACH`, `WARMUP_SECONDS`, `CONNS`,
`SERVER_CPUS`, `LOAD_CPUS`, `IDLE_CORES`, `IDLE_WAIT_MINUTES`, `REQUIRE_IDLE` and `BUILD`. It
builds the Go programs into `.build/` and the Lean ones with Lake; `bench/` is a Lake package
of its own that requires Lanes at `..` and uses the repository's `.lake/packages`, so its
`lake-manifest.json` must pin what the repository's pins (`run.sh` checks; after a dependency
bump, copy the pins).

`profile.sh` looks inside one server under load: `threads` (CPU seconds of each thread),
`syscalls` (system calls a request, from `strace`), `callgrind` (instructions a request by
function) and `perf` (context switches a request and the hottest functions; `PERF` names the
binary). For example `bench/profile.sh syscalls lanes 16 5`.

Through GitHub: **Actions → Bench → Run workflow** (`.github/workflows/bench.yml`), or
`gh workflow run bench.yml -f seconds=10 -f runs=3`. Inputs: `seconds`, `runs`, `servers` (all
when empty), `require-idle` (on), `idle-wait-minutes` (30), `lean-threads` (the server's CPUs when empty) and `hosted`. It runs where the
mutation gate runs (`docs/RUNNERS.md`): with the AWS variables set, on the warm machine, which
it starts and, when no other run needs it, stops. The report is in the run's summary and in the
artifact `bench-<run>-<attempt>`.

The warm machine has 16 runners, and the others may take jobs while the benchmark runs. With
`require-idle`, `run.sh` waits for the machine to have no other job and at most a core of
other CPU, fails if it does not within `idle-wait-minutes`, and fails at the end if any run was
disturbed; the report is uploaded either way. Two runs of the benchmark never overlap (one
concurrency group). A machine launched for the run (`LANES_AWS_INSTANCE_TYPE`) has no other
jobs. On `ubuntu-latest` (4 vCPUs) the workflow runs, but its numbers are no results.

## Where the time goes

Measured in a 4-core container shared with other work, the server on 2 cores and the load on
the other 2, so only CPU a request, context switches a request and runs side by side count.
Before is the server of `docs/decisions/D57-the-server-runs-its-own-connections.md` as
it was merged; after is this one.

| workers | conns | req/s before → after | CPU µs/req before → after | context switches/req before → after |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 1 | 2,734 → 6,028 | 535 → 150 | 88 → 7.0 |
| 2 | 16 | 4,798 → 22,847 | 328 → 60 | 44 → 2.5 |
| 2 | 64 | 4,929 → 22,214 | 321 → 60 | |
| 32 | 1 | 1,780 → 8,668 | 751 → 94 | 160 → 6.8 |
| 32 | 16 | 3,748 → 18,079 | 339 → 85 | 110 → 5.5 |
| 32 | 64 | 6,455 → 23,623 | 231 → 61 | |

There was no spinning: an idle server uses no CPU. The time went to waking threads, for three
reasons, two of them in Lean's runtime.

1. **A thread waiting on a task wakes whenever any task ends.** The task manager ends each task
   with `notify_all` on one condition (`task_manager::resolve_core`), on which every thread in
   `IO.wait`, `Task.get` or `Async.block` sleeps. A `main` in `server.wait.block`, the shard
   waiting for input, and the shard handing outputs over (`.block`, which also starts a task)
   were such threads. They now park on a condition of their own (`Lanes/Runtime/IO/Park.lean`,
   `Lanes.block` for a `main`). Alone it is `tcp` against `tcp-park`: 97 → 75 µs a request at
   one connection, 2.9 → 1.7 context switches at 16; for `lanes` at 64 connections it took 321
   → 140 µs.
2. **A libuv call from a worker is a handshake with the loop thread** (`event_loop::lock`): the
   loop thread holds the loop's lock in `epoll_wait`, so the caller writes its eventfd and waits
   for the lock, and the loop thread wakes, lets go and waits for the caller: about four context
   switches a call. The old connection loop selected over the socket, its inbox and a timer on
   every turn, about eight such calls and five task hops a turn, two turns a request: 368 system
   calls a request at one connection, 319 of them `futex`. The loop now reads once at a time,
   does not wait for its writes and leaves deadlines to one ticker thread: two libuv calls and
   two hops a request, 36 system calls.
3. **A task hop wakes a worker**, under the task manager's one lock. With 32 workers on 2 cores
   the one woken is cold, which is why `tcp` costs 114 µs a request at 16 connections with 32
   workers and 23 with 2.

After, at 16 connections, `perf` puts about 40% of the server's CPU in the kernel (a third of
it switching threads, the rest the loopback TCP), 20% in allocating and freeing, 20% in the
shard (`Batch.run` and the kernel, about 11 µs a request), 11% in reading the request
(`Request.read`) and the rest in libuv's calls. `lanes` is now where `tcp` is at 32 workers;
causes 2 and 3 cannot be removed from our side.

A loop of our own in C would: epoll on each core, non-blocking sockets, `Conn.step` called
through `@[export]`, answers from the shard through an eventfd. That is about 500 lines of
trusted C and 60 of bindings in place of `Lanes/Web/IO/Server.lean`'s 470, and it would take away the
handshakes and the hop on each read, leaving a read, a write and a wakeup of the shard a
request. What it can save here is the scheduling and libuv's share, perhaps half the CPU; the
allocation, the parsing and the shard stay. It is not written: the evidence is that Lean's own
work is now as large as the cost of crossing threads.

## Parallel actors and IO threads

`docs/decisions/D64-actors-run-in-parallel.md`: connections on threads of the server's own
(`lanes-io`) and the actors of a wave stepping in parallel (`lanes-par`, `lanes-many-par`,
`lanes-heavy-par`). Measured in the shared 4-core container, the server on 2 CPUs and the load on
the other 2, `IO_THREADS=2 WORKERS=2`, three runs of 5 s, other agents building on the machine
(10 of 72 runs disturbed), so only the direction counts:

| server | conns | req/s | CPU µs/req |
| --- | ---: | ---: | ---: |
| `lanes` | 1 / 16 / 64 | 8,486 / 29,022 / 26,068 | 100 / 46 / 49 |
| `lanes-io` | 1 / 16 / 64 | 8,375 / 23,397 / 30,712 | 102 / 61 / 50 |
| `lanes-par` | 1 / 16 / 64 | 6,666 / 27,172 / 26,679 | 145 / 52 / 59 |
| `lanes-io-par` | 1 / 16 / 64 | 6,093 / 26,354 / 29,027 | 147 / 57 / 55 |
| `lanes-many` | 1 / 16 / 64 | 7,640 / 22,892 / 28,328 | 114 / 66 / 55 |
| `lanes-many-par` | 1 / 16 / 64 | 7,212 / 22,227 / 22,605 | 123 / 70 / 67 |
| `lanes-heavy` | 1 / 16 / 64 | 5,449 / 21,159 / 23,734 | 167 / 75 / 66 |
| `lanes-heavy-par` | 1 / 16 / 64 | 5,466 / 15,509 / 18,150 | 170 / 102 / 88 |

On two server CPUs both switches cost CPU and gain nothing: libuv's thread, the shard's and the
connections already fill the two cores (1.3 to 1.6 cores used), so there is no idle core for a
lane or a worker, and the load generator on two cores is the limit. With the server on three
CPUs and the load on one, the load generator is the limit (about 1.6 cores of the server used).
What the warm machine has to show is whether, with cores to spare, `lanes-io` lowers the CPU a
request and `lanes-heavy-par` raises the rate past `lanes-heavy`, whose shard thread is then the
limit (about 20 µs of step and 11 of kernel and gate a request, so about 30,000 a second).

The kernel alone (`benchWaves`, no IO, 64 counters, 256 messages a round, `LEAN_NUM_THREADS=4`,
the same container):

| step | 1 worker | 2 workers | 4 workers |
| --- | ---: | ---: | ---: |
| `spin 20000` (about 30 µs) | 31 µs a message | 17 | 9 |
| `spin 2000` (about 3 µs) | 3.7 µs | | 3.0 |
| `spin 0` | 0.32–0.45 µs | 1.27 | 1.5–1.7 |
| `spin 20000`, 4 messages a round | 30 µs | | 35 |

So the waves scale with workers where steps are costly and a wave is large, and cost about a
microsecond a message where steps are cheap: `perf` puts most of that in `lean_dec_ref_cold`,
freeing objects a task has made, which Lean counts atomically. A wave of a few messages costs
the hand-off to another thread and back. `lanes-heavy-par` sees both: the shard takes a few inputs
at a time from 64 connections, so its waves are small.

### Choosing from the shard's timing

`docs/decisions/D73-adaptive-waves.md`: with `parallel := .auto` the shard times its batches and
runs each on its own thread or on the pool (`Lanes/Runtime/Pace.lean`). `benchAuto` runs the shard
without IO adapters, its inbox holding 64 inputs, on seven workloads; each is run in each mode in
turn, `runs` times, a fresh shard each time, and the table gives the median µs a message and the
spread, (highest − lowest) / median. It takes about 30 s:

```bash
cd bench && lake build benchAuto && LEAN_NUM_THREADS=4 .lake/build/bin/benchAuto 4 7 1
```

In the shared four-core container, four workers, seven runs each, three sessions a few minutes
apart (load average 4 to 6, other agents building); µs a message, off / on / auto, the spread of
auto's seven runs in brackets:

| workload | session 1 | session 2 | session 3 | auto on the pool |
| --- | --- | --- | --- | ---: |
| trivial, 64 actors | 1.2 / 3.6 / 1.3 (72%) | 1.5 / 4.0 / 1.4 (42%) | 2.0 / 4.7 / 1.7 (42%) | 0% |
| trivial, 1 actor | 1.5 / 1.4 / 1.4 (62%) | 1.8 / 1.7 / 1.7 (16%) | 1.7 / 1.8 / 1.6 (44%) | 0% |
| `spin 2000` (about 3 µs), 64 actors | 4.5 / 6.7 / 4.5 (25%) | 5.0 / 7.1 / 5.0 (17%) | 5.0 / 6.6 / 6.2 (38%) | 2–9% |
| `spin 20000` (about 30 µs), 64 actors | 34.5 / 35.1 / 34.4 (31%) | 37.1 / 22.5 / 24.8 (21%) | 36.6 / 36.3 / 40.5 (33%) | 21–89% |
| `spin 20000`, 2 actors | 35.7 / 21.6 / 25.0 (45%) | 33.8 / 22.4 / 22.7 (85%) | 34.2 / 33.2 / 32.8 (46%) | 68–90% |
| every other step `spin 20000` | 18.0 / 17.0 / 17.3 (12%) | 20.1 / 19.2 / 18.3 (28%) | 19.3 / 19.5 / 21.1 (32%) | 6–57% |
| phases of heavy and trivial | 3.5 / 5.3 / 3.0 (41%) | 3.5 / 5.6 / 3.2 (15%) | 3.5 / 5.2 / 3.4 (26%) | 2–3% |

The spread of a mode within a session was 9% to 202%, so differences under about a third are
noise. Within that, auto was as fast as the faster of off and on in every row of every session:
at worst 24% slower, in a row whose spread was 38%. On the workload the other suits, `on` was up
to 2.8 times slower than auto (trivial steps on 64 actors) and `off` up to 1.5 times (heavy
steps).
Whether the pool paid changed from one session to the next: heavy steps on 64 actors were 35 µs
a message on the pool in sessions 1 and 3 and 22 in session 2, and auto ran 42%, 89% and 21% of
its batches there. Trivial steps never went to the pool. "Phases" is three rounds of 3,000 heavy
inputs and 50,000 trivial ones, so that auto has to follow a change twice a round.

A group of inputs costs more a message the larger it is: `Batch.run` alone on 1,024 trivial
inputs, as one group, took 1.3–1.4 µs a message against 0.55 for the same inputs as separate
turns; as groups of 64, 0.565 against 0.61. So a group holds at most `min batch snapshotEvery`
inputs.

Over HTTP, the server on two CPUs and the load on the other two, `WORKERS=2`, four rounds of one
run of 3 s per server, the servers taking turns within a round; requests a second, the median of
four and the spread, and CPU µs a request (most runs disturbed by other jobs):

| server | 16 conns | 64 conns | CPU µs/req at 16 / 64 |
| --- | ---: | ---: | ---: |
| `lanes-many` (off) | 22,311 (57%) | 27,228 (59%) | 67 / 46 |
| `lanes-many-par` | 22,180 (29%) | 20,938 (27%) | 59 / 55 |
| `lanes-many-auto` | 20,979 (32%) | 23,824 (17%) | 55 / 58 |
| `lanes-heavy` (off) | 14,208 (39%) | 17,374 (29%) | 87 / 84 |
| `lanes-heavy-par` | 11,762 (57%) | 14,199 (33%) | 92 / 99 |
| `lanes-heavy-auto` | 15,019 (30%) | 13,302 (38%) | 88 / 85 |

Two CPUs are already full with libuv's thread, the shard and the connections (D64), so no mode
gains, and the differences are inside the noise. `lanes-heavy-auto` used the CPU a request of
`lanes-heavy`, not that of `lanes-heavy-par`: it kept to the shard's thread. The warm machine,
with cores to spare, is where `lanes-heavy-auto` should come out near `lanes-heavy-par`.

## A loop of C

`docs/decisions/D85-a-loop-of-c.md`: `lanes-cloop` runs the connections on `IO_THREADS` threads
of C, each with its own epoll and listening socket (`ServerConfig.loop := .c`). Measured in the
shared 4-core container, the server on CPUs 0–1 and the load on 2–3, `LEAN_NUM_THREADS=2`; four
rounds of one run of 5 s per server and connection count, the servers taking turns within a
round. The first round had under a core of other CPU; the other three had two to three cores of
it (other agents building, load average 4 to 9.5), so only the direction counts. Requests a
second, the median of four and the range, and the median CPU µs a request:

| server | 1 conn | 16 conns | 64 conns | CPU µs/req at 1 / 16 / 64 |
| --- | ---: | ---: | ---: | --- |
| `go` | 15,572 (12,968–17,281) | 98,152 (76,772–130,776) | 110,605 (59,948–157,086) | 53 / 12 / 12 |
| `lanes-io`, 4 threads | 7,901 (5,883–9,929) | 28,890 (23,716–32,023) | 34,364 (28,756–37,975) | 97 / 35 / 35 |
| `lanes-cloop`, 1 thread | 12,822 (7,919–14,380) | 43,907 (23,562–46,538) | 51,444 (41,002–52,922) | 51 / 21 / 19 |
| `lanes-cloop`, 2 threads | 10,963 (8,618–14,596) | 45,661 (42,860–48,567) | 53,602 (51,209–56,261) | 63 / 22 / 20 |
| `lanes-cloop`, 4 threads | 11,835 (11,076–11,970) | 36,013 (30,594–57,914) | 50,533 (32,947–68,427) | 60 / 30 / 24 |

In the quiet first round alone, at 64 connections: `go` 117,208, `lanes-io` 34,577,
`lanes-cloop` 52,899, 54,712 and 68,427 on 1, 2 and 4 threads.

The C loop serves about 1.5 times what `lanes-io` does at 16 and 64 connections and 1.6 times at
one, for 40–45% less CPU a request (19–22 µs against 35); Go serves about twice what it does, for
12 µs. Four threads on two CPUs are oversubscribed and cost CPU. A request costs 5 system calls
(`profile.sh syscalls`, 16 connections): 1.3 reads, 1.3 writes, 1.8 `futex` (handing the request
to the shard and its answer back), and a share of an `epoll_wait` and of the eventfd's write and
read; `lanes-io` makes 15, 11 of them `futex`. (The rates above are from before a short read
ended the reads until the next edge, when a request cost 2.2 reads.) On one loop thread at 16 connections the loop's
thread used about 10 µs a request and the shard's about 7 (`profile.sh threads`).

On the warm machine, the servers to compare are the Lean loop and the C loop at the same
threads; `lanes-io-N` and `lanes-cloop-N` are those servers on N threads whatever `IO_THREADS`
is:

```bash
gh workflow run bench.yml -f seconds=10 -f runs=3 \
  -f servers="go lanes-io-8 lanes-cloop-1 lanes-cloop-2 lanes-cloop-4 lanes-cloop-8 lanes-cloop-16"
```

## Results

The latest run on the warm machine.

- Date: 2026-11-27. Commit: 70d61f52d0aa.
- Machine: c7a.16xlarge (64 vCPUs), the server and the load generator pinned to disjoint
  halves of its CPUs.
- Settings: `GET /` answered with `hello\n`, keep-alive, 1, 16 and 64 connections; the
  workflow's defaults (three runs of 10 s after a 1 s warm-up, medians; `LEAN_NUM_THREADS` the
  server's CPUs).

Requests a second:

| Server | 1 | 16 | 64 | Server CPU |
| --- | ---: | ---: | ---: | --- |
| `go` (Go `net/http`) | 29,870 | 125,809 | 137,938 | up to 12.8 cores |
| `lanes` | 11,395 | 34,516 | 37,098 | 3.2 cores, 85–101 µs a request |
| `lanes-journal` (every request synced before it is answered) | 344 | 2,393 | 8,632 | |

At 64 connections Lanes answers about a quarter of what Go does (3.7×). `lanes` is one actor on
one shard, and a shard is one thread, so the application's logic uses one core whatever the
number of connections; the IO path and running actors in parallel are the next steps.
`lanes-journal` syncs the journal once a batch before it answers, and a batch is what has
arrived since the last, so more connections share a sync.

### Parallel actors and IO threads on the warm machine (2026-11-27, commit baec29b81c11)

Same machine and settings as above; `IO_THREADS` and `WORKERS` 8 (a quarter of the server's 32
CPUs). Requests a second at 1 / 16 / 64 connections, CPU µs a request at 64.

| server | req/s | CPU µs/req |
| --- | --- | ---: |
| `go` | 29,926 / 125,774 / 139,730 | 93 |
| `lanes` | 10,518 / 34,223 / 37,177 | 85 |
| `lanes-io` | 13,719 / 42,482 / 45,088 | 60 |
| `lanes-par` | 10,671 / 33,975 / 36,790 | 89 |
| `lanes-io-par` | 11,529 / 40,600 / 44,335 | 62 |
| `lanes-many` | 10,992 / 34,715 / 37,474 | 89 |
| `lanes-many-par` | 10,451 / 29,755 / 33,798 | 114 |
| `lanes-heavy` | 7,530 / 20,524 / 20,453 | 142 |
| `lanes-heavy-par` | 7,351 / 28,670 / 31,921 | 147 |

IO threads gain 21–30% and cut CPU a request by a quarter. Parallel actors gain 40–56% when each
step does real work (`heavy`) and cost about 10% when steps are trivial (`many`), so `workers`
stays 1 by default until the shell chooses it from its own timing.
