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
| `std` | `Std.Http.Server` with its default configuration, which is what Lanes runs; it closes a connection after 100 requests | `StdHello.lean` |
| `std-unlimited` | `std` with no limit of requests per connection | `StdHello.lean` |
| `lanes` | `Lanes.Http.serve` with one actor (`Server.system`) that answers each request; no journal | `LanesHello.lean` |
| `lanes-journal` | `lanes` with a journal: every request is appended and synced (`fsync`, `Lanes/Env/Journal.lean`) before it is answered; the journal only grows | `LanesHello.lean` |
| `lanes-snapshot` | `lanes-journal`, also saving the kernel and cutting the journal every 1024 inputs | `LanesHello.lean` |

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
machine's CPU count, so `run.sh` sets `LEAN_NUM_THREADS` to the number of the server's CPUs.

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
`syscalls` (system calls a request, from `strace`) and `callgrind` (instructions a request by
function). For example `bench/profile.sh syscalls lanes 16 5`.

Through GitHub: **Actions → Bench → Run workflow** (`.github/workflows/bench.yml`), or
`gh workflow run bench.yml -f seconds=10 -f runs=3`. Inputs: `seconds`, `runs`, `servers` (all
when empty), `require-idle` (on), `idle-wait-minutes` (30) and `hosted`. It runs where the
mutation gate runs (`docs/RUNNERS.md`): with the AWS variables set, on the warm machine, which
it starts and, when no other run needs it, stops. The report is in the run's summary and in the
artifact `bench-<run>-<attempt>`.

The warm machine has 16 runners, and the others may take jobs while the benchmark runs. With
`require-idle`, `run.sh` waits for the machine to have no other job and at most a core of
other CPU, fails if it does not within `idle-wait-minutes`, and fails at the end if any run was
disturbed; the report is uploaded either way. Two runs of the benchmark never overlap (one
concurrency group). A machine launched for the run (`LANES_AWS_INSTANCE_TYPE`) has no other
jobs. On `ubuntu-latest` (4 vCPUs) the workflow runs, but its numbers are no results.

## Results

None yet. The first run on the warm machine (c7a.16xlarge, 64 cores) goes here: its
`results/<date>-<commit>.md`, the commit, and what it shows.
