#!/usr/bin/env bash
# Runs servers against the load generator, the two pinned to disjoint CPUs, and writes
# results/<date>-<commit>.md (the table), .json (the table, the machine and every run) and
# .jsonl (one line a run). See README.md.
#
#   ./run.sh                                   every server: 3 runs of 10 s at 1, 16 and 64 connections
#   RUNS=1 SECONDS_EACH=2 ./run.sh go std lanes   a quick look at some servers
#
# Settings, from the environment:
#   RUNS (3), SECONDS_EACH (10), WARMUP_SECONDS (1), CONNS ("1 16 64")
#   SERVER_CPUS, LOAD_CPUS   CPU lists for taskset; by default the first and second half of the
#                            CPUs this process may use
#   IDLE_CORES (1.0)         CPU, in cores, that other processes may use before a run counts as disturbed
#   IDLE_WAIT_MINUTES (0)    how long to wait at the start for the machine to be idle
#   REQUIRE_IDLE (0)         1: exit 3 if the machine is not idle at the start, 4 if a run was disturbed
#   BUILD (1)                0: use the binaries already built
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:/usr/local/go/bin:$PATH"
. ./servers.sh

RUNS=${RUNS:-3}
SECONDS_EACH=${SECONDS_EACH:-10}
WARMUP_SECONDS=${WARMUP_SECONDS:-1}
CONNS=${CONNS:-"1 16 64"}
IDLE_CORES=${IDLE_CORES:-1.0}
IDLE_WAIT_MINUTES=${IDLE_WAIT_MINUTES:-0}
REQUIRE_IDLE=${REQUIRE_IDLE:-0}
SERVERS=("$@")
[ ${#SERVERS[@]} -gt 0 ] || SERVERS=("${ALL_SERVERS[@]}")
for name in "${SERVERS[@]}"; do server_argv "$name" 0 /nonexistent; done

# "0-2,5" -> "0 1 2 5"
expand_cpus() {
  local part c out=()
  IFS=, read -ra parts <<<"$1"
  for part in "${parts[@]}"; do
    for ((c = ${part%-*}; c <= ${part#*-}; c++)); do out+=("$c"); done
  done
  echo "${out[@]}"
}
join_cpus() { local IFS=,; echo "$*"; }

read -ra allowed <<<"$(expand_cpus "$(awk '/^Cpus_allowed_list/ {print $2}' /proc/self/status)")"
if [ -z "${SERVER_CPUS:-}" ] || [ -z "${LOAD_CPUS:-}" ]; then
  if [ ${#allowed[@]} -lt 2 ]; then
    echo "run.sh: one CPU only; the server and the load generator share it" >&2
    SERVER_CPUS=${allowed[0]} LOAD_CPUS=${allowed[0]}
  else
    half=$(( ${#allowed[@]} / 2 ))
    SERVER_CPUS=$(join_cpus "${allowed[@]:0:half}")
    LOAD_CPUS=$(join_cpus "${allowed[@]:half}")
  fi
fi
read -ra server_cpus <<<"$(expand_cpus "$SERVER_CPUS")"
# Lean's runtime sizes its thread pool from the machine's CPUs, not from its affinity mask, as
# Go does; this gives it as many workers as it has CPUs.
export LEAN_NUM_THREADS=${#server_cpus[@]}

# Runner.Worker is the process of a GitHub Actions job: one is this job (if any), others are
# jobs that other runners on the machine took.
other_jobs() {
  local p=$$ mine=0 n
  while [ "$p" -gt 1 ]; do
    [ "$(cat "/proc/$p/comm" 2>/dev/null)" = Runner.Worker ] && mine=1
    p=$(sed 's/.*) //' "/proc/$p/stat" 2>/dev/null | cut -d' ' -f2) || break
    [ -n "$p" ] || break
  done
  n=$(grep -lx Runner.Worker /proc/[0-9]*/comm 2>/dev/null | wc -l || true)
  echo $(( n - mine ))
}

busy_ticks() { awk '/^cpu / {print $2 + $3 + $4}' /proc/stat; }

# CPU, in cores, that the machine spends over 5 s while this script only sleeps.
busy_cores() {
  local a b
  a=$(busy_ticks); sleep 5; b=$(busy_ticks)
  awk -v a="$a" -v b="$b" -v t="$(getconf CLK_TCK)" 'BEGIN {printf "%.2f", (b - a) / t / 5}'
}

idle_now() {
  start_jobs=$(other_jobs)
  start_cores=$(busy_cores)
  echo "run.sh: $start_jobs other jobs, $start_cores cores busy, load $(cut -d' ' -f1-3 /proc/loadavg)" >&2
  [ "$start_jobs" -eq 0 ] && awk -v c="$start_cores" -v m="$IDLE_CORES" 'BEGIN {exit !(c <= m)}'
}

# bench/.lake/packages is the repository's (README.md): a dependency pinned at another commit
# here would make Lake check that commit out there.
python3 - <<'EOF'
import json, sys
pins = lambda path: {p["name"]: p.get("rev") for p in json.load(open(path))["packages"]}
root, here = pins("../lake-manifest.json"), pins("lake-manifest.json")
here.pop("lanes", None)
if root != here:
    sys.exit("run.sh: bench/lake-manifest.json does not pin what lake-manifest.json pins: "
             + ", ".join(sorted(k for k in root.keys() | here.keys() if root.get(k) != here.get(k))))
EOF

if [ "${BUILD:-1}" = 1 ]; then
  (cd go && go build -o ../.build/ ./...)
  lake build
fi

deadline=$(( $(date +%s) + IDLE_WAIT_MINUTES * 60 ))
idle=true
until idle_now; do
  if [ "$(date +%s)" -ge "$deadline" ]; then idle=false; break; fi
  sleep 25
done
if [ "$idle" = false ]; then
  echo "run.sh: the machine is not idle" >&2
  [ "$REQUIRE_IDLE" = 1 ] && exit 3
fi

SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/lanesbench.XXXXXX")
pid=
trap '[ -n "$pid" ] && kill "$pid" 2>/dev/null; rm -rf "$SCRATCH"' EXIT
mkdir -p results
commit=$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)
[ -z "$(git status --porcelain --untracked-files=no 2>/dev/null)" ] || commit="$commit-dirty"
base=results/$(date -u +%Y-%m-%d)-$commit
[ ! -e "$base.jsonl" ] || base="$base-$(date -u +%H%M%S)"
: > "$base.jsonl"

jstr() { printf '"%s"' "$(printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g')"; }
{
  echo "{"
  echo "\"date\": $(jstr "$(date -u +%Y-%m-%dT%H:%M:%SZ)"),"
  echo "\"commit\": $(jstr "$commit"),"
  echo "\"cpu\": $(jstr "$(awk -F': ' '/^model name/ {print $2; exit}' /proc/cpuinfo)"),"
  echo "\"cpus\": ${#allowed[@]},"
  echo "\"kernel\": $(jstr "$(uname -r)"),"
  echo "\"go\": $(jstr "$(go version | cut -d' ' -f3)"),"
  echo "\"lean\": $(jstr "$(cat lean-toolchain)"),"
  echo "\"server_cpus\": $(jstr "$SERVER_CPUS"),"
  echo "\"load_cpus\": $(jstr "$LOAD_CPUS"),"
  echo "\"lean_num_threads\": $LEAN_NUM_THREADS,"
  echo "\"runs\": $RUNS, \"seconds\": $SECONDS_EACH, \"warmup_seconds\": $WARMUP_SECONDS,"
  echo "\"conns\": $(jstr "$CONNS"),"
  echo "\"idle_at_start\": $idle,"
  echo "\"other_jobs_at_start\": $start_jobs, \"busy_cores_at_start\": $start_cores,"
  echo "\"runner\": $(jstr "${RUNNER_NAME:-local}")"
  echo "}"
} > "$base.machine.json"

port=$((18100 + RANDOM % 1000))
for name in "${SERVERS[@]}"; do
  for conns in $CONNS; do
    for run in $(seq 1 "$RUNS"); do
      port=$((port + 1))
      rm -f "$SCRATCH"/j*
      server_argv "$name" "$port" "$SCRATCH"
      taskset -c "$SERVER_CPUS" "${SERVER[@]}" > "$SCRATCH/server.log" 2>&1 &
      pid=$!
      if ! wait_port "$port"; then
        echo "run.sh: $name did not listen on $port:" >&2
        cat "$SCRATCH/server.log" >&2
        exit 1
      fi
      run_jobs=$(other_jobs)
      load1=$(cut -d' ' -f1 /proc/loadavg)
      taskset -c "$LOAD_CPUS" .build/load -addr "127.0.0.1:$port" -c "$conns" \
        -d "${SECONDS_EACH}s" -warmup "${WARMUP_SECONDS}s" -pid "$pid" \
        -cpus "$SERVER_CPUS,$LOAD_CPUS" -json > "$SCRATCH/load.json"
      alive=true
      kill -0 "$pid" 2>/dev/null || alive=false
      journal=$(cat "$SCRATCH"/j "$SCRATCH"/j.snapshot 2>/dev/null | wc -c || true)
      kill "$pid" 2>/dev/null || true
      wait "$pid" 2>/dev/null || true
      pid=
      printf '{"server":"%s","run":%d,"load1":%s,"other_jobs":%d,"journal_bytes":%s,"alive":%s,"load":%s}\n' \
        "$name" "$run" "$load1" "$run_jobs" "$journal" "$alive" "$(cat "$SCRATCH/load.json")" \
        | tee -a "$base.jsonl"
    done
  done
done

.build/summary -machine "$base.machine.json" -idle-cores "$IDLE_CORES" \
  -md "$base.md" -json "$base.json" "$base.jsonl"
rm -f "$base.machine.json"
cat "$base.md"
echo "results in $base.md and $base.json"
disturbed=$(grep -o '"disturbed_runs": [0-9]*' "$base.json" | head -1 | grep -o '[0-9]*$')
if [ "$disturbed" -gt 0 ] && [ "$REQUIRE_IDLE" = 1 ]; then exit 4; fi
