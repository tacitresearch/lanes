#!/usr/bin/env bash
# Runs benchMixed (Mixed.lean: mixed step costs at p99, the shell serial, in waves and auto, and
# free-running actors) pinned to the first half of the CPUs this process may use, and writes
# results/<date>-<commit>-mixed.md. See README.md, "Mixed step costs".
#
#   ./mixed.sh                   5 runs of 64,000 requests, WORKERS a quarter of the CPUs
#
# Settings, from the environment: RUNS (5), REQUESTS (64000), WORKERS, CPUS (a taskset list),
# BUILD (1). LEAN_NUM_THREADS is the number of CPUs used unless it is set.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

read -ra allowed <<<"$(awk '/^Cpus_allowed_list/ {print $2}' /proc/self/status | tr ',' ' ')"
count=0
for part in "${allowed[@]}"; do count=$(( count + ${part#*-} - ${part%-*} + 1 )); done
half=$(( count > 1 ? count / 2 : 1 ))
CPUS=${CPUS:-0-$(( half - 1 ))}
WORKERS=${WORKERS:-$(( count / 4 > 1 ? count / 4 : 2 ))}
RUNS=${RUNS:-5}
REQUESTS=${REQUESTS:-64000}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-$half}

[ "${BUILD:-1}" = 0 ] || lake build benchMixed

mkdir -p results
commit=$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)
out=results/$(date -u +%Y-%m-%d)-$commit-mixed.md
{
  echo "## Mixed step costs (benchMixed)"
  echo
  echo "- Machine: $(nproc) CPUs, $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ //')"
  echo "- CPUs $CPUS, $WORKERS workers, LEAN_NUM_THREADS=$LEAN_NUM_THREADS, $RUNS runs of $REQUESTS requests"
  echo "- Load before: $(cut -d' ' -f1-3 /proc/loadavg)"
  echo
  taskset -c "$CPUS" .lake/build/bin/benchMixed "$WORKERS" "$RUNS" "$REQUESTS"
  echo
  echo "- Load after: $(cut -d' ' -f1-3 /proc/loadavg)"
} | tee "$out"
