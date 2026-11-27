#!/usr/bin/env bash
# Where a server's time goes, without perf: ./profile.sh <what> <server> [conns] [seconds]
#
#   threads    CPU seconds of each thread of the server during a run
#   syscalls   system calls per request, from strace -c -f
#   callgrind  instructions per request by function, from valgrind --tool=callgrind
#   perf       context switches per request and where the CPU goes, from perf ($PERF, or perf)
#
# <server> is a name of run.sh (go, tcp, std, lanes, lanes-journal, ...). Build with run.sh first.
set -euo pipefail
cd "$(dirname "$0")"
. ./servers.sh
WHAT=$1
NAME=$2
CONNS=${3:-16}
SECONDS_EACH=${4:-5}
PORT=$((18900 + RANDOM % 50))
SCRATCH=$(mktemp -d /tmp/lanesprofile.XXXXXX)
pid=
trap '[ -n "$pid" ] && kill "$pid" 2>/dev/null; rm -rf "$SCRATCH"' EXIT
server_argv "$NAME" "$PORT" "$SCRATCH"

load() {
  .build/load -addr "127.0.0.1:$PORT" -c "$CONNS" -d "${SECONDS_EACH}s" -warmup 1s "$@"
}

thread_ticks() {
  for t in /proc/"$pid"/task/*; do
    echo "$(basename "$t") $(cat "$t/comm" | tr ' ' '_') $(awk '{print $14 + $15}' "$t/stat")"
  done | sort
}

case $WHAT in
  threads)
    "${SERVER[@]}" > /dev/null 2>&1 &
    pid=$!
    wait_port "$PORT" || { echo "the server did not start" >&2; exit 1; }
    load > "$SCRATCH/load.txt" &
    lpid=$!
    sleep 1
    thread_ticks > "$SCRATCH/before"
    wait "$lpid"
    thread_ticks > "$SCRATCH/after"
    cat "$SCRATCH/load.txt"
    echo "CPU seconds per thread over the measured window (tid name seconds):"
    join "$SCRATCH/before" "$SCRATCH/after" | awk -v t="$(getconf CLK_TCK)" \
      '{d = ($5 - $3) / t; if (d > 0) printf "%s %s %.2f\n", $1, $2, d}' | sort -k3 -nr
    ;;
  syscalls)
    "${SERVER[@]}" > /dev/null 2>&1 &
    pid=$!
    wait_port "$PORT" || { echo "the server did not start" >&2; exit 1; }
    strace -f -c -p "$pid" -o "$SCRATCH/strace.txt" &
    spid=$!
    sleep 0.5
    load -json > "$SCRATCH/load.json"
    kill -INT "$spid"
    wait "$spid" || true
    requests=$(grep -o '"requests":[0-9]*' "$SCRATCH/load.json" | cut -d: -f2)
    echo "$requests requests under strace; calls per request:"
    awk -v n="$requests" '$1 ~ /^[0-9.]+$/ && NF >= 5 {calls = $4; name = $NF; if (calls / n >= 0.01) printf "%-20s %8.2f\n", name, calls / n}' \
      "$SCRATCH/strace.txt" | sort -k2 -nr
    ;;
  callgrind)
    out=${OUT:-callgrind.$NAME.out}
    valgrind --tool=callgrind --callgrind-out-file="$out" --dump-instr=no \
      "${SERVER[@]}" > /dev/null 2> "$SCRATCH/valgrind.txt" &
    pid=$!
    wait_port "$PORT" || { echo "the server did not start" >&2; exit 1; }
    load -warmup 2s > /dev/null
    callgrind_control -z "$pid" > /dev/null
    load -json -warmup 0s > "$SCRATCH/load.json"
    callgrind_control -d "$pid" > /dev/null
    sleep 1
    kill "$pid"
    wait "$pid" || true
    pid=
    requests=$(grep -o '"requests":[0-9]*' "$SCRATCH/load.json" | cut -d: -f2)
    echo "$requests requests measured; the last dump is the measured window:"
    # shellcheck disable=SC2012
    last=$(ls -t "$out"* | head -1)
    callgrind_annotate --inclusive=yes "$last" | head -60 | awk -v n="$requests" '
      /^ *[0-9,]+ / { ir = $1; gsub(",", "", ir); printf "%12.0f instr/req  %s\n", ir / n, $0; next } { print }'
    ;;
  perf)
    perf=${PERF:-perf}
    "${SERVER[@]}" > /dev/null 2>&1 &
    pid=$!
    wait_port "$PORT" || { echo "the server did not start" >&2; exit 1; }
    load -json > "$SCRATCH/load.json" &
    lpid=$!
    sleep 1
    "$perf" stat -e context-switches -x, -o "$SCRATCH/stat.txt" -p "$pid" -- sleep "$SECONDS_EACH" &
    statpid=$!
    "$perf" record -F 999 -g -o "$SCRATCH/perf.data" -p "$pid" -- sleep "$SECONDS_EACH" 2> /dev/null
    wait "$lpid" "$statpid"
    requests=$(grep -o '"requests":[0-9]*' "$SCRATCH/load.json" | cut -d: -f2)
    awk -F, -v n="$requests" '$3 == "context-switches" {
      printf "%d requests measured; %.1f context switches a request\n", n, $1 / n }' "$SCRATCH/stat.txt"
    "$perf" report -i "$SCRATCH/perf.data" --no-children --sort dso,sym --stdio -g none 2> /dev/null \
      | grep '%' | head -40
    ;;
  *)
    echo "usage: ./profile.sh threads|syscalls|callgrind|perf <server> [conns] [seconds]" >&2
    exit 2
    ;;
esac
