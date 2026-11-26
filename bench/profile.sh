#!/usr/bin/env bash
# Where a server's time goes, without perf: ./profile.sh <what> <server> [conns] [seconds]
#
#   threads    CPU seconds of each thread of the server during a run
#   syscalls   system calls per request, from strace -c -f
#   callgrind  instructions per request by function, from valgrind --tool=callgrind
#
# <server> is a name of run.sh (go, tcp, std, lanes, lanes-journal, ...). Build with run.sh first.
set -euo pipefail
cd "$(dirname "$0")"
WHAT=$1
NAME=$2
CONNS=${3:-16}
SECONDS_EACH=${4:-5}
BIN=.lake/build/bin
PORT=$((18900 + RANDOM % 50))
SCRATCH=$(mktemp -d /tmp/lanesprofile.XXXXXX)
pid=
trap '[ -n "$pid" ] && kill "$pid" 2>/dev/null; rm -rf "$SCRATCH"' EXIT

command_of() {
  case $1 in
    go1) echo "env GOMAXPROCS=1 .build/hello -port $PORT" ;;
    go) echo ".build/hello -port $PORT" ;;
    tcp) echo "$BIN/benchTcp $PORT" ;;
    std) echo "$BIN/benchStd $PORT" ;;
    std-unlimited) echo "$BIN/benchStd $PORT 1000000000" ;;
    lanes) echo "$BIN/benchLanes $PORT" ;;
    lanes-journal) echo "$BIN/benchLanes $PORT $SCRATCH/j" ;;
    lanes-snapshot) echo "$BIN/benchLanes $PORT $SCRATCH/j 1024" ;;
    *) echo "unknown server $1" >&2; exit 2 ;;
  esac
}

wait_port() {
  for _ in $(seq 1 600); do
    (exec 3<>/dev/tcp/127.0.0.1/$PORT) 2>/dev/null && return
    sleep 0.1
  done
  echo "the server did not start" >&2
  exit 1
}

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
    # shellcheck disable=SC2046
    exec_cmd=$(command_of "$NAME")
    $exec_cmd > /dev/null 2>&1 &
    pid=$!
    wait_port
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
    $(command_of "$NAME") > /dev/null 2>&1 &
    pid=$!
    wait_port
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
    # shellcheck disable=SC2046
    valgrind --tool=callgrind --callgrind-out-file="$out" --dump-instr=no \
      $(command_of "$NAME") > /dev/null 2> "$SCRATCH/valgrind.txt" &
    pid=$!
    wait_port
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
    last=$(ls -t "$out"* | head -1)
    callgrind_annotate --inclusive=yes "$last" | head -60 | awk -v n="$requests" '
      /^ *[0-9,]+ / { ir = $1; gsub(",", "", ir); printf "%12.0f instr/req  %s\n", ir / n, $0; next } { print }'
    ;;
  *)
    echo "usage: ./profile.sh threads|syscalls|callgrind <server> [conns] [seconds]" >&2
    exit 2
    ;;
esac
