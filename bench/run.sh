#!/usr/bin/env bash
# Runs every server in the matrix against the load generator and appends one JSON line per run
# to results/<stamp>.jsonl, then prints the summary table.
#
#   ./run.sh                      everything: 3 runs of 10 s at 1, 16 and 64 connections
#   RUNS=1 SECONDS_EACH=3 ./run.sh go std lanes     a quick look at some servers
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:/usr/local/go/bin:$PATH"

RUNS=${RUNS:-3}
SECONDS_EACH=${SECONDS_EACH:-10}
CONNS=${CONNS:-"1 16 64"}
SERVERS=("$@")
if [ ${#SERVERS[@]} -eq 0 ]; then
  SERVERS=(go1 go tcp std std-unlimited lanes lanes-journal lanes-snapshot)
fi

(cd go && go build -o ../.build/ ./...)
lake build
BIN=.lake/build/bin
PORT=18100
SCRATCH=$(mktemp -d /tmp/lanesbench.XXXXXX)
mkdir -p results
OUT=results/$(date -u +%Y%m%dT%H%M%SZ).jsonl
TICK=$(getconf CLK_TCK)
pid=
trap '[ -n "$pid" ] && kill "$pid" 2>/dev/null; rm -rf "$SCRATCH"' EXIT

cpu_ticks() { awk '{print $14 + $15}' "/proc/$1/stat"; }

start_server() {
  local name=$1 port=$2
  rm -f "$SCRATCH"/j*
  case $name in
    go1) GOMAXPROCS=1 exec .build/hello -port "$port" ;;
    go) exec .build/hello -port "$port" ;;
    tcp) exec "$BIN/benchTcp" "$port" ;;
    std) exec "$BIN/benchStd" "$port" ;;
    std-unlimited) exec "$BIN/benchStd" "$port" 1000000000 ;;
    lanes) exec "$BIN/benchLanes" "$port" ;;
    lanes-journal) exec "$BIN/benchLanes" "$port" "$SCRATCH/j" ;;
    lanes-snapshot) exec "$BIN/benchLanes" "$port" "$SCRATCH/j" 1024 ;;
    *) echo "unknown server $name" >&2; exit 2 ;;
  esac
}

for name in "${SERVERS[@]}"; do
  for conns in $CONNS; do
    for run in $(seq 1 "$RUNS"); do
      PORT=$((PORT + 1))
      start_server "$name" "$PORT" > /dev/null 2>&1 &
      pid=$!
      for _ in $(seq 1 100); do
        (exec 3<>/dev/tcp/127.0.0.1/$PORT) 2>/dev/null && break
        sleep 0.05
      done
      load=$(cut -d' ' -f1 /proc/loadavg)
      .build/load -addr "127.0.0.1:$PORT" -c "$conns" -d "${SECONDS_EACH}s" -warmup 1s -json \
        > "$SCRATCH/load.json" &
      lpid=$!
      sleep 1
      before=$(cpu_ticks "$pid")
      wait "$lpid"
      after=$(cpu_ticks "$pid")
      rss=$(awk '/VmHWM/ {print $2}' "/proc/$pid/status")
      threads=$(awk '/Threads/ {print $2}' "/proc/$pid/status")
      journal=$(cat "$SCRATCH"/j "$SCRATCH"/j.snapshot 2>/dev/null | wc -c || true)
      kill "$pid"
      wait "$pid" 2>/dev/null || true
      pid=
      cpu=$(awk -v a="$before" -v b="$after" -v t="$TICK" 'BEGIN {printf "%.2f", (b - a) / t}')
      printf '{"server":"%s","run":%d,"load1":%s,"cpu_s":%s,"rss_kb":%s,"threads":%s,"journal_bytes":%s,"load":%s}\n' \
        "$name" "$run" "$load" "$cpu" "$rss" "$threads" "$journal" "$(cat "$SCRATCH/load.json")" \
        | tee -a "$OUT"
    done
  done
done
pid=
echo "results in $OUT"
.build/summary "$OUT"
