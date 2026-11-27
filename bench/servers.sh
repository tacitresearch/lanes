# The servers of the benchmark, sourced by run.sh and profile.sh from bench/.
# shellcheck shell=bash

# Every server, in the order run.sh runs them. lanes-io-N and lanes-cloop-N, not in the list, are
# lanes-io and lanes-cloop on N threads whatever IO_THREADS is.
ALL_SERVERS=(go1 go tcp tcp-park std std-unlimited lanes lanes-journal lanes-snapshot
  lanes-io lanes-cloop lanes-par lanes-io-par lanes-many lanes-many-par lanes-many-auto lanes-heavy
  lanes-heavy-par lanes-heavy-auto)

# The threads of the servers that run in parallel: IO_THREADS run connections
# (ServerConfig.ioThreads; in lanes-cloop, threads of the C loop) and WORKERS work out actors' steps (Runtime.Config.workers); by default
# a quarter of LEAN_NUM_THREADS each, which run.sh sets to the server's CPUs. K actors in
# lanes-many* and lanes-heavy*, and SPIN rounds of hashing in each step of lanes-heavy*.
K=${K:-64}
SPIN=${SPIN:-20000}
quarter_cpus() { local n=$(( ${LEAN_NUM_THREADS:-4} / 4 )); echo $(( n > 0 ? n : 1 )); }

# Sets SERVER to the command that runs server <name> on <port>, keeping any journal in <dir>.
# shellcheck disable=SC2034
server_argv() {
  local name=$1 port=$2 dir=$3 bin=.lake/build/bin
  local io=${IO_THREADS:-$(quarter_cpus)} workers=${WORKERS:-$(quarter_cpus)}
  case $name in
    go1) SERVER=(env GOMAXPROCS=1 .build/hello -port "$port") ;;
    go) SERVER=(.build/hello -port "$port") ;;
    tcp) SERVER=("$bin/benchTcp" "$port") ;;
    tcp-park) SERVER=("$bin/benchTcp" "$port" park) ;;
    std) SERVER=("$bin/benchStd" "$port") ;;
    std-unlimited) SERVER=("$bin/benchStd" "$port" 1000000000) ;;
    lanes) SERVER=("$bin/benchLanes" "$port") ;;
    lanes-journal) SERVER=("$bin/benchLanes" "$port" "$dir/j") ;;
    lanes-snapshot) SERVER=("$bin/benchLanes" "$port" "$dir/j" 1024) ;;
    lanes-io) SERVER=("$bin/benchLanes" "$port" "io=$io") ;;
    lanes-cloop) SERVER=("$bin/benchLanes" "$port" "io=$io" loop=c) ;;
    lanes-cloop-[0-9]*) SERVER=("$bin/benchLanes" "$port" "io=${name#lanes-cloop-}" loop=c) ;;
    lanes-io-[0-9]*) SERVER=("$bin/benchLanes" "$port" "io=${name#lanes-io-}") ;;
    lanes-par) SERVER=("$bin/benchLanes" "$port" "workers=$workers") ;;
    lanes-io-par) SERVER=("$bin/benchLanes" "$port" "io=$io" "workers=$workers") ;;
    lanes-many) SERVER=("$bin/benchMany" "$port" "$K" 0) ;;
    lanes-many-par) SERVER=("$bin/benchMany" "$port" "$K" 0 "workers=$workers") ;;
    lanes-many-auto) SERVER=("$bin/benchMany" "$port" "$K" 0 "workers=$workers" parallel=auto) ;;
    lanes-heavy) SERVER=("$bin/benchMany" "$port" "$K" "$SPIN") ;;
    lanes-heavy-par) SERVER=("$bin/benchMany" "$port" "$K" "$SPIN" "workers=$workers") ;;
    lanes-heavy-auto)
      SERVER=("$bin/benchMany" "$port" "$K" "$SPIN" "workers=$workers" parallel=auto) ;;
    *) echo "unknown server $name; the servers are ${ALL_SERVERS[*]}" >&2; return 2 ;;
  esac
}

# Waits up to 30 s for something to listen on <port>.
wait_port() {
  for _ in $(seq 1 300); do
    (exec 3<>"/dev/tcp/127.0.0.1/$1") 2>/dev/null && return 0
    sleep 0.1
  done
  return 1
}
