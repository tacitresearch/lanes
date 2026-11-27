# The servers of the benchmark, sourced by run.sh and profile.sh from bench/.
# shellcheck shell=bash

# Every server, in the order run.sh runs them.
ALL_SERVERS=(go1 go tcp tcp-park std std-unlimited lanes lanes-journal lanes-snapshot)

# Sets SERVER to the command that runs server <name> on <port>, keeping any journal in <dir>.
# shellcheck disable=SC2034
server_argv() {
  local name=$1 port=$2 dir=$3 bin=.lake/build/bin
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
