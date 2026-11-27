#!/bin/bash
# Runs the command line of the systemd unit app-instance.sh writes, on this machine, against a
# built Lanes executable, with the unit's environment, to show that its arguments and paths work:
# the executable starts in its journal's directory, answers, writes its journal there, stops at
# SIGTERM, and starts again on the same journal. It runs as you, without systemd, so the unit's
# sandboxing is not tried.
#
#   infra/app/smoke.sh BINARY [ARGS] [PATH]
#
# ARGS is the stack's AppArguments ("{port} {journal}" by default) and PATH the page that must
# answer 200 (/ by default; /readyz once the application configures ServerConfig.ops).
set -euo pipefail

binary=$(realpath "${1:?the executable to run, such as examples/counter/.lake/build/bin/counter}")
args=${2:-"{port} {journal}"}
path=${3:-/}
here=$(dirname "$(realpath "$0")")
work=$(mktemp -d)
pid=""
stop() { if [ -n "$pid" ]; then kill -KILL "$pid" 2>/dev/null || true; fi; }
trap stop EXIT

say() { echo "smoke: $*"; }
die() { say "FAIL: $*"; exit 1; }

port=$(python3 -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
name=$(basename "$binary")
export BASE=$work/opt DATA=$work/srv CONF=$work/app.conf
mkdir -p "$BASE/releases/smoke" "$DATA/journal"
cp "$binary" "$BASE/releases/smoke/$name"
ln -s "$BASE/releases/smoke" "$BASE/current"
printf '%s=%q\n' APP smoke BINARY "$name" ARGS "$args" PORT "$port" READY_PATH "$path" >"$CONF"

"$here/app-instance.sh" unit >"$work/lanes-app.service"
command=$(sed -n 's/^ExecStart=//p' "$work/lanes-app.service")
directory=$(sed -n 's/^WorkingDirectory=//p' "$work/lanes-app.service")
writable=$(sed -n 's/^ReadWritePaths=//p' "$work/lanes-app.service")
environment=$(sed -n 's/^Environment=//p' "$work/lanes-app.service")
say "Environment=$environment"
say "ExecStart=$command"
[ "$directory" = "$writable" ] || die "the working directory $directory is not the writable one, $writable"
if command -v systemd-analyze >/dev/null; then
  # The other units are not there, and neither is the user: only the unit's own syntax counts.
  systemd-analyze verify --man=no "$work/lanes-app.service" 2>&1 \
    | grep -v -e 'lanes-volume.service' -e 'Failed to resolve user' -e '^$' >&2 || true
fi

start() {
  read -r -a argv <<<"$command"
  read -r -a vars <<<"$environment"
  (cd "$directory" && exec env "${vars[@]}" "${argv[@]}") >>"$work/out.log" 2>&1 &
  pid=$!
  for _ in $(seq 1 100); do
    if curl -fs -o /dev/null --max-time 2 "http://127.0.0.1:$port$path"; then return 0; fi
    kill -0 "$pid" 2>/dev/null || { cat "$work/out.log" >&2; die "it exited before answering"; }
    sleep 0.2
  done
  die "nothing answered 200 at http://127.0.0.1:$port$path in 20 s"
}

term() {
  status=0
  kill -TERM "$pid"
  wait "$pid" || status=$?
  pid=""
}

start
say "answered 200 at $path"
journal=$(find "$directory" -maxdepth 1 -type f -name '*.journal' | head -1)
[ -n "$journal" ] && [ -s "$journal" ] || die "no journal was written in $directory"
say "journal $journal, $(stat -c %s "$journal") bytes, beside: $(find "$directory" -mindepth 1 -maxdepth 1 -printf "%f ")"
term
case "$status" in
  0) say "SIGTERM: it drained and stopped, status 0" ;;
  143) say "SIGTERM ended it at once (status 143: its main does not call Server.stopOnSignal)" ;;
  *) die "SIGTERM: status $status" ;;
esac
start
say "started again on the same journal and answered 200"
term
say "PASS (the files are in $work)"
