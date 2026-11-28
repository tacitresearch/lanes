#!/usr/bin/env bash
# The service oracles of the store models against a PostgreSQL made for the run: the key-value
# store (`store`) and the typed store (`db`):
#
#   oracles/postgres/run.sh [--record]
#
# It makes a cluster with scripts/postgres-test-server in a new directory, on a free port, runs
# `lake exe lanesServiceOracle store db` against it, then stops the cluster with pg_ctl and removes
# it. PostgreSQL's binaries must be on PATH or in /usr/lib/postgresql/<version>/bin; run as root,
# the cluster is made and run by the user postgres. Without PostgreSQL it says it is skipped.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
if ! command -v initdb >/dev/null; then
  for bin in /usr/lib/postgresql/*/bin; do
    if [ -x "$bin/initdb" ]; then PATH="$bin:$PATH"; fi
  done
fi
if ! command -v initdb >/dev/null; then
  echo "store: skipped, no PostgreSQL: initdb is not on PATH or in /usr/lib/postgresql"
  exit 0
fi
dir=$(mktemp -d "${TMPDIR:-/tmp}/lanes-postgres.XXXXXX")
as=()
if [ "$(id -u)" = 0 ]; then
  chown postgres "$dir"
  as=(runuser -u postgres --)
fi
port=$(python3 -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
stop() {
  "${as[@]}" env PATH="$PATH" pg_ctl -D "$dir/data" -m fast stop >/dev/null 2>&1 || true
  rm -rf "$dir"
}
trap stop EXIT
"${as[@]}" env PATH="$PATH" bash "$root/scripts/postgres-test-server" "$dir" "$port"
initdb --version
cd "$root"
LANES_POSTGRES="127.0.0.1:$port" lake exe lanesServiceOracle store db "$@"
