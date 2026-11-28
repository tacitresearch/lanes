#!/usr/bin/env bash
# The service oracles of the store models against a PostgreSQL made for the run: the key-value
# store (`store`) and the typed store (`db`):
#
#   oracles/postgres/run.sh [--record]
#
# It runs `lake exe lanesServiceOracle store db` under scripts/with-postgres, which makes a
# cluster with scripts/postgres-test-server, names it in LANES_POSTGRES, and stops and removes it
# after. PostgreSQL's binaries must be on PATH or in /usr/lib/postgresql/<version>/bin. Without
# PostgreSQL it says it is skipped.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
if ! command -v initdb >/dev/null && ! ls /usr/lib/postgresql/*/bin/initdb >/dev/null 2>&1; then
  echo "store: skipped, no PostgreSQL: initdb is not on PATH or in /usr/lib/postgresql"
  exit 0
fi
cd "$root"
exec scripts/with-postgres lake exe lanesServiceOracle store db "$@"
