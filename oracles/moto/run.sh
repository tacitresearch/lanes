#!/usr/bin/env bash
# The service oracles of the object store, multipart, email and queue models against moto, S3,
# SES and SQS served on one local port:
#
#   oracles/moto/run.sh [--record]
#
# It makes a virtual environment from oracles/moto/requirements.txt (in LANES_ORACLE_CACHE, or
# .lake/oracles), starts moto_server on a free port, runs `lake exe lanesServiceOracle s3 s3-post
# s3-multipart s3-backup` and, in integrations/aws, `lake exe serviceOracle` (SES and SQS), then stops moto
# by its process id. Without python3 it says it is skipped.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
python=${LANES_PYTHON:-python3}
if ! command -v "$python" >/dev/null; then
  echo "s3, s3-post, s3-multipart, s3-backup, ses, sqs: skipped, no $python to run moto"
  exit 0
fi
cache=${LANES_ORACLE_CACHE:-$root/.lake/oracles}
venv=$cache/venv/moto
requirements=$root/oracles/moto/requirements.txt
if ! cmp -s "$requirements" "$venv/lanes-requirements.txt"; then
  "$python" -m venv --clear "$venv"
  "$venv/bin/pip" install --quiet --disable-pip-version-check -r "$requirements"
  cp "$requirements" "$venv/lanes-requirements.txt"
fi
port=$("$python" -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
"$venv/bin/moto_server" -H 127.0.0.1 -p "$port" > "$cache/moto.log" 2>&1 &
moto=$!
trap 'kill "$moto" 2>/dev/null || true' EXIT
for _ in $(seq 100); do
  if "$python" -c "import socket, sys; socket.create_connection(('127.0.0.1', $port), 1)" 2>/dev/null; then
    break
  fi
  sleep 0.1
done
"$venv/bin/pip" show moto | grep '^Version'
export LANES_MOTO="127.0.0.1:$port"
status=0
(cd "$root" && lake exe lanesServiceOracle s3 s3-post s3-multipart s3-backup "$@") || status=1
(cd "$root/integrations/aws" && lake exe serviceOracle "$@") || status=1
exit $status
