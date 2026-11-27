#!/usr/bin/env bash
# Model checking of native/loop.c with CBMC (TRUSTED.md): scripts/cbmc/loop.c checks that each
# thing a thread of the loop does keeps the invariant of its table of connections, on stubs of
# Lean, the sockets and the clock. Loops over the table run in full; TURNS (2) bounds the turns
# of a connection's drive and of its writes, and ACCEPTS (2) the accepts of a turn, so a path
# with more is not checked. OP (0 to 4) checks one operation, all five when unset.
set -euo pipefail
cd "$(dirname "$0")/.."
turns=${TURNS:-2}
op=()
[ -z "${OP:-}" ] || op=(-D "OP=$OP")
cbmc scripts/cbmc/loop.c -I scripts/cbmc "${op[@]}" --object-bits 12 \
  --unwindset "main.0:3,check.0:3,check.1:3,sweep.0:3,stop_all.0:3,take_mail.0:3" \
  --unwindset "lanes_cloop_take.0:3,accept_some.0:${ACCEPTS:-2}" \
  --unwindset "drive.1:$turns,drive.0:$turns,flush.0:$turns" \
  --bounds-check --pointer-check --div-by-zero-check --signed-overflow-check \
  --unsigned-overflow-check "$@"
