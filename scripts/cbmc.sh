#!/usr/bin/env bash
# Bounded model checking of native/loop.c with CBMC (TRUSTED.md): scripts/cbmc/loop.c runs a
# thread of the loop on stubs of Lean, the sockets, epoll and the clock. UNWIND (4) bounds
# every loop, so what is checked is every path of that many turns of each loop.
set -euo pipefail
cd "$(dirname "$0")/.."
cbmc scripts/cbmc/loop.c -I scripts/cbmc --unwind "${UNWIND:-4}" \
  --bounds-check --pointer-check --pointer-primitive-check --div-by-zero-check \
  --signed-overflow-check --unsigned-overflow-check --conversion-check \
  --undefined-shift-check --nan-check "$@"
