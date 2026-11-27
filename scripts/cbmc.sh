#!/usr/bin/env bash
# Bounded model checking of native/loop.c with CBMC (TRUSTED.md): scripts/cbmc/loop.c runs a
# thread of the loop on stubs of Lean, the sockets, epoll and the clock. TURNS (3) bounds the
# turns of the thread's loop, and every other loop is bounded below; what is checked is every
# path within those bounds.
set -euo pipefail
cd "$(dirname "$0")/.."
turns=${TURNS:-3}
cbmc scripts/cbmc/loop.c -I scripts/cbmc \
  --unwindset "work.1:$turns,work.0:3,drive.1:3,drive.0:2,flush.0:2,accept_some.0:2" \
  --unwindset "take_mail.0:3,sweep.0:3,stop_all.0:3,epoll_wait.0:3" \
  --unwindset "lanes_cloop_take.0:3,main.0:8" \
  --bounds-check --pointer-check --pointer-primitive-check --div-by-zero-check \
  --signed-overflow-check --unsigned-overflow-check --conversion-check \
  --undefined-shift-check "$@"
