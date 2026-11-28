/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Tests.Live

/-!
Stopping on a signal. The drain a server does is decided by `Http.Shutdown.step`, checked here on
runs of looks at the requests in flight; `Server.stopOnSignal` is run in a child process by
`Tests/Ops.lean`. Live, a runtime alone is sent a real SIGTERM, by this process to itself, while
its waiter is listening, and stops with every input it took taken.
-/

namespace Tests.Signal

open Lanes Lanes.Http Std.Async

/-- The actions of a drain of `drain_ms` begun at `0`, looked at at each `(now_ms, inFlight)`. -/
def drainRun (drain_ms : Nat) (looks : List (Nat × Nat)) : List (Nat × Shutdown.Action) :=
  let start := Shutdown.step drain_ms .serving (.signal 0)
  let (_, acts) := looks.foldl (init := (start.1, start.2.map (0, ·))) fun (p, acts) (now, n) =>
    let (p, more) := Shutdown.step drain_ms p (.tick now n)
    (p, acts ++ more.map (now, ·))
  acts

def tests : List (String × Bool) :=
  [ ("shutdown: a drain stops as soon as nothing is in flight, and once",
      drainRun 1000 [(10, 2), (20, 1), (30, 0), (40, 0)] == [(0, .drain), (30, .stop)]),
    ("shutdown: a drain with requests still in flight stops at its deadline",
      drainRun 100 [(50, 3), (99, 3), (100, 3), (150, 3)] == [(0, .drain), (100, .stop)]),
    ("shutdown: nothing is done before a signal",
      Shutdown.step 100 .serving (.tick 5 0) == (.serving, [])) ]

abbrev countSig : Signature where
  Id := Unit
  Msg _ := Unit
  In := Unit
  Out := Nat

abbrev counter : System countSig where
  State _ := Nat
  actor _ := { init := 0, step := fun n () => (n + 1, [.emit (n + 1)]) }
  accept x := ⟨(), x⟩

def live : Async (List (String × Bool)) := do
  let rt ← Runtime.start counter
  for _ in [0:100] do rt.input ()
  let caught ← IO.Promise.new
  let stopped ← async (rt.stopOnSignal (caught := caught.resolve ()))
  let some () ← Tests.Live.within 10000 (await caught.result!) |
    rt.stop
    return [("signal: the waiter listens", false)]
  discard <| IO.Process.output { cmd := "kill", args := #["-TERM", toString (← IO.Process.getPID)] }
  let returned ← Tests.Live.within 10000 (await stopped)
  return [
    ("signal: a runtime sent SIGTERM stops, every input it took taken, and its process lives on",
      returned.isSome && (← rt.depth) == 0 && (← rt.ended).isNone) ]

end Tests.Signal
