/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
What a server does when it is told to stop, decided purely (rule 3.9); `Server.stopOnSignal`
(`Lanes/Web/IO/Server.lean`) performs it.

At SIGTERM or SIGINT the server drains: readiness answers `503`, so that a load balancer sends
it nothing new, while it goes on serving and the requests the shard has taken are answered. It
stops (`Server.stop`: the listener closes, the runtime stops, what still waits is answered `503`)
once nothing is in flight or `drain_ms` has passed. The listener stays open while it drains: a
load balancer may still send a request in the moments before it reads readiness, and a closed
port would refuse it.

What is proved: the server stops only when nothing is in flight or the deadline has passed
(`step_stop`), so a request whose answer comes before the deadline is answered by the system,
not cut off; it stops at the first look at or past the deadline (`step_deadline`); and it stops
once (`step_stopping`). With the gate's theorems, every request it admitted is answered, by the
system, `504` at its own deadline, or `503` at the stop.
-/

@[expose] public section

namespace Lanes.Http.Shutdown

inductive Phase where
  | serving
  | draining (deadline_ms : Nat)
  | stopping
  deriving DecidableEq, Repr

inductive Event where
  /-- SIGTERM or SIGINT, at a moment of the monotonic clock. -/
  | signal (now_ms : Nat)
  /-- A look at the requests in flight. -/
  | tick (now_ms inFlight : Nat)
  deriving DecidableEq, Repr

inductive Action where
  /-- Readiness answers `503` from now on (`Server.drain`). -/
  | drain
  | stop
  deriving DecidableEq, Repr

def step (drain_ms : Nat) : Phase → Event → Phase × List Action
  | .serving, .signal now_ms => (.draining (now_ms + drain_ms), [.drain])
  | .draining deadline_ms, .tick now_ms inFlight =>
    if inFlight = 0 ∨ deadline_ms ≤ now_ms then (.stopping, [.stop]) else (.draining deadline_ms, [])
  | p, _ => (p, [])

/-- The server stops only while it drains, and only when nothing is in flight or the deadline
has passed. -/
theorem step_stop {drain_ms : Nat} {p : Phase} {e : Event} (h : .stop ∈ (step drain_ms p e).2) :
    ∃ deadline_ms now_ms inFlight, p = .draining deadline_ms ∧ e = .tick now_ms inFlight ∧
      (inFlight = 0 ∨ deadline_ms ≤ now_ms) := by
  unfold step at h
  split at h
  · simp at h
  · split at h
    · exact ⟨_, _, _, rfl, rfl, by assumption⟩
    · simp at h
  · simp at h

/-- A drain ends at the first look at or past its deadline. -/
theorem step_deadline (drain_ms deadline_ms now_ms inFlight : Nat) (h : deadline_ms ≤ now_ms) :
    step drain_ms (.draining deadline_ms) (.tick now_ms inFlight) = (.stopping, [.stop]) := by
  simp [step, h]

/-- The deadline is `drain_ms` after the signal. -/
theorem step_signal (drain_ms now_ms : Nat) :
    step drain_ms .serving (.signal now_ms) = (.draining (now_ms + drain_ms), [.drain]) := rfl

/-- Once stopping, nothing more is done: a server stops once. -/
theorem step_stopping (drain_ms : Nat) (e : Event) : step drain_ms .stopping e = (.stopping, []) := by
  cases e <;> rfl

end Lanes.Http.Shutdown
