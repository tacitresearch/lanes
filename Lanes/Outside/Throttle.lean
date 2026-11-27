/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc

/-!
# A service that throttles

`server config inner` is the service `inner` behind a rate limit: it may answer a call
`throttled retryAfter`, HTTP's `429 Too Many Requests` with `Retry-After`, which says the request
was not executed and asks the caller to wait `retryAfter` ticks before it calls again. A call
received earlier than the service said is counted (`early`): a caller that retries at once, or
calls on while it was told to wait, is one that hammers the service. Dropping a call is
`Rpc`'s: no answer, or `unknown`.

Time is a tick the service reports as an event (rule 2.4: the caller sees time as inputs too),
at most `maxTicks` of them (rule 2.6). With `burst` given, the limit is that many calls a tick: a
call within it is never throttled and one beyond it always is (`Throttle.within_not_throttled`),
so a caller that waits as it is told gets through. Without it the service may throttle any call,
as one throttled for the load of others may.

Proved: a throttled answer leaves the inner service as it was (`Throttle.throttled_inner`), and
the service never asks for a wait of more than `maxRetryAfter` ticks from now
(`Throttle.wait_le`), in every run the model allows.
-/

@[expose] public section

namespace Lanes.Throttle

lanes_data inductive Answer (A : Type) where
  | ok (a : A)
  /-- The request was not executed: call again in `retryAfter` ticks. -/
  | throttled (retryAfter : Nat)
  deriving DecidableEq, Repr, Hashable, Codable

lanes_data inductive Event (E : Type) where
  /-- A tick of time passed. -/
  | tick
  | inner (e : E)
  deriving DecidableEq, Repr, Hashable, Codable

structure Config where
  /-- The longest `Retry-After` the service gives, at least one tick. -/
  maxRetryAfter : Nat
  maxTicks : Nat
  /-- Calls a tick within the limit; `none` if any call may be throttled. -/
  burst : Option Nat := none

structure State (S : Type) where
  inner : S
  now : Nat := 0
  /-- The first tick at which the service said it takes calls again. -/
  retryAt : Nat := 0
  /-- Calls received this tick. -/
  used : Nat := 0
  /-- Calls received beyond the limit. -/
  over : List Nat := []
  /-- Calls received before `retryAt`. -/
  early : Nat := 0
  deriving DecidableEq, Repr, Hashable

variable {S Q A E : Type}

def server (config : Config) (inner : Rpc.Server S Q A E) :
    Rpc.Server (State S) Q (Answer A) (Event E) where
  init := { inner := inner.init }
  receive d call :=
    { d with inner := inner.receive d.inner call
             used := d.used + 1
             over := if config.burst.all (d.used < ·) then d.over else call.id :: d.over
             early := if d.now < d.retryAt then d.early + 1 else d.early }
  answer d call
    | .ok a =>
      if config.burst.isSome && call ∈ d.over then none
      else (inner.answer d.inner call a).map ({ d with inner := · })
    | .throttled retryAfter =>
      if 0 < retryAfter ∧ retryAfter ≤ config.maxRetryAfter
          ∧ (config.burst.isNone || call ∈ d.over) then
        some { d with retryAt := max d.retryAt (d.now + retryAfter) }
      else none
  event d
    | .tick => if d.now < config.maxTicks then some { d with now := d.now + 1, used := 0 } else none
    | .inner e => (inner.event d.inner e).map ({ d with inner := · })

/-- A throttled answer leaves the inner service as it was: the request was not executed. -/
theorem throttled_inner (config : Config) (inner : Rpc.Server S Q A E) {d d' : State S}
    {call retryAfter : Nat} (h : (server config inner).answer d call (.throttled retryAfter) = some d') :
    d'.inner = d.inner := by
  simp only [server] at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · simp at h

/-- Under a limit of `burst` calls a tick, a call within it is not throttled. -/
theorem within_not_throttled (config : Config) (inner : Rpc.Server S Q A E) {d : State S}
    {call retryAfter : Nat} (hburst : config.burst.isSome) (hwithin : call ∉ d.over) :
    (server config inner).answer d call (.throttled retryAfter) = none := by
  simp [server, hwithin, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none.mp hburst]

/-- The service never asks for a wait of more than `maxRetryAfter` ticks from now, in every run
the model allows. -/
theorem wait_le {σ : Signature} (port : Rpc.Port σ Q (Answer A) (Event E)) (config : Config)
    (inner : Rpc.Server S Q A E) {events : List (Lanes.Event σ)} {d : Rpc.State (State S)}
    (h : (Rpc.outside port (server config inner)).after events = some d) :
    d.server.retryAt ≤ d.server.now + config.maxRetryAfter := by
  refine Rpc.server_invariant port _ (fun _ => True)
    (fun d => d.retryAt ≤ d.now + config.maxRetryAfter) (by simp [server]) ?_ ?_ ?_
    (fun _ _ _ _ => trivial) h
  · intro s call hs _
    simpa [server] using hs
  · intro s call a s' hs hanswer
    cases a with
    | ok a =>
      simp only [server] at hanswer
      split at hanswer
      · simp at hanswer
      · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hanswer
        exact hs
    | throttled r =>
      simp only [server] at hanswer
      split at hanswer
      · next hok =>
        obtain rfl := Option.some.inj hanswer
        simp only
        omega
      · simp at hanswer
  · intro s e s' hs hevent
    cases e with
    | tick =>
      simp only [server] at hevent
      split at hevent
      · obtain rfl := Option.some.inj hevent
        simp only
        omega
      · simp at hevent
    | inner e =>
      simp only [server] at hevent
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hevent
      exact hs

end Lanes.Throttle
