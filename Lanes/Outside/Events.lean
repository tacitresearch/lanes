/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc

/-!
# Events a service reports on its own

A service reports what happened to the things it holds with events it sends when it likes
(webhooks). They come late, in any order, more than once, or never: a service that retries
until it is acknowledged sends an event again whenever an acknowledgement is lost.

`bounded maxDeliveries inner` is the service `inner` with its events delivered so: an event
`inner` may report is delivered at once or later, and one delivered before may be delivered
again at any later time, whatever `inner` has done since, up to `maxDeliveries` times in all
(rule 2.6: the bound keeps the checker finite, and is the most a test of the real service may
see). That an event about an earlier state may still come after a later one is for `inner` to
allow, since only it knows which states a thing went through.

Not yet checked against a real service: no run recorded from one that sends webhooks; the runs
are written by hand (`oracles/README.md`).
-/

@[expose] public section

namespace Lanes.Events

/-- The service's state, and how often each event has been delivered. -/
structure State (S E : Type) where
  inner : S
  delivered : List (E × Nat)
  deriving DecidableEq, Repr, Hashable

variable {σ : Signature} {S Q A E : Type} [DecidableEq E]

def count (delivered : List (E × Nat)) (e : E) : Nat := (delivered.lookup e).getD 0

/-- One more delivery of `e`. -/
def bump (delivered : List (E × Nat)) (e : E) : List (E × Nat) :=
  (e, count delivered e + 1) :: delivered.filter (·.1 != e)

def bounded (maxDeliveries : Nat) (inner : Rpc.Server S Q A E) : Rpc.Server (State S E) Q A E where
  init := ⟨inner.init, []⟩
  receive d call := { d with inner := inner.receive d.inner call }
  answer d call a := (inner.answer d.inner call a).map ({ d with inner := · })
  event d e :=
    if count d.delivered e < maxDeliveries then
      if 0 < count d.delivered e then some { d with delivered := bump d.delivered e }
      else (inner.event d.inner e).map (⟨·, bump d.delivered e⟩)
    else none

@[simp] theorem count_bump_self (delivered : List (E × Nat)) (e : E) :
    count (bump delivered e) e = count delivered e + 1 := by
  simp [count, bump]

theorem count_bump_of_ne (delivered : List (E × Nat)) {e e' : E} (h : e' ≠ e) :
    count (bump delivered e) e' = count delivered e' := by
  have hne : (e' == e) = false := by simpa using h
  simp only [count, bump, List.lookup, hne]
  congr 1
  induction delivered with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨a, n⟩ := p
    by_cases ha : a = e
    · subst ha
      simp [List.lookup, hne, ih]
    · cases hp' : e' == a <;> simp [ha, List.lookup, hp', ih]

/-- How often `events` deliver `e`. -/
def deliveries (port : Rpc.Port σ Q A E) (e : E) (events : List (Event σ)) : Nat :=
  events.countP fun
    | .input x => port.reported x == some e
    | _ => false

/-- Each event is delivered at most `maxDeliveries` times, in every run the model allows. -/
theorem deliveries_le (port : Rpc.Port σ Q A E) (maxDeliveries : Nat)
    (inner : Rpc.Server S Q A E) {events : List (Event σ)} {d : Rpc.State (State S E)}
    (h : (Rpc.outside port (bounded maxDeliveries inner)).after events = some d) (e : E) :
    deliveries port e events ≤ maxDeliveries := by
  suffices hc : deliveries port e events = count d.server.delivered e ∧
      count d.server.delivered e ≤ maxDeliveries by omega
  refine (Rpc.outside port (bounded maxDeliveries inner)).after_induction
    (P := fun events d => deliveries port e events = count d.server.delivered e ∧
      count d.server.delivered e ≤ maxDeliveries)
    (by simp [deliveries, count, Rpc.outside, bounded]) ?_ h
  intro events d event d' ⟨ih, hle⟩ hsee
  cases event with
  | input x =>
    simp only [Outside.see] at hsee
    simp only [deliveries, List.countP_append] at ih ⊢
    cases hrep : port.reported x with
    | some e' =>
      obtain ⟨s, hs, rfl⟩ := Rpc.allow_reported hrep hsee
      simp only [bounded] at hs
      split at hs
      · next hlt =>
        have hdel : s.delivered = bump d.server.delivered e' := by
          split at hs
          · obtain rfl := Option.some.inj hs; rfl
          · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hs; rfl
        rw [hdel]
        by_cases he : e' = e
        · subst he
          simp [hrep, ih]
          omega
        · simp [hrep, he, count_bump_of_ne _ (Ne.symm he), ih, hle]
      · simp at hs
    | none =>
      have hd : d'.server.delivered = d.server.delivered := by
        rcases Rpc.allow_not_reported hrep hsee with h | ⟨_, _, _, hans⟩
        · rw [h]
        · simp only [bounded] at hans
          obtain ⟨s, -, hs⟩ := Option.map_eq_some_iff.mp hans
          rw [← hs]
      simp [hrep, hd, ih, hle]
  | output out =>
    simp only [Outside.see, Rpc.outside, Option.some.injEq] at hsee
    subst hsee
    simp only [deliveries, List.countP_append] at ih ⊢
    split <;> simp [bounded, ih, hle]
  | _ =>
    simp only [Outside.see, Option.some.injEq] at hsee
    subst hsee
    simp only [deliveries, List.countP_append] at ih ⊢
    simp [ih, hle]

end Lanes.Events
