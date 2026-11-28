/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Basic
public import Lanes.Data.Declare

/-!
# A call to a service, whose timeout says nothing

A system calls a service with an output that carries an id, a deadline and a request (rule 3.4),
and is told the answer with an input. The answer may come, come after the caller stopped
waiting, or never come; or the adapter that makes the call gives up at the deadline and says
`unknown`. An `unknown` says nothing about whether the request took effect: it may have, it may
not have, and it may still. A caller that retries after one is safe only if a repeat is harmless,
which is what `Lanes.Outside.Idempotent` gives.

What the service may answer, and which events it may report, is a `Server`: a model of the
service's state, told each request as it is sent. `Rpc.outside` makes an `Outside` of it, which
answers each call at most once (`Rpc.answered_le_called`) and may answer any call `unknown`.
-/

@[expose] public section

namespace Lanes.Rpc

lanes_data structure Call (Q : Type) where
  id : Nat
  /-- How long the adapter waits for the answer before it says `unknown`. -/
  deadline_ms : Nat
  request : Q
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Reply (A : Type) where
  | answer (a : A)
  /-- No answer by the deadline: the request may or may not have taken effect. -/
  | unknown
  deriving DecidableEq, Repr, Hashable

/-- Which outputs of a system are calls, which inputs answer them, and which inputs are events
the service reports on its own (webhooks). -/
structure Port (σ : Signature) (Q A E : Type) where
  called : σ.Out → Option (Call Q)
  replied : σ.In → Option (Nat × Reply A)
  notified : σ.In → Option E := fun _ => none

/-- A model of a service: its state, which changes as each request is sent to it, and which
answers and events it may give. -/
structure Server (S Q A E : Type) where
  init : S
  receive : S → Call Q → S
  answer : S → (call : Nat) → A → Option S
  event : S → E → Option S := fun _ _ => none

/-- The calls not yet answered, and the server's state. -/
structure State (S : Type) where
  pending : List Nat
  server : S
  deriving DecidableEq, Repr, Hashable

variable {σ : Signature} {S Q A E : Type}

/-- What the service may do: answer an open call once, with an answer its model allows or with
`unknown`, report an event its model allows, or do nothing at all. -/
def outside (port : Port σ Q A E) (server : Server S Q A E) : Outside σ (State S) where
  init := ⟨[], server.init⟩
  allow d x :=
    match port.replied x with
    | some (call, reply) =>
      if call ∈ d.pending then
        match reply with
        | .answer a => (server.answer d.server call a).map (⟨d.pending.erase call, ·⟩)
        | .unknown => some ⟨d.pending.erase call, d.server⟩
      else none
    | none =>
      match port.notified x with
      | some e => (server.event d.server e).map (⟨d.pending, ·⟩)
      | none => none
  observe d out :=
    match port.called out with
    | some call => ⟨call.id :: d.pending, server.receive d.server call⟩
    | none => d

/-- The event an input reports, as `outside` reads it: an answer to a call is not one. -/
def Port.reported (port : Port σ Q A E) (x : σ.In) : Option E :=
  match port.replied x with
  | some _ => none
  | none => port.notified x

theorem allow_reported {port : Port σ Q A E} {server : Server S Q A E} {d d' : State S}
    {x : σ.In} {e : E} (h : port.reported x = some e)
    (hallow : (outside port server).allow d x = some d') :
    ∃ s, server.event d.server e = some s ∧ d' = ⟨d.pending, s⟩ := by
  simp only [Port.reported] at h
  simp only [outside] at hallow
  split at hallow
  · simp_all
  · next hreplied =>
    simp only [hreplied] at h
    simp only [h] at hallow
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hallow
    exact ⟨s, hs, rfl⟩

theorem allow_not_reported {port : Port σ Q A E} {server : Server S Q A E} {d d' : State S}
    {x : σ.In} (h : port.reported x = none)
    (hallow : (outside port server).allow d x = some d') :
    d'.server = d.server ∨ ∃ call a, port.replied x = some (call, .answer a) ∧
      server.answer d.server call a = some d'.server := by
  simp only [outside] at hallow
  split at hallow
  · next call reply hreplied =>
    split at hallow
    · split at hallow
      · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hallow
        exact .inr ⟨call, _, hreplied, hs⟩
      · obtain rfl := Option.some.inj hallow
        exact .inl rfl
    · simp at hallow
  · next hreplied =>
    simp only [Port.reported, hreplied] at h
    simp [h] at hallow

theorem allow_answer {port : Port σ Q A E} {server : Server S Q A E} {d d' : State S}
    {x : σ.In} {call : Nat} {a : A} (h : port.replied x = some (call, .answer a))
    (hallow : (outside port server).allow d x = some d') :
    server.answer d.server call a = some d'.server := by
  simp only [outside, h] at hallow
  split at hallow
  · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hallow
    exact hs
  · simp at hallow

/-- What the server's start has, and every request `good` admits, every answer and every event
keep, holds after every run whose calls `good` admits. -/
theorem server_invariant (port : Port σ Q A E) (server : Server S Q A E)
    (good : Call Q → Prop) (P : S → Prop) (init : P server.init)
    (receive : ∀ s call, P s → good call → P (server.receive s call))
    (answer : ∀ s call a s', P s → server.answer s call a = some s' → P s')
    (event : ∀ s e s', P s → server.event s e = some s' → P s')
    {events : List (Event σ)}
    (hgood : ∀ out, Event.output out ∈ events → ∀ call, port.called out = some call → good call)
    {d : State S} (h : (outside port server).after events = some d) : P d.server := by
  refine (outside port server).after_invariant
    (fun out => ∀ call, port.called out = some call → good call) (fun d => P d.server) init
    ?_ ?_ hgood h
  · intro d x d' hd hallow
    simp only [outside] at hallow
    split at hallow
    · split at hallow
      · split at hallow
        · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hallow
          exact answer _ _ _ _ hd hs
        · obtain rfl := Option.some.inj hallow
          exact hd
      · simp at hallow
    · split at hallow
      · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hallow
        exact event _ _ _ hd hs
      · simp at hallow
  · intro d out hd hout
    simp only [outside]
    split
    · next call hcall => exact receive _ _ hd (hout call hcall)
    · exact hd

/-- How often `events` call with id `call`. -/
def called (port : Port σ Q A E) (call : Nat) (events : List (Event σ)) : Nat :=
  events.countP fun
    | .output out => (port.called out).any (·.id == call)
    | _ => false

/-- How often `events` answer the call `call`, `unknown` included. -/
def answered (port : Port σ Q A E) (call : Nat) (events : List (Event σ)) : Nat :=
  events.countP fun
    | .input x => (port.replied x).any (·.1 == call)
    | _ => false

/-- A call is answered at most once each time it is made, in every run the model allows. -/
theorem answered_le_called (port : Port σ Q A E) (server : Server S Q A E)
    {events : List (Event σ)} {d : State S} (h : (outside port server).after events = some d)
    (call : Nat) : answered port call events ≤ called port call events := by
  suffices hc : answered port call events + d.pending.count call = called port call events by omega
  refine (outside port server).after_induction
    (P := fun events d => answered port call events + d.pending.count call = called port call events)
    (by simp [answered, called, outside]) ?_ h
  intro events d event d' ih hsee
  cases event with
  | input x =>
    simp only [Outside.see, outside] at hsee
    simp only [answered, called, List.countP_append] at ih ⊢
    split at hsee
    · next c reply hreply =>
      split at hsee
      · next hopen =>
        have hd' : d'.pending = d.pending.erase c := by
          split at hsee
          · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp hsee
            rfl
          · obtain rfl := Option.some.inj hsee
            rfl
        rw [hd', List.count_erase]
        by_cases hc : c = call
        · subst hc
          have := List.count_pos_iff.mpr hopen
          simp [hreply]
          omega
        · simp [hreply, hc]
          omega
      · simp at hsee
    · next hreply =>
      split at hsee
      · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp hsee
        simp [hreply, ih]
      · simp at hsee
  | output out =>
    simp only [Outside.see, outside, Option.some.injEq] at hsee
    subst hsee
    simp only [answered, called, List.countP_append] at ih ⊢
    split
    · next c hc =>
      by_cases hid : c.id = call
      · simp [hc, hid]
        omega
      · simp [hc, hid]
        omega
    · next hc =>
      simp [hc]
      omega
  | _ =>
    simp only [Outside.see, Option.some.injEq] at hsee
    subst hsee
    simpa [answered, called, List.countP_append] using ih

end Lanes.Rpc
