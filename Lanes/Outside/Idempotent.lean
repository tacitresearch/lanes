/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Rpc

/-!
# Requests with idempotency keys

A request that changes something may carry a key. The service has the effect of the first
request under a key, and a repeat under that key has none: it is answered as the first was, or
refused for now (the first is still being handled, or the repeat asks for something else). A
request without a key has an effect of its own each time it is sent.

`server inner refusal` is the service `inner` behind keys. Each effect the service may have
had is a `Slot`: made by the first request under its key, or by one without a key, and told to
`inner` as a call whose id is the slot's index. Its `result` is the first answer given, if one
has been. A slot is made when the request is sent, not when its effect is known: a request
whose answer was `unknown` may have had its effect, and a slot counts it.

`at_most_once` is the guarantee: a request that is always sent under one key has its effect at
most once, in every run the model allows, whatever was lost, repeated, late or timed out.

Not yet checked against a real service: no run recorded from one that takes idempotency keys;
the runs are written by hand (`oracles/README.md`).
-/

@[expose] public section

namespace Lanes.Idempotent

lanes_data structure Keyed (K Q : Type) where
  key : Option K
  request : Q
  deriving DecidableEq, Repr, Hashable

/-- An effect the service may have had. -/
lanes_data structure Slot (K Q A : Type) where
  key : Option K
  request : Q
  /-- The first answer given about it, which every repeat that is answered gets. -/
  result : Option A
  deriving DecidableEq, Repr, Hashable

/-- How a call is answered: from slot `slot`, as the call that made it (`first`) or as a
repeat, with the same request as the first (`same`) or another, which only a refusal answers. -/
lanes_data structure Route where
  call : Nat
  slot : Nat
  first : Bool
  same : Bool
  deriving DecidableEq, Repr, Hashable

structure State (K Q A S : Type) where
  slots : List (Slot K Q A)
  routes : List Route
  inner : S
  deriving DecidableEq, Repr, Hashable

variable {K Q A S E : Type} [DecidableEq K] [DecidableEq Q] [DecidableEq A]

/-- The key and request of each slot. -/
def requests (d : State K Q A S) : List (Option K × Q) :=
  d.slots.map fun slot => (slot.key, slot.request)

/-- The slot a request under `key` repeats, if any. -/
def holder (d : State K Q A S) (key : Option K) : Option Nat :=
  key.bind fun k => d.slots.findIdx? (·.key == some k)

/-- `inner` behind keys. `refusal` says which answers refuse a repeat without effect: Stripe's
`409` while the first is being handled and `400` when the parameters differ. -/
def server (inner : Rpc.Server S Q A E) (refusal : A → Bool) :
    Rpc.Server (State K Q A S) (Keyed K Q) A E where
  init := ⟨[], [], inner.init⟩
  receive d call :=
    match holder d call.request.key with
    | some n =>
      { d with routes := ⟨call.id, n, false,
          decide ((d.slots[n]?).map (·.request) = some call.request.request)⟩ :: d.routes }
    | none =>
      { slots := d.slots ++ [⟨call.request.key, call.request.request, none⟩]
        routes := ⟨call.id, d.slots.length, true, true⟩ :: d.routes
        inner := inner.receive d.inner ⟨d.slots.length, call.deadline_ms, call.request.request⟩ }
  answer d call a :=
    match d.routes.find? (·.call == call) with
    | none => none
    | some r =>
      if !r.first && refusal a then some d
      else if !r.same then none
      else
        match d.slots[r.slot]? with
        | none => none
        | some slot =>
          match slot.result with
          | some first => if a = first then some d else none
          | none =>
            (inner.answer d.inner r.slot a).map fun s =>
              { d with slots := d.slots.set r.slot { slot with result := some a }, inner := s }
  event d e := (inner.event d.inner e).map ({ d with inner := · })

omit [DecidableEq K] [DecidableEq Q] [DecidableEq A] in
theorem requests_set {d : State K Q A S} {n : Nat} {slot : Slot K Q A} {a : A}
    (h : d.slots[n]? = some slot) (inner : S) :
    requests { d with slots := d.slots.set n { slot with result := some a }, inner } =
      requests d := by
  simp only [requests, List.map_set]
  have hn : n < d.slots.length := (List.getElem?_eq_some_iff.mp h).1
  have hslot : d.slots[n] = slot := (List.getElem?_eq_some_iff.mp h).2
  have hget : (d.slots.map fun slot => (slot.key, slot.request))[n]'(by simpa using hn) =
      (slot.key, slot.request) := by simp [hslot]
  rw [← hget, List.set_getElem_self]

/-- The keys of the slots are distinct, and every slot's key and request is one `good`
admits. -/
def Holds (good : Option K × Q → Prop) (d : State K Q A S) : Prop :=
  ((requests d).filterMap (·.1)).Nodup ∧ ∀ r ∈ requests d, good r

theorem holds_receive {good : Option K × Q → Prop} (inner : Rpc.Server S Q A E)
    (refusal : A → Bool) {d : State K Q A S} {call : Rpc.Call (Keyed K Q)} (h : Holds good d)
    (hcall : good (call.request.key, call.request.request)) :
    Holds good ((server inner refusal).receive d call) := by
  simp only [server]
  split
  · exact h
  · next hholder =>
    refine ⟨?_, ?_⟩
    · simp only [requests, List.map_append, List.map_cons, List.map_nil, List.filterMap_append]
      refine List.nodup_append.mpr ⟨h.1, ?_, ?_⟩
      · cases call.request.key <;> simp
      · intro k hk k' hk'
        cases hkey : call.request.key with
        | none => simp [hkey] at hk'
        | some k₀ =>
          simp only [hkey, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hk'
          subst hk'
          simp only [holder, hkey, Option.bind_some, List.findIdx?_eq_none_iff] at hholder
          intro hkk
          subst hkk
          obtain ⟨⟨key, _⟩, hmem, hk⟩ := List.mem_filterMap.mp hk
          obtain ⟨slot, hslot, hkr⟩ := List.mem_map.mp hmem
          simp only [Prod.mk.injEq] at hkr
          obtain ⟨rfl, -⟩ := hkr
          have := hholder slot hslot
          simp_all
    · intro r hr
      simp only [requests, List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact h.2 r hr
      · exact hcall

theorem holds_answer {good : Option K × Q → Prop} (inner : Rpc.Server S Q A E)
    (refusal : A → Bool) {d d' : State K Q A S} {call : Nat} {a : A} (h : Holds good d)
    (hanswer : (server inner refusal).answer d call a = some d') : Holds good d' := by
  simp only [server] at hanswer
  split at hanswer
  · simp at hanswer
  · split at hanswer
    · obtain rfl := Option.some.inj hanswer; exact h
    · split at hanswer
      · simp at hanswer
      · split at hanswer
        · simp at hanswer
        · next slot hslot =>
          split at hanswer
          · split at hanswer
            · obtain rfl := Option.some.inj hanswer; exact h
            · simp at hanswer
          · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp hanswer
            unfold Holds
            rw [requests_set hslot]
            exact h

/-- What holds of the keys and requests of the slots, in every run whose calls `good`
admits. -/
theorem holds (port : Rpc.Port σ (Keyed K Q) A E) (inner : Rpc.Server S Q A E)
    (refusal : A → Bool) (good : Option K × Q → Prop) {events : List (Event σ)}
    (hgood : ∀ out, Event.output out ∈ events → ∀ call, port.called out = some call →
      good (call.request.key, call.request.request))
    {d : Rpc.State (State K Q A S)}
    (h : (Rpc.outside port (server inner refusal)).after events = some d) :
    Holds good d.server :=
  Rpc.server_invariant port _ (fun call => good (call.request.key, call.request.request))
    (Holds good) (by simp [Holds, requests, server])
    (fun _ _ h hcall => holds_receive inner refusal h hcall)
    (fun _ _ _ _ h hanswer => holds_answer inner refusal h hanswer)
    (fun _ _ _ h hevent => by
      obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp hevent
      exact h)
    hgood h

/-- No two effects the service may have had share a key, in every run the model allows. -/
theorem keys_nodup (port : Rpc.Port σ (Keyed K Q) A E) (inner : Rpc.Server S Q A E)
    (refusal : A → Bool) {events : List (Event σ)} {d : Rpc.State (State K Q A S)}
    (h : (Rpc.outside port (server inner refusal)).after events = some d) :
    (d.server.slots.filterMap (·.key)).Nodup := by
  have := (holds port inner refusal (fun _ => True) (fun _ _ _ _ => trivial) h).1
  simpa [requests, List.filterMap_map, Function.comp_def] using this

/-- A request that is always sent under one key has its effect at most once: if every call
whose request `p` picks carries key `k`, at most one effect the service may have had is of a
request `p` picks, in every run the model allows. -/
theorem at_most_once (port : Rpc.Port σ (Keyed K Q) A E) (inner : Rpc.Server S Q A E)
    (refusal : A → Bool) (p : Q → Bool) (k : K) {events : List (Event σ)}
    (hkey : ∀ out, Event.output out ∈ events → ∀ call, port.called out = some call →
      p call.request.request = true → call.request.key = some k)
    {d : Rpc.State (State K Q A S)}
    (h : (Rpc.outside port (server inner refusal)).after events = some d) :
    (d.server.slots.filter (p ·.request)).length ≤ 1 := by
  obtain ⟨hnodup, hgood⟩ := holds port inner refusal (fun r => p r.2 = true → r.1 = some k)
    (fun out hout call hcall => hkey out hout call hcall) h
  let picked := d.server.slots.filter (p ·.request)
  have hkeys : picked.filterMap (·.key) = List.replicate picked.length k := by
    have hall : ∀ slot ∈ picked, slot.key = some k := by
      intro slot hslot
      obtain ⟨hmem, hp⟩ := List.mem_filter.mp hslot
      exact hgood (slot.key, slot.request) (List.mem_map.mpr ⟨slot, hmem, rfl⟩) hp
    clear_value picked
    induction picked with
    | nil => rfl
    | cons slot rest ih =>
      simp only [List.filterMap_cons, hall slot List.mem_cons_self, List.length_cons,
        List.replicate_succ, ih fun s hs => hall s (List.mem_cons_of_mem _ hs)]
  have hsub : (picked.filterMap (·.key)).Sublist (d.server.slots.filterMap (·.key)) :=
    (List.filter_sublist).filterMap _
  have hn : (picked.filterMap (·.key)).Nodup :=
    hsub.nodup (by simpa [requests, List.filterMap_map, Function.comp_def] using hnodup)
  rw [hkeys] at hn
  exact List.nodup_replicate.mp hn

/-- A repeat is answered as the first was, or refused: an answer the model allows to a call
whose slot was answered before is that answer, or a refusal of a repeat. -/
theorem answer_repeat (inner : Rpc.Server S Q A E) (refusal : A → Bool)
    {d d' : State K Q A S} {call : Nat} {a first : A} {r : Route} {slot : Slot K Q A}
    (hroute : d.routes.find? (·.call == call) = some r) (hslot : d.slots[r.slot]? = some slot)
    (hfirst : slot.result = some first)
    (h : (server inner refusal).answer d call a = some d') :
    a = first ∨ (r.first = false ∧ refusal a = true) := by
  simp only [server, hroute, hslot, hfirst] at h
  by_cases hrefused : (!r.first && refusal a) = true
  · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hrefused
    exact .inr hrefused
  · simp only [hrefused, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · simp at h
    · split at h
      · next heq => exact .inl heq
      · simp at h

end Lanes.Idempotent
