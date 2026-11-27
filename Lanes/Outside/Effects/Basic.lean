/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Idempotent
public import Lanes.Outside.Events
public import Lanes.Data.Enum
public import Lanes.Proof.List.Basic

/-!
# A service that holds things which change on their own

A payment, a sent email, a shipment: the caller asks the service to make one, with a request
under an idempotency key, and the service then moves it through the states of its `Lifecycle`
(made, pending, then succeeded, failed or canceled) as the world outside both of them decides,
and reports each move with an event. The caller learns of a thing from the answer to its request
or from an event, whichever comes first, and may learn of it only from an event: the answer may
have been `unknown`.

`server lifecycle` is the model of the things alone: a request sent is a thing that may exist;
an answer or an event that names it shows it does, in a state its lifecycle allows. An event
about a state the thing may have passed through on the way to the one it is in may still come.
`service` puts it behind keys (`Idempotent.server`) with its events late, repeated and out of
order (`Events.bounded`), and `outside` is that as an `Outside`. What the model leaves out is
said in the decision on models of external systems.

Of a state that no move leaves (`Lifecycle.Terminal`), such as a payment that succeeded, the
model keeps what it was told (`Sound`, in every run: `sound_after`): an answer or an event that
a thing is in it shows a thing in it, of the request the answer's call made
(`Sound.shows_reply`, `Sound.shows_report`), and it stays (`Keeps`).
-/

@[expose] public section

namespace Lanes.Effects

lanes_data inductive Phase where
  | created
  | pending
  | succeeded
  | failed
  | canceled
  deriving DecidableEq, Repr, Hashable, Codable, Enum

def Phase.final : Phase → Bool
  | .succeeded | .failed | .canceled => true
  | .created | .pending => false

/-- The states a thing goes through, as the service documents them. -/
structure Lifecycle (St : Type) where
  /-- The states a thing may be in when the request that makes it is answered. -/
  first : St → Bool
  /-- The moves the service may make on its own. -/
  next : St → St → Bool
  phase : St → Phase
  /-- The states the service sends an event about. -/
  reported : St → Bool

variable {St : Type} [DecidableEq St] [Enum St]

/-- A thing in a final phase does not move. -/
def Lifecycle.Final (lifecycle : Lifecycle St) : Prop :=
  ∀ a b, lifecycle.next a b = true → (lifecycle.phase a).final = false

/-- The states moves lead to from `a`, `a` among them. -/
def Lifecycle.reachable (lifecycle : Lifecycle St) (a : St) : List St :=
  go (Enum.all (α := St)).length [a]
where
  go : Nat → List St → List St
    | 0, found => found
    | n + 1, found => go n (found ++ (Enum.all (α := St)).filter fun c =>
        !found.contains c && found.any (lifecycle.next · c))

def Lifecycle.reaches (lifecycle : Lifecycle St) (a b : St) : Bool :=
  (lifecycle.reachable a).contains b

/-- The states a thing may be in when it is first seen, through an event. -/
def Lifecycle.seen (lifecycle : Lifecycle St) (st : St) : Bool :=
  (Enum.all (α := St)).any fun a => lifecycle.first a && lifecycle.reaches a st

lanes_data inductive Answer (R St : Type) where
  | made (id : R) (state : St)
  /-- A repeat under a key refused for now, with no effect. -/
  | refused
  deriving DecidableEq, Repr, Hashable, Codable

def Answer.isRefused {R : Type} : Answer R St → Bool
  | .refused => true
  | .made .. => false

/-- An event: thing `id`, made by a request with parameters `params`, is in state `state`. -/
lanes_data structure Report (R St P : Type) where
  id : R
  state : St
  params : P
  deriving DecidableEq, Repr, Hashable, Codable

/-- A thing that has been seen, made by the request of slot `slot`. -/
lanes_data structure Thing (R St P : Type) where
  id : R
  slot : Nat
  params : P
  state : St
  deriving DecidableEq, Repr, Hashable, Codable

/-- The requests sent whose thing nobody has seen, which may or may not exist, and the things
seen. -/
structure State (R St P : Type) where
  unseen : List (Nat × P)
  things : List (Thing R St P)
  deriving DecidableEq, Repr, Hashable

variable {R P : Type} [DecidableEq R] [DecidableEq P]

def ids (d : State R St P) : List R := d.things.map (·.id)

/-- The thing made by slot `n` seen in `st` as the answer to its request, if the lifecycle
allows. -/
def answered (lifecycle : Lifecycle St) (d : State R St P) (n : Nat) (id : R) (st : St) :
    Option (State R St P) :=
  match d.things.find? (·.slot == n) with
  | some t => if t.id = id ∧ lifecycle.first st ∧ lifecycle.reaches st t.state then some d else none
  | none =>
    match d.unseen.lookup n with
    | some p =>
      if lifecycle.first st ∧ id ∉ ids d then
        some ⟨d.unseen.erase (n, p), d.things ++ [⟨id, n, p, st⟩]⟩
      else none
    | none => none

/-- `t` reported in `st`: a state it was in, may have passed through, or moves to now. -/
def moved (lifecycle : Lifecycle St) (d : State R St P) (t : Thing R St P) (st : St) :
    Option (State R St P) :=
  if lifecycle.reaches st t.state then some d
  else if lifecycle.next t.state st then
    some { d with things := d.things.map fun u => if u.id = t.id then { u with state := st } else u }
  else none

def reported (lifecycle : Lifecycle St) (d : State R St P) (e : Report R St P) :
    Option (State R St P) :=
  if !lifecycle.reported e.state then none
  else
    match d.things.find? (·.id == e.id) with
    | some t => if t.params = e.params then moved lifecycle d t e.state else none
    | none =>
      match d.unseen.find? (·.2 == e.params) with
      | some (n, p) =>
        if lifecycle.seen e.state then
          some ⟨d.unseen.erase (n, p), d.things ++ [⟨e.id, n, p, e.state⟩]⟩
        else none
      | none => none

/-- The things alone, told each request as a call whose id is its slot. -/
def server (lifecycle : Lifecycle St) :
    Rpc.Server (State R St P) P (Answer R St) (Report R St P) where
  init := ⟨[], []⟩
  receive d call := { d with unseen := d.unseen ++ [(call.id, call.request)] }
  answer d n
    | .made id st => answered lifecycle d n id st
    | .refused => none
  event := reported lifecycle

abbrev Model (K R St P : Type) : Type :=
  Idempotent.State K P (Answer R St) (Events.State (State R St P) (Report R St P))

/-- The things behind keys, with their events late, repeated and out of order. -/
def service {K : Type} [DecidableEq K] (lifecycle : Lifecycle St) (maxDeliveries : Nat) :
    Rpc.Server (Model K R St P) (Idempotent.Keyed K P) (Answer R St) (Report R St P) :=
  Idempotent.server (Events.bounded maxDeliveries (server lifecycle)) Answer.isRefused

def outside {σ : Signature} {K : Type} [DecidableEq K]
    (port : Rpc.Port σ (Idempotent.Keyed K P) (Answer R St) (Report R St P))
    (lifecycle : Lifecycle St) (maxDeliveries : Nat) :
    Outside σ (Rpc.State (Model K R St P)) :=
  Rpc.outside port (service lifecycle maxDeliveries)

/-- A request whose parameters `p` picks, always sent under key `k`, has its effect at most
once in every run the model allows: at most one thing the service may have made is of such a
request, seen or not. -/
theorem at_most_once {σ : Signature} {K : Type} [DecidableEq K]
    (port : Rpc.Port σ (Idempotent.Keyed K P) (Answer R St) (Report R St P))
    (lifecycle : Lifecycle St) (maxDeliveries : Nat) (p : P → Bool) (k : K)
    {events : List (Event σ)}
    (hkey : ∀ out, Event.output out ∈ events → ∀ call, port.called out = some call →
      p call.request.request = true → call.request.key = some k)
    {d : Rpc.State (Model K R St P)} (h : (outside port lifecycle maxDeliveries).after events = some d) :
    (d.server.slots.filter (p ·.request)).length ≤ 1 :=
  Idempotent.at_most_once port _ _ p k hkey h

/-- A state no move leaves. -/
def Lifecycle.Terminal (lifecycle : Lifecycle St) (f : St) : Prop :=
  ∀ x, lifecycle.next f x = false

theorem Lifecycle.reachable_go_terminal {lifecycle : Lifecycle St} {f : St}
    (h : lifecycle.Terminal f) (n : Nat) : Lifecycle.reachable.go lifecycle n [f] = [f] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Lifecycle.reachable.go]
    have : (Enum.all (α := St)).filter
        (fun c => !([f].contains c) && [f].any (lifecycle.next · c)) = [] :=
      List.filter_eq_nil_iff.mpr fun c _ => by simp [h c]
    rw [this, List.append_nil, ih]

/-- Moves lead from a state no move leaves to that state alone. -/
theorem Lifecycle.reaches_terminal {lifecycle : Lifecycle St} {f x : St}
    (h : lifecycle.Terminal f) (hx : lifecycle.reaches f x = true) : x = f := by
  simpa [Lifecycle.reaches, Lifecycle.reachable, reachable_go_terminal h] using hx

theorem answered_cases {lifecycle : Lifecycle St} {d d' : State R St P} {n : Nat} {id : R}
    {st : St} (h : answered lifecycle d n id st = some d') :
    (d' = d ∧ ∃ t ∈ d.things, t.slot = n ∧ lifecycle.reaches st t.state = true) ∨
      ∃ p, (n, p) ∈ d.unseen ∧ id ∉ ids d ∧
        d' = ⟨d.unseen.erase (n, p), d.things ++ [⟨id, n, p, st⟩]⟩ := by
  unfold answered at h
  split at h
  · next t ht =>
    split at h
    · next hc =>
      obtain rfl := Option.some.inj h
      exact .inl ⟨rfl, t, List.mem_of_find?_eq_some ht, by simpa using List.find?_some ht,
        hc.2.2⟩
    · simp at h
  · split at h
    · next p hp =>
      split at h
      · next hc =>
        obtain rfl := Option.some.inj h
        obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hp
        exact .inr ⟨p, by simp [hl], hc.2, rfl⟩
      · simp at h
    · simp at h

theorem reported_cases {lifecycle : Lifecycle St} {d d' : State R St P} {e : Report R St P}
    (h : reported lifecycle d e = some d') :
    (d' = d ∧ ∃ t ∈ d.things, t.params = e.params ∧ lifecycle.reaches e.state t.state = true) ∨
      (∃ t ∈ d.things, t.params = e.params ∧ lifecycle.next t.state e.state = true ∧
        d' = { d with things := d.things.map fun u =>
          if u.id = t.id then { u with state := e.state } else u }) ∨
      ∃ n, (n, e.params) ∈ d.unseen ∧ e.id ∉ ids d ∧
        d' = ⟨d.unseen.erase (n, e.params), d.things ++ [⟨e.id, n, e.params, e.state⟩]⟩ := by
  unfold reported at h
  split at h
  · simp at h
  · split at h
    · next t ht =>
      have hmem := List.mem_of_find?_eq_some ht
      split at h
      · next hp =>
        unfold moved at h
        split at h
        · next hr => exact .inl ⟨(Option.some.inj h).symm, t, hmem, hp, hr⟩
        · split at h
          · next hn => exact .inr (.inl ⟨t, hmem, hp, hn, (Option.some.inj h).symm⟩)
          · simp at h
      · simp at h
    · next hnone =>
      split at h
      · next n p hp =>
        split at h
        · obtain rfl := Option.some.inj h
          have hpe : p = e.params := by simpa using List.find?_some hp
          subst hpe
          refine .inr (.inr ⟨n, List.mem_of_find?_eq_some hp, ?_, rfl⟩)
          intro hid
          obtain ⟨u, hu, hue⟩ := List.mem_map.mp hid
          have := List.find?_eq_none.mp hnone u hu
          simp [hue] at this
        · simp at h
      · simp at h

section Sound

variable {K : Type} [DecidableEq K] {f : St}

/-- The service holds a thing, made by a request with parameters `p`, in state `f`. -/
def Shows (d : Model K R St P) (f : St) (p : P) : Prop :=
  ∃ t ∈ d.inner.inner.things, t.params = p ∧ t.state = f

/-- What the things behind keys keep, about a state `f` that no move leaves: each thing is of
the request of its slot, an answer that gave `f` and an event about `f` delivered left a thing
in `f`. -/
structure Sound (f : St) (d : Model K R St P) : Prop where
  ids : (ids d.inner.inner).Nodup
  params : ∀ t ∈ d.inner.inner.things, (d.slots[t.slot]?).map (·.request) = some t.params
  unseen : ∀ q ∈ d.inner.inner.unseen, (d.slots[q.1]?).map (·.request) = some q.2
  answered : ∀ n slot id, d.slots[n]? = some slot → slot.result = some (.made id f) →
    ∃ t ∈ d.inner.inner.things, t.slot = n ∧ t.state = f
  reported : ∀ e, 0 < Events.count d.inner.delivered e → e.state = f → Shows d f e.params

/-- What the things of `d` in state `f` are, `d'` keeps. -/
def Keeps (f : St) (d d' : State R St P) : Prop :=
  ∀ t ∈ d.things, t.state = f → t ∈ d'.things

theorem keeps_answered {lifecycle : Lifecycle St} {d d' : State R St P} {n : Nat} {id : R}
    {st : St} (h : answered lifecycle d n id st = some d') : Keeps f d d' := by
  intro t ht _
  rcases answered_cases h with ⟨rfl, -⟩ | ⟨p, -, -, rfl⟩
  · exact ht
  · exact List.mem_append_left _ ht

theorem keeps_reported {lifecycle : Lifecycle St} (hf : lifecycle.Terminal f)
    {d d' : State R St P} {e : Report R St P} (hids : (ids d).Nodup)
    (h : reported lifecycle d e = some d') : Keeps f d d' := by
  intro u hu hf'
  rcases reported_cases h with ⟨rfl, -⟩ | ⟨t, ht, -, hn, rfl⟩ | ⟨n, -, -, rfl⟩
  · exact hu
  · refine List.mem_map.mpr ⟨u, hu, ?_⟩
    by_cases hid : u.id = t.id
    · have hut := eq_of_mem_of_nodup_map hids hu ht hid
      subst hut
      rw [hf', hf] at hn
      exact absurd hn Bool.false_ne_true
    · simp [hid]
  · exact List.mem_append_left _ hu

omit [DecidableEq St] [Enum St] [DecidableEq R] [DecidableEq P] [DecidableEq K] in
theorem Keeps.shows {d d' : Model K R St P} (h : Keeps f d.inner.inner d'.inner.inner) {p : P}
    (hs : Shows d f p) : Shows d' f p := by
  obtain ⟨t, ht, hp, hst⟩ := hs
  exact ⟨t, h t ht hst, hp, hst⟩

end Sound

section Sound

variable {K : Type} [DecidableEq K] {f : St} {lifecycle : Lifecycle St} {maxDeliveries : Nat}

omit [DecidableEq St] [Enum St] [DecidableEq R] [DecidableEq P] [DecidableEq K] in
theorem nodup_ids_append {d : State R St P} {t : Thing R St P} {u : List (Nat × P)}
    (h : (ids d).Nodup) (ht : t.id ∉ ids d) :
    (ids (⟨u, d.things ++ [t]⟩ : State R St P)).Nodup := by
  simp only [ids, List.map_append, List.map_cons, List.map_nil]
  refine List.nodup_append.mpr ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst hab hb
  exact ht ha

omit [DecidableEq St] [Enum St] [DecidableEq R] [DecidableEq P] [DecidableEq K] in
theorem requests_set {d : Model K R St P} {n k : Nat} {slot : Idempotent.Slot K P (Answer R St)}
    {a : Answer R St} (h : d.slots[n]? = some slot) :
    ((d.slots.set n { slot with result := some a })[k]?).map (·.request) =
      (d.slots[k]?).map (·.request) := by
  rw [List.getElem?_set]
  split
  · next hnk =>
    subst hnk
    obtain ⟨hn, hslot⟩ := List.getElem?_eq_some_iff.mp h
    simp [hn, hslot]
  · rfl

theorem sound_init : Sound f (service (K := K) (R := R) (P := P) lifecycle maxDeliveries).init := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [ids, service, Idempotent.server, Events.bounded, server, Events.count]

theorem Sound.receive {d : Model K R St P} (h : Sound f d) (call : Rpc.Call (Idempotent.Keyed K P)) :
    Sound f ((service lifecycle maxDeliveries).receive d call) ∧
      Keeps f d.inner.inner ((service lifecycle maxDeliveries).receive d call).inner.inner := by
  simp only [service, Idempotent.server]
  split
  · exact ⟨⟨h.ids, h.params, h.unseen, h.answered, h.reported⟩, fun t ht _ => ht⟩
  · refine ⟨⟨h.ids, ?_, ?_, ?_, h.reported⟩, fun t ht _ => ht⟩
    · intro t ht
      rw [getElem?_append_of_map (h.params t ht)]
      exact h.params t ht
    · intro q hq
      simp only [Events.bounded, server, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · rw [getElem?_append_of_map (h.unseen q hq)]
        exact h.unseen q hq
      · simp
    · intro n slot id hslot hres
      rcases getElem?_append_singleton hslot with hslot | ⟨-, rfl⟩
      · exact h.answered n slot id hslot hres
      · simp at hres

theorem Sound.answer (hf : lifecycle.Terminal f) {d d' : Model K R St P} (h : Sound f d)
    {call : Nat} {a : Answer R St} (ha : (service lifecycle maxDeliveries).answer d call a = some d') :
    Sound f d' ∧ Keeps f d.inner.inner d'.inner.inner := by
  simp only [service, Idempotent.server] at ha
  split at ha
  · simp at ha
  · next r hr =>
    split at ha
    · obtain rfl := Option.some.inj ha
      exact ⟨h, fun t ht _ => ht⟩
    · split at ha
      · simp at ha
      · split at ha
        · simp at ha
        · next slot hslot =>
          split at ha
          · split at ha
            · obtain rfl := Option.some.inj ha
              exact ⟨h, fun t ht _ => ht⟩
            · simp at ha
          · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp ha
            simp only [Events.bounded] at hs
            obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hs
            cases a with
            | refused => simp [server] at hx
            | made id st =>
              simp only [server] at hx
              have hkeeps : Keeps f d.inner.inner x := keeps_answered hx
              refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hkeeps⟩
              · rcases answered_cases hx with ⟨rfl, -⟩ | ⟨p, -, hid, rfl⟩
                · exact h.ids
                · exact nodup_ids_append h.ids hid
              · intro t ht
                show ((d.slots.set r.slot _)[t.slot]?).map _ = _
                rw [requests_set hslot]
                rcases answered_cases hx with ⟨rfl, -⟩ | ⟨p, hp, -, rfl⟩
                · exact h.params t ht
                · simp only [List.mem_append, List.mem_singleton] at ht
                  rcases ht with ht | rfl
                  · exact h.params t ht
                  · exact h.unseen _ hp
              · intro q hq
                show ((d.slots.set r.slot _)[q.1]?).map _ = _
                rw [requests_set hslot]
                rcases answered_cases hx with ⟨rfl, -⟩ | ⟨p, -, -, rfl⟩
                · exact h.unseen q hq
                · exact h.unseen q (List.mem_of_mem_erase hq)
              · intro n slot' id' hslot' hres
                simp only [List.getElem?_set] at hslot'
                split at hslot'
                · next hn =>
                  subst hn
                  have hlt : r.slot < d.slots.length := (List.getElem?_eq_some_iff.mp hslot).1
                  simp only [hlt, ↓reduceIte, Option.some.injEq] at hslot'
                  subst hslot'
                  simp only [Option.some.injEq, Answer.made.injEq] at hres
                  obtain ⟨rfl, rfl⟩ := hres
                  rcases answered_cases hx with ⟨rfl, t, ht, hts, hr⟩ | ⟨p, -, -, rfl⟩
                  · exact ⟨t, ht, hts, (Lifecycle.reaches_terminal hf hr)⟩
                  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
                · obtain ⟨t, ht, hts, htf⟩ := h.answered n slot' id' hslot' hres
                  exact ⟨t, hkeeps t ht htf, hts, htf⟩
              · intro e he hst
                exact Keeps.shows (d := d) hkeeps (h.reported e he hst)

end Sound

section Sound

variable {K : Type} [DecidableEq K] {f : St} {lifecycle : Lifecycle St} {maxDeliveries : Nat}

omit [DecidableEq St] [Enum St] [DecidableEq R] [DecidableEq P] in
theorem ids_map_state (d : State R St P) (g : Thing R St P → Prop) [DecidablePred g] (st : St) :
    ids { d with things := d.things.map fun u => if g u then { u with state := st } else u } =
      ids d := by
  simp only [ids, List.map_map]
  congr 1
  funext u
  simp only [Function.comp_apply]
  split <;> rfl

omit [DecidableEq K] in
theorem Sound.reported_inner (hf : lifecycle.Terminal f) {d : Model K R St P}
    (h : Sound f d) {e : Report R St P} {x : State R St P}
    (hx : Effects.reported lifecycle d.inner.inner e = some x) :
    (Effects.ids x).Nodup ∧
      (∀ t ∈ x.things, (d.slots[t.slot]?).map (·.request) = some t.params) ∧
      (∀ q ∈ x.unseen, (d.slots[q.1]?).map (·.request) = some q.2) ∧
      (e.state = f → ∃ t ∈ x.things, t.params = e.params ∧ t.state = f) := by
  rcases reported_cases hx with ⟨rfl, t, ht, hp, hr⟩ | ⟨t, ht, hp, -, rfl⟩ |
      ⟨n, hn, hid, rfl⟩
  · refine ⟨h.ids, h.params, h.unseen, fun hst => ⟨t, ht, hp, ?_⟩⟩
    rw [hst] at hr
    exact Lifecycle.reaches_terminal hf hr
  · refine ⟨?_, ?_, h.unseen, fun hst => ⟨{ t with state := e.state }, ?_, hp, hst⟩⟩
    · rw [ids_map_state]; exact h.ids
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      split <;> exact h.params v hv
    · exact List.mem_map.mpr ⟨t, ht, by simp⟩
  · refine ⟨nodup_ids_append h.ids hid, ?_, fun q hq => h.unseen q (List.mem_of_mem_erase hq),
      fun hst => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, hst⟩⟩
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact h.params u hu
    · exact h.unseen _ hn

theorem Sound.event (hf : lifecycle.Terminal f) {d d' : Model K R St P} (h : Sound f d)
    {e : Report R St P} (he : (service lifecycle maxDeliveries).event d e = some d') :
    Sound f d' ∧ Keeps f d.inner.inner d'.inner.inner := by
  simp only [service, Idempotent.server, Events.bounded] at he
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp he
  split at hs
  · split at hs
    · next hpos =>
      obtain rfl := Option.some.inj hs
      refine ⟨⟨h.ids, h.params, h.unseen, h.answered, ?_⟩, fun t ht _ => ht⟩
      intro e' he' hst
      by_cases hee : e' = e
      · subst hee; exact h.reported e' hpos hst
      · rw [Events.count_bump_of_ne _ hee] at he'
        exact h.reported e' he' hst
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hs
      simp only [server] at hx
      have hkeeps : Keeps f d.inner.inner x := keeps_reported hf h.ids hx
      obtain ⟨hids, hparams, hunseen, hshows⟩ := h.reported_inner hf hx
      refine ⟨⟨hids, hparams, hunseen, ?_, ?_⟩, hkeeps⟩
      · intro n slot id hslot hres
        obtain ⟨t, ht, hts, htf⟩ := h.answered n slot id hslot hres
        exact ⟨t, hkeeps t ht htf, hts, htf⟩
      · intro e' he' hst
        by_cases hee : e' = e
        · subst hee; exact hshows hst
        · rw [Events.count_bump_of_ne _ hee] at he'
          exact Keeps.shows (d := d) hkeeps (h.reported e' he' hst)
  · simp at hs

/-- How the service answers a call `.made id st`: through the route of the call, to a request
whose slot is answered so from now on. -/
theorem answer_made {d d' : Model K R St P} {call : Nat} {id : R} {st : St}
    (ha : (service lifecycle maxDeliveries).answer d call (.made id st) = some d') :
    ∃ r, d.routes.find? (·.call == call) = some r ∧ r.same = true ∧
      ∃ slot, d.slots[r.slot]? = some slot ∧ ∃ slot', d'.slots[r.slot]? = some slot' ∧
        slot'.request = slot.request ∧ slot'.result = some (.made id st) := by
  simp only [service, Idempotent.server] at ha
  split at ha
  · simp at ha
  · next r hr =>
    split at ha
    · simp [Answer.isRefused] at *
    · split at ha
      · simp at ha
      · next hsame =>
        refine ⟨r, hr, by simpa using hsame, ?_⟩
        split at ha
        · simp at ha
        · next slot hslot =>
          refine ⟨slot, hslot, ?_⟩
          split at ha
          · next first hfirst =>
            split at ha
            · next heq =>
              obtain rfl := Option.some.inj ha
              exact ⟨slot, hslot, rfl, heq ▸ hfirst⟩
            · simp at ha
          · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp ha
            have hlt : r.slot < d.slots.length := (List.getElem?_eq_some_iff.mp hslot).1
            exact ⟨{ slot with result := some (.made id st) }, by simp [hlt], rfl, rfl⟩

/-- An answer that a thing is in `f` shows the request of the call's slot made a thing now
in `f`. -/
theorem Sound.shows_answer {d d' : Model K R St P} (h' : Sound f d') {call : Nat} {id : R}
    (ha : (service lifecycle maxDeliveries).answer d call (.made id f) = some d') :
    ∃ r, d.routes.find? (·.call == call) = some r ∧ r.same = true ∧
      ∃ slot, d.slots[r.slot]? = some slot ∧ Shows d' f slot.request := by
  obtain ⟨r, hr, hsame, slot, hslot, slot', hslot', hreq, hres⟩ := answer_made ha
  refine ⟨r, hr, hsame, slot, hslot, ?_⟩
  obtain ⟨t, ht, hts, htf⟩ := h'.answered _ _ _ hslot' hres
  refine ⟨t, ht, ?_, htf⟩
  have := h'.params t ht
  rw [hts, hslot'] at this
  simpa [hreq] using this.symm

omit [Enum St] [DecidableEq K] in
/-- An event that a thing is in `f` shows a thing of its parameters now in `f`. -/
theorem Sound.shows_event {d' : Model K R St P} (h' : Sound f d') {e : Report R St P}
    (hst : e.state = f) (hpos : 0 < Events.count d'.inner.delivered e) : Shows d' f e.params :=
  h'.reported e hpos hst

theorem count_event {d d' : Model K R St P} {e : Report R St P}
    (he : (service lifecycle maxDeliveries).event d e = some d') :
    0 < Events.count d'.inner.delivered e := by
  simp only [service, Idempotent.server, Events.bounded] at he
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp he
  split at hs
  · split at hs
    · obtain rfl := Option.some.inj hs; simp
    · obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp hs; simp
  · simp at hs

end Sound

section Sound

variable {K : Type} [DecidableEq K] {f : St} {lifecycle : Lifecycle St} {maxDeliveries : Nat}
  {σ : Signature} {port : Rpc.Port σ (Idempotent.Keyed K P) (Answer R St) (Report R St P)}
  {d d' : Rpc.State (Model K R St P)}

/-- An input the model allows keeps `Sound` and every thing in `f`. -/
theorem Sound.allow (hf : lifecycle.Terminal f) (h : Sound f d.server) {x : σ.In}
    (hallow : (outside port lifecycle maxDeliveries).allow d x = some d') :
    Sound f d'.server ∧ Keeps f d.server.inner.inner d'.server.inner.inner := by
  cases hrep : port.reported x with
  | some e =>
    obtain ⟨s, hs, rfl⟩ := Rpc.allow_reported hrep hallow
    exact h.event hf hs
  | none =>
    rcases Rpc.allow_not_reported hrep hallow with hs | ⟨call, a, -, hs⟩
    · rw [hs]; exact ⟨h, fun t ht _ => ht⟩
    · exact h.answer hf hs

/-- An output keeps `Sound` and every thing in `f`. -/
theorem Sound.observe (h : Sound f d.server) (out : σ.Out) :
    Sound f ((outside port lifecycle maxDeliveries).observe d out).server ∧
      Keeps f d.server.inner.inner
        ((outside port lifecycle maxDeliveries).observe d out).server.inner.inner := by
  simp only [outside, Rpc.outside]
  split
  · exact h.receive _
  · exact ⟨h, fun t ht _ => ht⟩

/-- `Sound` holds after every run the model allows. -/
theorem sound_after (hf : lifecycle.Terminal f) {events : List (Event σ)}
    (h : (outside port lifecycle maxDeliveries).after events = some d) : Sound f d.server :=
  Rpc.server_invariant port _ (fun _ => True) (Sound f) sound_init
    (fun _ call h _ => (h.receive call).1) (fun _ _ _ _ h ha => (h.answer hf ha).1)
    (fun _ _ _ h he => (h.event hf he).1) (fun _ _ _ _ => trivial) h

/-- An answer the model allows, that the thing of call `call` is in `f`, shows the request of
the call's slot made a thing in `f`. -/
theorem Sound.shows_reply (hf : lifecycle.Terminal f) (h : Sound f d.server) {x : σ.In}
    {call : Nat} {id : R} (hx : port.replied x = some (call, .answer (.made id f)))
    (hallow : (outside port lifecycle maxDeliveries).allow d x = some d') :
    ∃ r, d.server.routes.find? (·.call == call) = some r ∧ r.same = true ∧
      ∃ slot, d.server.slots[r.slot]? = some slot ∧ Shows d'.server f slot.request :=
  (h.allow hf hallow).1.shows_answer (Rpc.allow_answer hx hallow)

/-- An event the model allows, that a thing is in `f`, shows a thing of its parameters in
`f`. -/
theorem Sound.shows_report (hf : lifecycle.Terminal f) (h : Sound f d.server) {x : σ.In}
    {e : Report R St P} (hx : port.reported x = some e) (hst : e.state = f)
    (hallow : (outside port lifecycle maxDeliveries).allow d x = some d') :
    Shows d'.server f e.params := by
  obtain ⟨s, hs, rfl⟩ := Rpc.allow_reported hx hallow
  exact (h.event hf hs).1.shows_event hst (count_event hs)

end Sound

section Routes

variable {K : Type} [DecidableEq K] {lifecycle : Lifecycle St} {maxDeliveries : Nat}
  {σ : Signature} {port : Rpc.Port σ (Idempotent.Keyed K P) (Answer R St) (Report R St P)}

theorem answer_requests {d d' : Model K R St P} {call : Nat} {a : Answer R St}
    (ha : (service lifecycle maxDeliveries).answer d call a = some d') :
    d'.routes = d.routes ∧ ∀ n : Nat, (d'.slots[n]?).map (·.request) = (d.slots[n]?).map (·.request) := by
  simp only [service, Idempotent.server] at ha
  split at ha
  · simp at ha
  · split at ha
    · obtain rfl := Option.some.inj ha; exact ⟨rfl, fun _ => rfl⟩
    · split at ha
      · simp at ha
      · split at ha
        · simp at ha
        · next slot hslot =>
          split at ha
          · split at ha
            · obtain rfl := Option.some.inj ha; exact ⟨rfl, fun _ => rfl⟩
            · simp at ha
          · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp ha
            exact ⟨rfl, fun _ => requests_set hslot⟩

/-- An input the model allows changes no route and no slot's request. -/
theorem allow_requests {d d' : Rpc.State (Model K R St P)} {x : σ.In}
    (hallow : (outside port lifecycle maxDeliveries).allow d x = some d') :
    d'.server.routes = d.server.routes ∧
      ∀ n : Nat, (d'.server.slots[n]?).map (·.request) = (d.server.slots[n]?).map (·.request) := by
  cases hrep : port.reported x with
  | some e =>
    obtain ⟨s, hs, rfl⟩ := Rpc.allow_reported hrep hallow
    simp only [service, Idempotent.server] at hs
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨rfl, fun _ => rfl⟩
  | none =>
    rcases Rpc.allow_not_reported hrep hallow with hs | ⟨call, a, -, hs⟩
    · rw [hs]; exact ⟨rfl, fun _ => rfl⟩
    · exact answer_requests hs

/-- An output keeps every slot, and a call adds its route in front, to a slot of the call's
request when the route says it is the same. -/
theorem observe_routes {d d' : Rpc.State (Model K R St P)} {out : σ.Out}
    (hd' : (outside port lifecycle maxDeliveries).observe d out = d') :
    (∀ (n : Nat) slot, d.server.slots[n]? = some slot → d'.server.slots[n]? = some slot) ∧
      (port.called out = none → d'.server.routes = d.server.routes) ∧
      ∀ call, port.called out = some call → ∃ rt, d'.server.routes = rt :: d.server.routes ∧
        rt.call = call.id ∧
        (rt.same = true → (d'.server.slots[rt.slot]?).map (·.request) = some call.request.request) := by
  subst hd'
  simp only [outside, Rpc.outside]
  split
  · next call hcall =>
    simp only [service, Idempotent.server]
    split
    · next n hn =>
      refine ⟨fun _ _ h => h, by simp [hcall], fun call' hcall' => ?_⟩
      obtain rfl := Option.some.inj (hcall.symm.trans hcall')
      exact ⟨_, rfl, rfl, fun h => by simpa using h⟩
    · refine ⟨fun n slot h => ?_, by simp [hcall], fun call' hcall' => ?_⟩
      · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h
      · obtain rfl := Option.some.inj (hcall.symm.trans hcall')
        exact ⟨_, rfl, rfl, fun _ => by simp⟩
  · next hcall =>
    exact ⟨fun _ _ h => h, fun _ => rfl, fun call h => by simp [hcall] at h⟩

end Routes

end Lanes.Effects
