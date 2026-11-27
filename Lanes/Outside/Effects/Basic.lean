/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Outside.Idempotent
public import Lanes.Outside.Events
public import Lanes.Data.Enum

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

end Lanes.Effects
