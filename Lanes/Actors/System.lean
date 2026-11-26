/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Actor

/-!
# Systems of actors

A `Signature` names the actors of a system and gives each one its own message type. An actor
identity is therefore also a typed reference: `Effect.send to msg` only type-checks when
`msg : σ.Msg to`. Identities are plain data, so they can be stored, compared, hashed and sent.

Identities may form infinite families (`account (n : Nat)`, `session (id : SessionId)`). Every
identity names an actor that conceptually always exists and is started on demand, so there is no
spawn effect and no registry in the semantics.

## Main definitions

- `Signature`: actor identities, per-actor message types, external inputs and outputs.
- `Effect σ self`: what an actor in a system may ask the runtime to do.
- `Envelope σ`: a message in flight.
- `System σ`: an actor for every identity, plus the routing of external inputs.
- `Link`, `EnvModel σ`: the assumptions about links and crashes that a property is proved under.
-/

@[expose] public section

namespace Lanes

/--
The interface of a system: who its actors are, what each one accepts, and what crosses the
system boundary.

Identities, messages and outputs are data (rule 2.3), which is what the bundled decidable
equalities say. They are instance fields so that they never need to be passed around.
-/
structure Signature where
  /-- Actor identities. An identity is also the typed reference used to send to that actor. -/
  Id : Type
  /-- The messages each actor accepts: one type per actor. -/
  Msg : Id → Type
  /-- Inputs arriving from outside the system, such as client requests. -/
  In : Type := Empty
  /-- Outputs leaving the system, such as responses to clients. -/
  Out : Type := Empty
  /-- Identities are data. -/
  [decEqId : DecidableEq Id]
  /-- Messages are data. -/
  [decEqMsg : ∀ i, DecidableEq (Msg i)]
  /-- Inputs are data. -/
  [decEqIn : DecidableEq In]
  /-- Outputs are data. -/
  [decEqOut : DecidableEq Out]

attribute [instance] Signature.decEqId Signature.decEqMsg Signature.decEqIn Signature.decEqOut

/--
An effect returned by the actor `self` of a system with signature `σ`. Effects are values
(rule 2.4): the runtime performs them, and the semantics says what performing them means.
-/
inductive Effect (σ : Signature) (self : σ.Id) : Type where
  /-- Send `msg` to the actor `to`. -/
  | send (to : σ.Id) (msg : σ.Msg to)
  /-- Hand `out` to the outside world, for example a response to a client. -/
  | emit (out : σ.Out)
  /--
  Arm a timer that delivers `msg` back to this actor no earlier than `delay_ms` milliseconds from
  now. A timer is identified by its message: arming a pending timer again restarts it.
  -/
  | after (delay_ms : Nat) (msg : σ.Msg self)
  /-- Disarm the timer identified by `msg`, if it is pending. -/
  | cancel (msg : σ.Msg self)
  /--
  Stop this actor once the current step's effects are performed (rule 3.1). Its volatile state,
  timers and mailbox are lost; it starts again through `Actor.recover`.
  -/
  | stop

namespace Effect

variable {σ : Signature} {self : σ.Id}

/-- Whether this effect is `stop`. -/
def isStop : Effect σ self → Bool
  | .stop => true
  | _ => false

instance : DecidableEq (Effect σ self) := fun a b =>
  match a, b with
  | .send t₁ m₁, .send t₂ m₂ =>
    if h : t₁ = t₂ then
      if h' : h ▸ m₁ = m₂ then isTrue (by subst h; subst h'; rfl)
      else isFalse (by intro heq; cases heq; exact h' rfl)
    else isFalse (by intro heq; cases heq; exact h rfl)
  | .emit o₁, .emit o₂ =>
    if h : o₁ = o₂ then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .after d₁ m₁, .after d₂ m₂ =>
    if h : d₁ = d₂ ∧ m₁ = m₂ then isTrue (by rw [h.1, h.2])
    else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl⟩)
  | .cancel m₁, .cancel m₂ =>
    if h : m₁ = m₂ then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .stop, .stop => isTrue rfl
  | .send .., .emit _ | .send .., .after .. | .send .., .cancel _ | .send .., .stop
  | .emit _, .send .. | .emit _, .after .. | .emit _, .cancel _ | .emit _, .stop
  | .after .., .send .. | .after .., .emit _ | .after .., .cancel _ | .after .., .stop
  | .cancel _, .send .. | .cancel _, .emit _ | .cancel _, .after .. | .cancel _, .stop
  | .stop, .send .. | .stop, .emit _ | .stop, .after .. | .stop, .cancel _ =>
    isFalse (by intro heq; cases heq)

end Effect

/-- An actor of a system: its effects are the system's effects. -/
abbrev Signature.Actor (σ : Signature) (i : σ.Id) (S : Type) : Type :=
  Lanes.Actor S (σ.Msg i) (Effect σ i)

/-- A message in flight to the actor `dst`. -/
structure Envelope (σ : Signature) where
  /-- The sending actor, or `none` for a message that came from outside the system. -/
  src : Option σ.Id
  /-- The receiving actor. -/
  dst : σ.Id
  /-- The message. -/
  msg : σ.Msg dst

namespace Envelope

variable {σ : Signature}

instance : DecidableEq (Envelope σ) := fun a b =>
  match a, b with
  | ⟨s₁, d₁, m₁⟩, ⟨s₂, d₂, m₂⟩ =>
    if hs : s₁ = s₂ then
      if hd : d₁ = d₂ then
        if hm : hd ▸ m₁ = m₂ then isTrue (by subst hs; subst hd; subst hm; rfl)
        else isFalse (by intro heq; cases heq; exact hm rfl)
      else isFalse (by intro heq; cases heq; exact hd rfl)
    else isFalse (by intro heq; cases heq; exact hs rfl)

/-- Whether two envelopes travel on the same link, that is from the same sender to the same
receiver. -/
def sameLink (a b : Envelope σ) : Bool :=
  decide (a.src = b.src) && decide (a.dst = b.dst)

end Envelope

/--
A system: an actor for every identity of the signature.

Actors are deterministic. Whatever chooses (clients, the network, crashes) lives outside, in
the events of the semantics.
-/
structure System (σ : Signature) where
  /-- The private state type of each actor. -/
  State : σ.Id → Type
  /-- The actor behind each identity. -/
  actor : (i : σ.Id) → σ.Actor i (State i)
  /-- Where an external input goes: the receiving actor and the message it sees. Raw input has
  already been parsed by an adapter at this point (rule 2.2). -/
  accept : σ.In → (i : σ.Id) × σ.Msg i
  /-- Actors started when the system starts, in order. All others start on their first message. -/
  boot : List σ.Id := []

/-- What is assumed about one link, from one sender to one receiver. -/
structure Link where
  /-- Messages on this link are delivered in the order they were sent. -/
  ordered : Bool := true
  /-- Messages on this link may be lost. -/
  lossy : Bool := false
  /-- Messages on this link may be delivered more than once. -/
  duplicating : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace Link

/-- A link inside one process: ordered, no loss, no duplication. -/
def reliable : Link := {}

/-- A link between machines with retries: messages may be lost, reordered and duplicated, never
forged. -/
def network : Link := { ordered := false, lossy := true, duplicating := true }

/-- A link that only reorders: every message is delivered exactly once, in any order. -/
def unordered : Link := { ordered := false }

end Link

/--
The environment model: the assumptions about links and failures under which a property is
checked or proved. It is part of the specification, and every field is a named assumption
(rule 5.6).
-/
structure EnvModel (σ : Signature) where
  /-- The model of the link from each sender (`none` is the outside world) to each receiver. -/
  link : Option σ.Id → σ.Id → Link := fun _ _ => Link.reliable
  /-- Which actors may crash at any moment. -/
  mayCrash : σ.Id → Bool := fun _ => false
  /-- Which stopped actors start again on their own, without waiting for a message. -/
  restarts : σ.Id → Bool := fun _ => false

namespace EnvModel

variable {σ : Signature}

/-- One process, no faults: every link reliable, nothing crashes. -/
def reliable : EnvModel σ := {}

/-- Every link between two actors is a network link; links from the outside stay reliable. -/
def distributed : EnvModel σ where
  link src _ := if src.isSome then Link.network else Link.reliable

end EnvModel

end Lanes
