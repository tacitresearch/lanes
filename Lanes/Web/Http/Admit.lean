/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.Front

/-!
The gate off the shard's hot path (`docs/decisions/D96-runtime-contract.md`,
`docs/decisions/D106-gate-before-shard.md`). The gate's decisions are `Gate.step`, and they need
not be made by an actor: the server makes them where a request arrives, with the waiting list in
its own memory, and hands the shard only what the gate admitted. The shard then runs
`admitted sys bridge`: `sys` itself, with no actor that every request goes through.

`Gate.Act` is what the gate does, as data, so the server and `Loopback` perform the same
decisions. `Gate.admit` and `Gate.receive` are `Gate.step` on an arrival and on an answer with
`decode` and `encode` taken out, so that the server runs those outside its lock.

A request the gate admitted reaches the shard as `(id, request)`, the entry the journal has always
held, and the shard decodes it again: the journal has no codec for `σ.In` yet
(`docs/decisions/D97-data-format.md`, 3.4). A request that no longer decodes, at a replay
through a newer `decode`, goes to `.inl ()`, an actor that does nothing.

`Lanes.Web.Http.AdmitSound` proves that a run of the server's front with the shard is a run of
`served sys`, with the same answers, and that the gate's theorems hold of the front.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

/-- What the gate does, as data: answer a request, pass an input on, arm or disarm a request's
deadline. -/
inductive Gate.Act (σ : Signature) where
  | respond (id : ReqId) (response : Response)
  | forward (x : σ.In)
  | arm (id : ReqId)
  | disarm (id : ReqId)

def Gate.acts : Gate.Effects σ (Gate.Act σ) := ⟨.respond, .forward, .arm, .disarm⟩

/-- The gate's decision on the arrival of `id`, given what `decode` made of the request. -/
def Gate.admit {E : Type} (config : GateConfig) (does : Gate.Effects σ E) (pending : List ReqId)
    (id : ReqId) (decoded : Except Response σ.In) : List ReqId × List E :=
  if id ∈ pending then (pending, [])
  else if pending.length ≥ config.maxPending then (pending, [does.respond id busy])
  else
    match decoded with
    | .error response => (pending, [does.respond id response])
    | .ok x => (id :: pending, [does.forward x, does.arm id])

/-- The gate's decision on an answer the system gave, once `encode` has read it as a response. -/
def Gate.receive {E : Type} (does : Gate.Effects σ E) (pending : List ReqId)
    (answer : ReqId × Response) : List ReqId × List E :=
  if answer.1 ∈ pending then (pending.erase answer.1, [does.disarm answer.1, does.respond answer.1 answer.2])
  else (pending, [])

theorem Gate.step_arrive_eq {E : Type} (bridge : Bridge σ) (config : GateConfig)
    (does : Gate.Effects σ E) (pending : List ReqId) (id : ReqId) (request : Request) :
    Gate.step bridge config does pending (.arrive id request)
      = Gate.admit config does pending id (bridge.decode id request) := rfl

theorem Gate.step_answer_eq {E : Type} (bridge : Bridge σ) (config : GateConfig)
    (does : Gate.Effects σ E) (pending : List ReqId) (out : σ.Out) :
    Gate.step bridge config does pending (.answer out)
      = match bridge.encode out with
        | some answer => Gate.receive does pending answer
        | none => (pending, []) := by
  simp only [Gate.step, Gate.receive]
  split <;> simp_all

/-- A request the gate does not pass on, as busy or as `decode` answers it, leaves the waiting
list as it was. -/
theorem Gate.admit_refused (config : GateConfig) (pending : List ReqId) (id : ReqId)
    (decoded : Except Response σ.In)
    (h : ∀ x, Gate.Act.forward x ∉ (Gate.admit config Gate.acts pending id decoded).2) :
    (Gate.admit config Gate.acts pending id decoded).1 = pending := by
  cases decoded with
  | error r => simp only [Gate.admit]; split <;> (try split) <;> rfl
  | ok x =>
    simp only [Gate.admit] at h ⊢
    split
    · rfl
    · split
      · rfl
      · exact absurd (by simp_all [Gate.acts]) (h x)

/-! ## The shard's system -/

/-- One actor, `()`, that takes a message and does nothing. -/
abbrev sinkSig : Signature where
  Id := Unit
  Msg _ := Unit
  In := Unit
  Out := Empty

def sink : System sinkSig where
  State _ := Unit
  actor _ :=
    { init := ()
      step s _ := (s, [])
      recover s := (s, [])
      fresh _ := true
      fresh_recover _ _ := rfl }
  accept _ := ⟨(), ()⟩

/-- Where an input of the shard goes: a request to the actor `decode` names, or to the sink if
it no longer decodes; any other input to `sys` as it is. -/
def admitInput (bridge : Bridge σ) : (ReqId × Request) ⊕ σ.In → Unit ⊕ σ.In
  | .inl (id, request) =>
    match bridge.decode id request with
    | .ok x => .inr x
    | .error _ => .inl ()
  | .inr x => .inr x

def admitOutput : Empty ⊕ σ.Out → Option σ.Out
  | .inl e => e.elim
  | .inr out => some out

abbrev admittedFrontedSig (σ : Signature) : Signature :=
  (joinSig sinkSig σ).withIO ((ReqId × Request) ⊕ σ.In) σ.Out

/-- What the shard runs behind the server's front, for `Http.serveFronted`: the requests the gate
admitted, and inputs that are no request, go to `sys`; every output of `sys` comes out, for the
front to read. -/
abbrev admittedFronted (sys : System σ) (bridge : Bridge σ) : System (admittedFrontedSig σ) :=
  (sink.join sys).filterMapIO (admitInput bridge) admitOutput

abbrev admittedSig (σ : Signature) : Signature :=
  (admittedFrontedSig σ).withIO (ReqId × Request) σ.Out

/-- What the shard runs behind the server's front, for `Http.serve`: only requests come in. -/
abbrev admitted (sys : System σ) (bridge : Bridge σ) : System (admittedSig σ) :=
  (admittedFronted sys bridge).filterMapIO .inl some

/-- How the actors of the shard are written to a snapshot, given how the system's own are. -/
def admittedFrontedActors {sys : System σ} (actors : Kernel.Image.Codecs sys) (bridge : Bridge σ) :
    Kernel.Image.Codecs (admittedFronted sys bridge) where
  id := Codec.sum Codec.unit actors.id
  state
    | .inl _ => Codec.unit
    | .inr i => actors.state i
  msg
    | .inl _ => Codec.unit
    | .inr i => actors.msg i

def admittedActors {sys : System σ} (actors : Kernel.Image.Codecs sys) (bridge : Bridge σ) :
    Kernel.Image.Codecs (admitted sys bridge) :=
  let fronted := admittedFrontedActors actors bridge
  { id := fronted.id, state := fronted.state, msg := fronted.msg }

end Lanes.Http
