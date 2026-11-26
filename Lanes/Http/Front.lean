/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Join
public import Lanes.Actors.Shard
public import Lanes.Http.Gate

/-!
The gate as a system of its own, and a system with the gate joined in front of it.

`gateSystem` is one actor. Its inputs are the requests that arrive and the outputs of whatever
is behind it; its outputs are responses and the inputs it passes on. It makes the decisions of
`Lanes.Http.gate`, by the same function (`Gate.step`).

`fronted sys bridge` is `gateSystem` joined to `sys` with `System.join`: an input the gate
passes on is an input of `sys`, and an output of `sys` that the bridge reads as a response goes
to the gate. Every other output of `sys` is an output of `fronted sys`, and `sys` still takes
inputs that do not come through the gate. So a shard of a system spread over processes can sit
behind a gate: its parcels pass the gate by, both ways.

`Lanes.Http.FrontSound` proves that the gate alone answers no more often than it handles an
arrival, and, by projection, that `fronted sys` answers no request more often than it arrived.
-/

@[expose] public section

namespace Lanes.Http

variable {σ : Signature}

abbrev gateSig (σ : Signature) : Signature where
  Id := Unit
  Msg _ := GateMsg σ
  In := (ReqId × Request) ⊕ σ.Out
  Out := (ReqId × Response) ⊕ σ.In

def gateActor (bridge : Bridge σ) (config : GateConfig) : (gateSig σ).Actor () (List ReqId) where
  init := []
  step := Gate.step bridge config
    { respond := fun id response => .emit (.inl (id, response))
      forward := fun x => .emit (.inr x)
      arm := fun id => .after config.requestTimeout_ms (.expire id)
      disarm := fun id => .cancel (.expire id) }
  recover pending := (pending, pending.map fun id => .after config.requestTimeout_ms (.expire id))

theorem gateActor_bounded (bridge : Bridge σ) (config : GateConfig) :
    (gateActor bridge config).Invariant fun pending =>
      pending.length ≤ config.maxPending ∧ pending.Nodup :=
  Actor.Inductive.invariant
    ⟨by simp [gateActor], fun _ msg h => Gate.step_bounded bridge config _ msg h, fun _ h => h⟩

abbrev gateSystem (bridge : Bridge σ) (config : GateConfig := {}) : System (gateSig σ) where
  State _ := List ReqId
  actor _ := gateActor bridge config
  accept
    | .inl (id, request) => ⟨(), .arrive id request⟩
    | .inr out => ⟨(), .answer out⟩
  boot := [()]

/-- What the gate passes on goes to the system; of the system's outputs, those the bridge reads
as a response go to the gate. -/
def frontWiring (bridge : Bridge σ) : Wiring (gateSig σ) σ where
  toRight := Sum.getRight?
  toLeft out := if (bridge.encode out).isSome then some (.inr out) else none

abbrev frontedSig (σ : Signature) : Signature :=
  (joinSig (gateSig σ) σ).withIO ((ReqId × Request) ⊕ σ.In) ((ReqId × Response) ⊕ σ.Out)

/-- From outside, nothing can be handed to the gate as an output of the system. -/
def frontedInput : (ReqId × Request) ⊕ σ.In → (joinSig (gateSig σ) σ).In
  | .inl arrival => .inl (.inl arrival)
  | .inr x => .inr x

/-- The join's signature still names what the gate passes on as an output. None is ever put
out, the wiring turns each into a message, so hiding them loses nothing. -/
def frontedOutput : (joinSig (gateSig σ) σ).Out → Option ((ReqId × Response) ⊕ σ.Out)
  | .inl (.inl answer) => some (.inl answer)
  | .inl (.inr _) => none
  | .inr out => some (.inr out)

/-- `sys` with the gate joined in front of it. A request goes in as `.inl` and its response
comes out as `.inl`; what `sys` takes and puts out besides is `.inr`. -/
abbrev fronted (sys : System σ) (bridge : Bridge σ) (config : GateConfig := {}) :
    System (frontedSig σ) :=
  ((gateSystem bridge config).join sys (frontWiring bridge)).filterMapIO frontedInput frontedOutput

/-- A bridge for a shard: requests enter as inputs from outside, and a parcel is no response. -/
def Bridge.shard (bridge : Bridge σ) : Bridge (shardSig σ) where
  decode id request := (bridge.decode id request).map .inl
  encode
    | .inl out => bridge.encode out
    | .inr _ => none

/-- How the actors of a fronted system are written to a snapshot, given how the system's own
are, and its outputs, which may be on their way to the gate. -/
def frontedActors {sys : System σ} (actors : Kernel.Image.Codecs sys) (out : Codec σ.Out)
    (bridge : Bridge σ) (config : GateConfig := {}) :
    Kernel.Image.Codecs (fronted sys bridge config) where
  id := Codec.sum Codec.unit actors.id
  state
    | .inl _ => Codec.list Codec.nat
    | .inr i => actors.state i
  msg
    | .inl _ => Codec.sum% GateMsg { arrive (id := Codec.nat) (request := Request.codec),
        answer (out := out), expire (id := Codec.nat) }
    | .inr i => actors.msg i

/-- What the gate assumes of whoever sends it requests: an id is used once. Other inputs are
not its concern. -/
def frontedOutside (σ : Signature) : Outside (frontedSig σ) (List ReqId) where
  init := []
  allow used
    | .inl (id, _) => if id ∈ used then none else some (id :: used)
    | .inr _ => some used

end Lanes.Http
