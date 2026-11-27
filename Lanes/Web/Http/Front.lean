/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Core.Join
public import Lanes.Outside.Basic
public import Lanes.Runtime.Shard
public import Lanes.Durable.Snapshot
public import Lanes.Web.Http.Gate

/-!
The gate as a system of its own, and a system with the gate joined in front of it.

`gateSystem` is one actor. Its inputs are the requests that arrive and the outputs of whatever
is behind it; its outputs are responses and the inputs it passes on. Its decisions are
`Gate.step`.

`fronted sys bridge` is `gateSystem` joined to `sys` with `System.join`: an input the gate
passes on is an input of `sys`, and an output of `sys` that the bridge reads as a response goes
to the gate. Every other output of `sys` is an output of `fronted sys`, and `sys` still takes
inputs that do not come through the gate. So a shard of a system spread over processes can sit
behind a gate: its parcels pass the gate by, both ways. `served sys bridge` is `fronted sys` seen
as `Http.serve` runs it: requests in, responses out, and nothing else in or out.

`Lanes.Web.Http.FrontSound` proves that the gate alone answers no more often than it handles an
arrival, and, by projection, that `fronted sys` and `served sys` answer no request more often than
it arrived. `Lanes.Semantics.Front` proves, by projection of fair runs, that both answer every
request their gate admits.
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

abbrev servedSig (σ : Signature) : Signature :=
  (frontedSig σ).withIO (ReqId × Request) (ReqId × Response)

/-- `sys` with the gate joined in front of it, as `Http.serve` runs it: what `sys` puts out that
is no response is not put out, as the gate drops an output it cannot read. -/
abbrev served (sys : System σ) (bridge : Bridge σ) (config : GateConfig := {}) :
    System (servedSig σ) :=
  (fronted sys bridge config).filterMapIO .inl Sum.getLeft?

/-! What the checker needs of a fronted system is what it needs of the system behind the gate.
As for a join, each is named and given in one line: `instance : (frontedSig σ).Inspect := .fronted`
and `instance : (fronted sys bridge).Inspect := .fronted`. -/

@[instance_reducible] def _root_.Lanes.Signature.Inspect.gate [σ.Inspect] :
    (gateSig σ).Inspect where
  reprMsg _ := inferInstanceAs (Repr (GateMsg σ))
  hashMsg _ := inferInstanceAs (Hashable (GateMsg σ))

@[instance_reducible] def _root_.Lanes.System.Inspect.gate {bridge : Bridge σ}
    {config : GateConfig} : (gateSystem bridge config).Inspect where
  beqState _ := inferInstanceAs (BEq (List ReqId))
  reprState _ := inferInstanceAs (Repr (List ReqId))
  hashState _ := inferInstanceAs (Hashable (List ReqId))

@[instance_reducible] def _root_.Lanes.Signature.Inspect.fronted [σ.Inspect] :
    (frontedSig σ).Inspect :=
  letI : (gateSig σ).Inspect := .gate
  letI : (joinSig (gateSig σ) σ).Inspect := .join
  .withIO

@[instance_reducible] def _root_.Lanes.System.Inspect.fronted {sys : System σ} [sys.Inspect]
    {bridge : Bridge σ} {config : GateConfig} : (fronted sys bridge config).Inspect :=
  letI : (gateSystem bridge config).Inspect := .gate
  letI : ((gateSystem bridge config).join sys (frontWiring bridge)).Inspect := .join
  .filterMapIO

@[instance_reducible] def _root_.Lanes.Signature.Inspect.served [σ.Inspect] :
    (servedSig σ).Inspect :=
  letI : (frontedSig σ).Inspect := .fronted
  .withIO

@[instance_reducible] def _root_.Lanes.System.Inspect.served {sys : System σ} [sys.Inspect]
    {bridge : Bridge σ} {config : GateConfig} : (served sys bridge config).Inspect :=
  letI : (fronted sys bridge config).Inspect := .fronted
  .filterMapIO

/-- A bridge for a shard: requests enter as inputs from outside, and a parcel is no response. -/
def Bridge.shard (bridge : Bridge σ) : Bridge (shardSig σ) where
  decode id request := (bridge.decode id request).map .inl
  encode
    | .inl out => bridge.encode out
    | .inr _ => none
  prepare := bridge.prepare

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

def servedActors {sys : System σ} (actors : Kernel.Image.Codecs sys) (out : Codec σ.Out)
    (bridge : Bridge σ) (config : GateConfig := {}) :
    Kernel.Image.Codecs (served sys bridge config) :=
  let fronted := frontedActors actors out bridge config
  { id := fronted.id, state := fronted.state, msg := fronted.msg }

/-- What the gate assumes of whoever sends it requests: an id is used once. Other inputs are
not its concern. -/
def frontedOutside (σ : Signature) : Outside (frontedSig σ) (List ReqId) where
  init := []
  allow used
    | .inl (id, _) => if id ∈ used then none else some (id :: used)
    | .inr _ => some used

/-- What the gate assumes of whoever sends `served sys` requests: an id is used once. The
server allocates ids, and is tested to stay within this. -/
def servedOutside (σ : Signature) : Outside (servedSig σ) (List ReqId) where
  init := []
  allow used x := if x.1 ∈ used then none else some (x.1 :: used)

end Lanes.Http
