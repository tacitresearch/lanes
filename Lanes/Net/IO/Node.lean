/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.IO.Server
public import Lanes.Net.IO.Peers

/-!
One process of a system spread over several, with an HTTP front: the two adapters put together.
The process runs `fronted (sys.shard hosts)` on one runtime. A request enters through the gate,
a parcel from another process enters beside it, and of what the shard puts out a response goes
back through the gate and a parcel goes to `Peers`.

Request ids are this process's own. A response must be put out by an actor this process hosts:
one put out elsewhere reaches that process's gate, which has other requests under the same ids.
-/

public section

namespace Lanes.Http

open Std Std.Async

variable {σ : Signature}

/-- An output of `sys` that the bridge does not read as a response comes to `onOutput`. -/
def serveShard (sys : System σ) [Hashable σ.Id] (hosts : σ.Id → Bool) (bridge : Bridge σ)
    (peers : Peers.Config σ) (config : ServerConfig := {}) (runtimeConfig : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ())
    (log : Option (Journal.Log (fronted (sys.shard hosts) bridge.shard config.gate)) := none) :
    Async (Server (fronted (sys.shard hosts) bridge.shard config.gate) × Peers σ) := do
  let ready : IO.Promise (Parcel σ → Async Unit) ← IO.Promise.new
  let peers ← Peers.start peers fun parcel => do
    if let some offer ← await ready.result? then offer parcel
  let server ← try
      serveFronted (sys.shard hosts) bridge.shard config runtimeConfig (log := log) fun
        | .inl out => onOutput out
        | .inr parcel => peers.send parcel
    catch e =>
      peers.stop
      throw e
  ready.resolve fun parcel => discard <| server.tryInput (.inr parcel)
  return (server, peers)

end Lanes.Http
