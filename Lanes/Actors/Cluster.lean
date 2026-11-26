/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.Runtime
public import Lanes.Actors.Shard

/-!
Several shards of one system, each on a thread of its own, and the router between them. A shard
runs `System.shard`, the system as that shard sees it, on the ordinary runtime; an actor lives
on the shard its identity hashes to. The router carries each parcel a shard puts out to the
shard that hosts its receiver, on a lane that is never full.

Trusted here: that a parcel reaches the right shard, once, and that parcels from one shard to
another arrive in the order they were sent.
-/

public section

namespace Lanes

open Std Std.Async

variable {σ : Signature}

structure Cluster (sys : System σ) where
  private mk ::
  shards : Nat
  private inputs : Array (σ.In → Async Unit)
  private offers : Array (σ.In → Async Bool)
  private idles : Array (Async Unit)
  private stops : Array (Async Unit)
  private states : Array ((i : σ.Id) → Async (sys.State i))
  private parcels : IO.Ref Nat

namespace Cluster

variable {sys : System σ} [Hashable σ.Id]

/-- The shard an actor lives on. -/
def home (shards : Nat) (i : σ.Id) : Nat :=
  (hash i).toNat % shards

private def gone : IO.Error := IO.userError "lanes: no such shard"

/-- Boot `sys` on `shards` shards (at least one). Each output goes to `onOutput`, from the shard
that made it: outputs of different shards are not ordered among themselves. -/
def start (sys : System σ) [Hashable σ.Id] (shards : Nat) (config : Runtime.Config := {})
    (onOutput : σ.Out → Async Unit := fun _ => pure ()) : Async (Cluster sys) := do
  let shards := max 1 shards
  let routes : IO.Promise (Array (Parcel σ → BaseIO Bool)) ← IO.Promise.new
  let parcels ← IO.mkRef 0
  let mut cluster : Cluster sys :=
    { shards, inputs := #[], offers := #[], idles := #[], stops := #[], states := #[], parcels }
  let mut senders := #[]
  for k in [0:shards] do
    let rt ← Runtime.start (sys.shard fun i => home shards i == k)
      { config with clustered := true } fun
        | .inl out => onOutput out
        | .inr parcel => do
          parcels.modify (· + 1)
          if let some send := (← await routes)[home shards parcel.1]? then
            discard <| send parcel
    senders := senders.push fun parcel => rt.peer (.inr parcel)
    cluster := { cluster with
      inputs := cluster.inputs.push fun x => rt.input (.inl x)
      offers := cluster.offers.push fun x => rt.tryInput (.inl x)
      idles := cluster.idles.push rt.idle
      stops := cluster.stops.push rt.stop
      states := cluster.states.push fun i => rt.state i }
  routes.resolve senders
  return cluster

private def of {α : Type} (c : Cluster sys) (table : Array α) (i : σ.Id) : Async α := do
  let some entry := table[home c.shards i]? | throw gone
  return entry

/-- Hand over an input to the shard of the actor it is for, waiting while that shard's inbox is
full. -/
def input (c : Cluster sys) (x : σ.In) : Async Unit := do
  (← c.of c.inputs (sys.accept x).1) x

/-- Hand over an input if the shard it is for has room. -/
def tryInput (c : Cluster sys) (x : σ.In) : Async Bool := do
  (← c.of c.offers (sys.accept x).1) x

/-- Wait until every shard is idle and no parcel is on its way: rounds of waiting for each
shard, until a round in which none was sent. -/
def idle (c : Cluster sys) : Async Unit := do
  repeat
    let before ← c.parcels.get
    for wait in c.idles do wait
    if (← c.parcels.get) == before then break

/-- The current state of actor `i`. For tests. -/
def state (c : Cluster sys) (i : σ.Id) : Async (sys.State i) := do
  (← c.of c.states i) i

def stop (c : Cluster sys) : Async Unit := do
  for stop in c.stops do stop

end Cluster

end Lanes
