/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Actors.System

/-!
# A system as one shard sees it

`System.shard sys hosts` is `sys` on a shard that hosts only some of its actors. The actors it
hosts are themselves, except that a message to an actor hosted elsewhere leaves the shard as an
output, a `Parcel`, and a parcel arriving from elsewhere is an input. An actor the shard does
not host only forwards what reaches it, so a misrouted message is passed on, never handled in
the wrong place.

It is an ordinary `System`, so a shard runs on the ordinary kernel and runtime, and keeps the
ordinary journal. Several shards and a router between them are `Lanes.Cluster`.
-/

@[expose] public section

namespace Lanes

variable {σ : Signature}

/-- A message with its receiver, as it travels between shards. -/
abbrev Parcel (σ : Signature) : Type := (i : σ.Id) × σ.Msg i

abbrev shardSig (σ : Signature) : Signature where
  Id := σ.Id
  Msg := σ.Msg
  In := σ.In ⊕ Parcel σ
  Out := σ.Out ⊕ Parcel σ

def shardEffect (hosts : σ.Id → Bool) {i : σ.Id} : Effect σ i → Effect (shardSig σ) i
  | .send to msg => if hosts to then .send to msg else .emit (.inr ⟨to, msg⟩)
  | .emit out => .emit (.inl out)
  | .after delay_ms msg => .after delay_ms msg
  | .cancel msg => .cancel msg
  | .stop => .stop

abbrev System.shard (sys : System σ) (hosts : σ.Id → Bool) : System (shardSig σ) where
  State := sys.State
  actor i :=
    if hosts i then (sys.actor i).mapEff fun eff => [shardEffect hosts eff]
    else
      { init := (sys.actor i).init
        step := fun s msg => (s, [.emit (.inr ⟨i, msg⟩)])
        recover := fun s => (s, []) }
  accept
    | .inl x => sys.accept x
    | .inr parcel => parcel
  boot := sys.boot.filter hosts

end Lanes
