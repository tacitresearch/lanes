/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes
import Examples.Bank

/-!
Shards joined by TCP: the bank with each account on a shard of its own, each shard listening on
its own port, credits travelling between them as parcels. And the pure reading of a stream of
parcels, on the compiled code.
-/

namespace Tests.Peers

open Lanes Std Std.Async Examples.Bank

abbrev Bank3 := bank (Fin 3) 1000

abbrev σ := sig (Fin 3)

def idCodec : Codec σ.Id := Codec.fin

def msgCodec (i : σ.Id) : Codec (σ.Msg i) :=
  (actors (Codec.fin (n := 3)) 1000).msg i

def receive (bytes : ByteArray) : Option (List (Parcel σ) × Nat) :=
  Parcel.receive idCodec msgCodec bytes

def parcels : List (Parcel σ) :=
  [⟨0, .credit 5⟩, ⟨2, .transfer 7 1 300⟩, ⟨1, .query 9⟩, ⟨1, .credit 0⟩]

def tests : List (String × Bool) :=
  let stream := Parcel.send idCodec msgCodec parcels
  [ ("peers: a stream of parcels cut at any byte reads as the parcels sent before the cut",
      (List.range (stream.size + 1)).all fun n =>
        match receive (stream.extract 0 n) with
        | some (found, taken) =>
          taken ≤ n && found == parcels.take found.length
            && (n < stream.size || found.length == parcels.length)
        | none => false),
    ("peers: read in pieces of any size, a stream gives the parcels sent, in order",
      [1, 2, 7, 64].all fun piece => Id.run do
        let mut received := ByteArray.empty
        let mut found : List (Parcel σ) := []
        for start in List.range ((stream.size + piece - 1) / piece) do
          received := received ++ stream.extract (start * piece) ((start + 1) * piece)
          match receive received with
          | some (more, taken) =>
            found := found ++ more
            received := received.extract taken received.size
          | none => return false
        return found == parcels && received.isEmpty),
    ("peers: bytes that are not parcels end the reading",
      (receive (stream.set! (stream.size - 2) (stream[stream.size - 2]! ^^^ 1))).isNone) ]

structure Shard where
  input : Request (Fin 3) → Async Unit
  balance : Async Int
  stop : Async Unit

def startShard (ports : IO.Ref (Array UInt16)) (answered : IO.Ref Nat) (k : Nat) :
    Async Shard := do
  let config : Peers.Config σ := {
    listen := { port := (← ports.get)[k]?.getD 0 }
    home := fun i => return (← ports.get)[i.val]?.map fun port => { port }
    id := idCodec, msg := msgCodec }
  let (rt, peers) ← Peers.shard Bank3 (fun i => i.val == k) config {}
    (fun _ => answered.modify (· + 1))
  if (← ports.get).size ≤ k then ports.modify (·.push peers.port)
  return {
    input := fun x => rt.input (.inl x)
    balance := return (← rt.state (Fin.ofNat 3 k)).balance
    stop := do peers.stop; rt.stop }

def live : Async (List (String × Bool)) := do
  let ports ← IO.mkRef (#[] : Array UInt16)
  let answered ← IO.mkRef 0
  let mut shards : Array Shard := #[]
  for k in [0:3] do shards := shards.push (← startShard ports answered k)
  for round in [0:100] do
    for k in [0:3] do
      if let some shard := shards[k]? then
        shard.input (.transfer ⟨3 * round + k, Fin.ofNat 3 k, Fin.ofNat 3 (k + 1), 1 + k⟩)
  let mut settled := []
  for _ in [0:100] do
    settled ← shards.toList.mapM (·.balance)
    if settled.sum == 3000 then break
    Async.sleep 50
  let some (first, second) := (shards[0]?).bind fun a => (shards[1]?).map (a, ·)
    | return [("peers: the shards started", false)]
  second.stop
  let again ← startShard ports answered 1
  let mut reached := 0
  for round in [0:100] do
    first.input (.transfer ⟨1000 + round, 0, 1, 1⟩)
    Async.sleep 50
    reached ← again.balance
    if reached > 1000 then break
  for shard in shards.toList.eraseIdx 1 ++ [again] do shard.stop
  return [
    ("peers: three shards joined by TCP move every credit between them",
      settled == [1200, 900, 900] && (← answered.get) ≥ 300),
    ("peers: a shard started again on the same port is found by those that were sending",
      reached > 1000) ]

end Tests.Peers
